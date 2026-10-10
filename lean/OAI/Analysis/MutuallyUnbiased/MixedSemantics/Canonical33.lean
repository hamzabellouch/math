import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4224 raw4224Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw4224 raw4224Labels = mixedMoment B raw4224step0 raw4224step0Labels := by
      have ha : raw4224step0 = (fun i j => raw4224 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4224step0 raw4224; decide +kernel
      have hl : raw4224step0Labels = raw4224Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4224 raw4224Labels permutation176 permutation2
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw4225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4225step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4225 raw4225Labels = mixedMoment B node1378 node1378Labels := by
  calc
    mixedMoment B raw4225 raw4225Labels = mixedMoment B raw4225step0 raw4225step0Labels := by
      have ha : raw4225step0 = (fun i j => raw4225 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4225step0 raw4225; decide +kernel
      have hl : raw4225step0Labels = raw4225Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4225 raw4225Labels permutation662 permutation2
    mixedMoment B raw4225step0 raw4225step0Labels = mixedMoment B raw4225step1 raw4225step1Labels := by
      have ha : raw4225step1 = -raw4225step0 := by apply Matrix.ext; change ∀ i j, raw4225step1 i j = -(raw4225step0 i j); unfold raw4225step1 raw4225step0; decide +kernel
      have hl : raw4225step1Labels = raw4225step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1378 node1378Labels := by rfl

def raw4226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw4226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4226 raw4226Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw4226 raw4226Labels = mixedMoment B raw4226step0 raw4226step0Labels := by
      have hz : ∀ j, raw4226 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4226step0 = (fun i j => raw4226 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4226step0 raw4226; decide +kernel
      have hl : raw4226step0Labels = raw4226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4226 raw4226Labels permutation346 hz
    mixedMoment B raw4226step0 raw4226step0Labels = mixedMoment B raw4226step1 raw4226step1Labels := by
      have ha : raw4226step1 = (fun i j => raw4226step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4226step1 raw4226step0; decide +kernel
      have hl : raw4226step1Labels = raw4226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4226step0 raw4226step0Labels permutation44 permutation2
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw4227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4227 raw4227Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw4227 raw4227Labels = mixedMoment B raw4227step0 raw4227step0Labels := by
      have hz : ∀ j, raw4227 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4227step0 = (fun i j => raw4227 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4227step0 raw4227; decide +kernel
      have hl : raw4227step0Labels = raw4227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4227 raw4227Labels permutation346 hz
    mixedMoment B raw4227step0 raw4227step0Labels = mixedMoment B raw4227step1 raw4227step1Labels := by
      have ha : raw4227step1 = (fun i j => raw4227step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4227step1 raw4227step0; decide +kernel
      have hl : raw4227step1Labels = raw4227step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4227step0 raw4227step0Labels permutation34 permutation2
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw4228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw4228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4228 raw4228Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw4228 raw4228Labels = mixedMoment B raw4228step0 raw4228step0Labels := by
      have hz : ∀ j, raw4228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4228step0 = (fun i j => raw4228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4228step0 raw4228; decide +kernel
      have hl : raw4228step0Labels = raw4228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4228 raw4228Labels permutation346 hz
    mixedMoment B raw4228step0 raw4228step0Labels = mixedMoment B raw4228step1 raw4228step1Labels := by
      have ha : raw4228step1 = (fun i j => raw4228step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4228step1 raw4228step0; decide +kernel
      have hl : raw4228step1Labels = raw4228step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4228step0 raw4228step0Labels permutation38 permutation2
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw4229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4229step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4229 raw4229Labels = mixedMoment B node1394 node1394Labels := by
  calc
    mixedMoment B raw4229 raw4229Labels = mixedMoment B raw4229step0 raw4229step0Labels := by
      have hz : ∀ j, raw4229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4229step0 = (fun i j => raw4229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4229step0 raw4229; decide +kernel
      have hl : raw4229step0Labels = raw4229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4229 raw4229Labels permutation346 hz
    mixedMoment B raw4229step0 raw4229step0Labels = mixedMoment B raw4229step1 raw4229step1Labels := by
      have ha : raw4229step1 = (fun i j => raw4229step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4229step1 raw4229step0; decide +kernel
      have hl : raw4229step1Labels = raw4229step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4229step0 raw4229step0Labels permutation149 permutation2
    mixedMoment B raw4229step1 raw4229step1Labels = mixedMoment B raw4229step2 raw4229step2Labels := by
      have ha : raw4229step2 = -raw4229step1 := by apply Matrix.ext; change ∀ i j, raw4229step2 i j = -(raw4229step1 i j); unfold raw4229step2 raw4229step1; decide +kernel
      have hl : raw4229step2Labels = raw4229step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1394 node1394Labels := by rfl

def raw4230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw4230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw4230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4230step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4230 raw4230Labels = mixedMoment B node1394 node1394Labels := by
  calc
    mixedMoment B raw4230 raw4230Labels = mixedMoment B raw4230step0 raw4230step0Labels := by
      have hz : ∀ j, raw4230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4230step0 = (fun i j => raw4230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4230step0 raw4230; decide +kernel
      have hl : raw4230step0Labels = raw4230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4230 raw4230Labels permutation346 hz
    mixedMoment B raw4230step0 raw4230step0Labels = mixedMoment B raw4230step1 raw4230step1Labels := by
      have ha : raw4230step1 = (fun i j => raw4230step0 (permutation143 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4230step1 raw4230step0; decide +kernel
      have hl : raw4230step1Labels = raw4230step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4230step0 raw4230step0Labels permutation143 permutation2
    mixedMoment B raw4230step1 raw4230step1Labels = mixedMoment B raw4230step2 raw4230step2Labels := by
      have ha : raw4230step2 = -raw4230step1 := by apply Matrix.ext; change ∀ i j, raw4230step2 i j = -(raw4230step1 i j); unfold raw4230step2 raw4230step1; decide +kernel
      have hl : raw4230step2Labels = raw4230step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1394 node1394Labels := by rfl

def raw4231 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4231step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4231step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4231step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4231step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4231 raw4231Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw4231 raw4231Labels = mixedMoment B raw4231step0 raw4231step0Labels := by
      have hz : ∀ j, raw4231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4231step0 = (fun i j => raw4231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4231step0 raw4231; decide +kernel
      have hl : raw4231step0Labels = raw4231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4231 raw4231Labels permutation346 hz
    mixedMoment B raw4231step0 raw4231step0Labels = mixedMoment B raw4231step1 raw4231step1Labels := by
      have ha : raw4231step1 = (fun i j => raw4231step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4231step1 raw4231step0; decide +kernel
      have hl : raw4231step1Labels = raw4231step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4231step0 raw4231step0Labels permutation137 permutation7
    mixedMoment B raw4231step1 raw4231step1Labels = mixedMoment B raw4231step2 raw4231step2Labels := by
      have ha : raw4231step2 = -raw4231step1 := by apply Matrix.ext; change ∀ i j, raw4231step2 i j = -(raw4231step1 i j); unfold raw4231step2 raw4231step1; decide +kernel
      have hl : raw4231step2Labels = raw4231step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4231step2 raw4231step2Labels = mixedMoment B raw4231step3 raw4231step3Labels := by
      have ha : raw4231step3 = raw4231step2 := by apply Matrix.ext; unfold raw4231step3 raw4231step2; decide +kernel
      have hl : raw4231step2Labels = labelEmbedding10 ∘ raw4231step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4231step2 raw4231step2Labels raw4231step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw4232 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4232step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4232step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4232 raw4232Labels = mixedMoment B node5239 node5239Labels := by
  calc
    mixedMoment B raw4232 raw4232Labels = mixedMoment B raw4232step0 raw4232step0Labels := by
      have ha : raw4232step0 = (fun i j => raw4232 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4232step0 raw4232; decide +kernel
      have hl : raw4232step0Labels = raw4232Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4232 raw4232Labels permutation212 permutation7
    mixedMoment B raw4232step0 raw4232step0Labels = mixedMoment B raw4232step1 raw4232step1Labels := by
      have ha : raw4232step1 = raw4232step0 := by apply Matrix.ext; unfold raw4232step1 raw4232step0; decide +kernel
      have hl : raw4232step0Labels = labelEmbedding10 ∘ raw4232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4232step0 raw4232step0Labels raw4232step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5239 node5239Labels := by rfl

def raw4233 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4233step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4233step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4233step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4233step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4233 raw4233Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4233 raw4233Labels = mixedMoment B raw4233step0 raw4233step0Labels := by
      have hz : ∀ j, raw4233 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4233step0 = (fun i j => raw4233 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4233step0 raw4233; decide +kernel
      have hl : raw4233step0Labels = raw4233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4233 raw4233Labels permutation520 hz
    mixedMoment B raw4233step0 raw4233step0Labels = mixedMoment B raw4233step1 raw4233step1Labels := by
      have hz : ∀ j, raw4233step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4233step1 = (fun i j => raw4233step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4233step1 raw4233step0; decide +kernel
      have hl : raw4233step1Labels = raw4233step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4233step0 raw4233step0Labels permutation80 hz
    mixedMoment B raw4233step1 raw4233step1Labels = mixedMoment B raw4233step2 raw4233step2Labels := by
      have ha : raw4233step2 = (fun i j => raw4233step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4233step2 raw4233step1; decide +kernel
      have hl : raw4233step2Labels = raw4233step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4233step1 raw4233step1Labels permutation10 permutation7
    mixedMoment B raw4233step2 raw4233step2Labels = mixedMoment B raw4233step3 raw4233step3Labels := by
      have ha : raw4233step3 = raw4233step2 := by apply Matrix.ext; unfold raw4233step3 raw4233step2; decide +kernel
      have hl : raw4233step2Labels = labelEmbedding10 ∘ raw4233step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4233step2 raw4233step2Labels raw4233step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw4234 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4234 raw4234Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw4234 raw4234Labels = mixedMoment B raw4234step0 raw4234step0Labels := by
      have hz : ∀ j, raw4234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4234step0 = (fun i j => raw4234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4234step0 raw4234; decide +kernel
      have hl : raw4234step0Labels = raw4234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4234 raw4234Labels permutation346 hz
    mixedMoment B raw4234step0 raw4234step0Labels = mixedMoment B raw4234step1 raw4234step1Labels := by
      have ha : raw4234step1 = (fun i j => raw4234step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4234step1 raw4234step0; decide +kernel
      have hl : raw4234step1Labels = raw4234step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4234step0 raw4234step0Labels permutation137 permutation2
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw4235 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4235step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4235step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4235 raw4235Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4235 raw4235Labels = mixedMoment B raw4235step0 raw4235step0Labels := by
      have hz : ∀ j, raw4235 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4235step0 = (fun i j => raw4235 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4235step0 raw4235; decide +kernel
      have hl : raw4235step0Labels = raw4235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4235 raw4235Labels permutation265 hz
    mixedMoment B raw4235step0 raw4235step0Labels = mixedMoment B raw4235step1 raw4235step1Labels := by
      have ha : raw4235step1 = (fun i j => raw4235step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4235step1 raw4235step0; decide +kernel
      have hl : raw4235step1Labels = raw4235step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4235step0 raw4235step0Labels permutation32 permutation6
    mixedMoment B raw4235step1 raw4235step1Labels = mixedMoment B raw4235step2 raw4235step2Labels := by
      have ha : raw4235step2 = raw4235step1 := by apply Matrix.ext; unfold raw4235step2 raw4235step1; decide +kernel
      have hl : raw4235step1Labels = labelEmbedding9 ∘ raw4235step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4235step1 raw4235step1Labels raw4235step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw4236 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4236step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4236step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4236step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4236step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4236step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4236step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4236 raw4236Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw4236 raw4236Labels = mixedMoment B raw4236step0 raw4236step0Labels := by
      have hz : ∀ j, raw4236 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4236step0 = (fun i j => raw4236 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4236step0 raw4236; decide +kernel
      have hl : raw4236step0Labels = raw4236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4236 raw4236Labels permutation520 hz
    mixedMoment B raw4236step0 raw4236step0Labels = mixedMoment B raw4236step1 raw4236step1Labels := by
      have hz : ∀ j, raw4236step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4236step1 = (fun i j => raw4236step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4236step1 raw4236step0; decide +kernel
      have hl : raw4236step1Labels = raw4236step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4236step0 raw4236step0Labels permutation80 hz
    mixedMoment B raw4236step1 raw4236step1Labels = mixedMoment B raw4236step2 raw4236step2Labels := by
      have hz : ∀ j, raw4236step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4236step2 = (fun i j => raw4236step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4236step2 raw4236step1; decide +kernel
      have hl : raw4236step2Labels = raw4236step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4236step1 raw4236step1Labels permutation14 hz
    mixedMoment B raw4236step2 raw4236step2Labels = mixedMoment B raw4236step3 raw4236step3Labels := by
      have ha : raw4236step3 = (fun i j => raw4236step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4236step3 raw4236step2; decide +kernel
      have hl : raw4236step3Labels = raw4236step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4236step2 raw4236step2Labels permutation2 permutation6
    mixedMoment B raw4236step3 raw4236step3Labels = mixedMoment B raw4236step4 raw4236step4Labels := by
      have ha : raw4236step4 = raw4236step3 := by apply Matrix.ext; unfold raw4236step4 raw4236step3; decide +kernel
      have hl : raw4236step3Labels = labelEmbedding9 ∘ raw4236step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4236step3 raw4236step3Labels raw4236step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw4237 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4237step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4237 raw4237Labels = mixedMoment B node5218 node5218Labels := by
  calc
    mixedMoment B raw4237 raw4237Labels = mixedMoment B raw4237step0 raw4237step0Labels := by
      have ha : raw4237step0 = (fun i j => raw4237 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4237step0 raw4237; decide +kernel
      have hl : raw4237step0Labels = raw4237Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4237 raw4237Labels permutation152 permutation6
    mixedMoment B raw4237step0 raw4237step0Labels = mixedMoment B raw4237step1 raw4237step1Labels := by
      have ha : raw4237step1 = raw4237step0 := by apply Matrix.ext; unfold raw4237step1 raw4237step0; decide +kernel
      have hl : raw4237step0Labels = labelEmbedding9 ∘ raw4237step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4237step0 raw4237step0Labels raw4237step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5218 node5218Labels := by rfl

def raw4238 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4238step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4238step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4238step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4238 raw4238Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4238 raw4238Labels = mixedMoment B raw4238step0 raw4238step0Labels := by
      have hz : ∀ j, raw4238 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4238step0 = (fun i j => raw4238 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4238step0 raw4238; decide +kernel
      have hl : raw4238step0Labels = raw4238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4238 raw4238Labels permutation520 hz
    mixedMoment B raw4238step0 raw4238step0Labels = mixedMoment B raw4238step1 raw4238step1Labels := by
      have ha : raw4238step1 = (fun i j => raw4238step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4238step1 raw4238step0; decide +kernel
      have hl : raw4238step1Labels = raw4238step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4238step0 raw4238step0Labels permutation32 permutation6
    mixedMoment B raw4238step1 raw4238step1Labels = mixedMoment B raw4238step2 raw4238step2Labels := by
      have ha : raw4238step2 = raw4238step1 := by apply Matrix.ext; unfold raw4238step2 raw4238step1; decide +kernel
      have hl : raw4238step1Labels = labelEmbedding9 ∘ raw4238step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4238step1 raw4238step1Labels raw4238step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw4239 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw4239step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4239step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4239step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4239step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4239step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4239 raw4239Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw4239 raw4239Labels = mixedMoment B raw4239step0 raw4239step0Labels := by
      have hz : ∀ j, raw4239 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4239step0 = (fun i j => raw4239 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4239step0 raw4239; decide +kernel
      have hl : raw4239step0Labels = raw4239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4239 raw4239Labels permutation346 hz
    mixedMoment B raw4239step0 raw4239step0Labels = mixedMoment B raw4239step1 raw4239step1Labels := by
      have ha : raw4239step1 = (fun i j => raw4239step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4239step1 raw4239step0; decide +kernel
      have hl : raw4239step1Labels = raw4239step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4239step0 raw4239step0Labels permutation35 permutation4
    mixedMoment B raw4239step1 raw4239step1Labels = mixedMoment B raw4239step2 raw4239step2Labels := by
      have ha : raw4239step2 = -raw4239step1 := by apply Matrix.ext; change ∀ i j, raw4239step2 i j = -(raw4239step1 i j); unfold raw4239step2 raw4239step1; decide +kernel
      have hl : raw4239step2Labels = raw4239step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4239step2 raw4239step2Labels = mixedMoment B raw4239step3 raw4239step3Labels := by
      have ha : raw4239step3 = raw4239step2 := by apply Matrix.ext; unfold raw4239step3 raw4239step2; decide +kernel
      have hl : raw4239step2Labels = labelEmbedding7 ∘ raw4239step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4239step2 raw4239step2Labels raw4239step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw4240 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4240step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4240step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4240 raw4240Labels = mixedMoment B node5225 node5225Labels := by
  calc
    mixedMoment B raw4240 raw4240Labels = mixedMoment B raw4240step0 raw4240step0Labels := by
      have hz : ∀ j, raw4240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4240step0 = (fun i j => raw4240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4240step0 raw4240; decide +kernel
      have hl : raw4240step0Labels = raw4240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4240 raw4240Labels permutation346 hz
    mixedMoment B raw4240step0 raw4240step0Labels = mixedMoment B raw4240step1 raw4240step1Labels := by
      have ha : raw4240step1 = (fun i j => raw4240step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4240step1 raw4240step0; decide +kernel
      have hl : raw4240step1Labels = raw4240step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4240step0 raw4240step0Labels permutation34 permutation6
    mixedMoment B raw4240step1 raw4240step1Labels = mixedMoment B raw4240step2 raw4240step2Labels := by
      have ha : raw4240step2 = raw4240step1 := by apply Matrix.ext; unfold raw4240step2 raw4240step1; decide +kernel
      have hl : raw4240step1Labels = labelEmbedding9 ∘ raw4240step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4240step1 raw4240step1Labels raw4240step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5225 node5225Labels := by rfl

def raw4241 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4241step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4241 raw4241Labels = mixedMoment B node5240 node5240Labels := by
  calc
    mixedMoment B raw4241 raw4241Labels = mixedMoment B raw4241step0 raw4241step0Labels := by
      have ha : raw4241step0 = (fun i j => raw4241 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4241step0 raw4241; decide +kernel
      have hl : raw4241step0Labels = raw4241Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4241 raw4241Labels permutation154 permutation6
    mixedMoment B raw4241step0 raw4241step0Labels = mixedMoment B raw4241step1 raw4241step1Labels := by
      have ha : raw4241step1 = raw4241step0 := by apply Matrix.ext; unfold raw4241step1 raw4241step0; decide +kernel
      have hl : raw4241step0Labels = labelEmbedding9 ∘ raw4241step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4241step0 raw4241step0Labels raw4241step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5240 node5240Labels := by rfl

def raw4242 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4242step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4242step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4242step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4242 raw4242Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw4242 raw4242Labels = mixedMoment B raw4242step0 raw4242step0Labels := by
      have hz : ∀ j, raw4242 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4242step0 = (fun i j => raw4242 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4242step0 raw4242; decide +kernel
      have hl : raw4242step0Labels = raw4242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4242 raw4242Labels permutation520 hz
    mixedMoment B raw4242step0 raw4242step0Labels = mixedMoment B raw4242step1 raw4242step1Labels := by
      have hz : ∀ j, raw4242step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4242step1 = (fun i j => raw4242step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4242step1 raw4242step0; decide +kernel
      have hl : raw4242step1Labels = raw4242step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4242step0 raw4242step0Labels permutation80 hz
    mixedMoment B raw4242step1 raw4242step1Labels = mixedMoment B raw4242step2 raw4242step2Labels := by
      have ha : raw4242step2 = (fun i j => raw4242step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4242step2 raw4242step1; decide +kernel
      have hl : raw4242step2Labels = raw4242step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4242step1 raw4242step1Labels permutation8 permutation6
    mixedMoment B raw4242step2 raw4242step2Labels = mixedMoment B raw4242step3 raw4242step3Labels := by
      have ha : raw4242step3 = raw4242step2 := by apply Matrix.ext; unfold raw4242step3 raw4242step2; decide +kernel
      have hl : raw4242step2Labels = labelEmbedding9 ∘ raw4242step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4242step2 raw4242step2Labels raw4242step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw4243 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4243 raw4243Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw4243 raw4243Labels = mixedMoment B raw4243step0 raw4243step0Labels := by
      have hz : ∀ j, raw4243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4243step0 = (fun i j => raw4243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4243step0 raw4243; decide +kernel
      have hl : raw4243step0Labels = raw4243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4243 raw4243Labels permutation346 hz
    mixedMoment B raw4243step0 raw4243step0Labels = mixedMoment B raw4243step1 raw4243step1Labels := by
      have ha : raw4243step1 = (fun i j => raw4243step0 (permutation138 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4243step1 raw4243step0; decide +kernel
      have hl : raw4243step1Labels = raw4243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4243step0 raw4243step0Labels permutation138 permutation2
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw4244 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4244step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4244step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4244step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4244step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4244 raw4244Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw4244 raw4244Labels = mixedMoment B raw4244step0 raw4244step0Labels := by
      have hz : ∀ j, raw4244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4244step0 = (fun i j => raw4244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4244step0 raw4244; decide +kernel
      have hl : raw4244step0Labels = raw4244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4244 raw4244Labels permutation434 hz
    mixedMoment B raw4244step0 raw4244step0Labels = mixedMoment B raw4244step1 raw4244step1Labels := by
      have hz : ∀ j, raw4244step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4244step1 = (fun i j => raw4244step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4244step1 raw4244step0; decide +kernel
      have hl : raw4244step1Labels = raw4244step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4244step0 raw4244step0Labels permutation80 hz
    mixedMoment B raw4244step1 raw4244step1Labels = mixedMoment B raw4244step2 raw4244step2Labels := by
      have ha : raw4244step2 = (fun i j => raw4244step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4244step2 raw4244step1; decide +kernel
      have hl : raw4244step2Labels = raw4244step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4244step1 raw4244step1Labels permutation8 permutation6
    mixedMoment B raw4244step2 raw4244step2Labels = mixedMoment B raw4244step3 raw4244step3Labels := by
      have ha : raw4244step3 = raw4244step2 := by apply Matrix.ext; unfold raw4244step3 raw4244step2; decide +kernel
      have hl : raw4244step2Labels = labelEmbedding9 ∘ raw4244step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4244step2 raw4244step2Labels raw4244step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw4245 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4245step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4245step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4245step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4245step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4245 raw4245Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw4245 raw4245Labels = mixedMoment B raw4245step0 raw4245step0Labels := by
      have hz : ∀ j, raw4245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4245step0 = (fun i j => raw4245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4245step0 raw4245; decide +kernel
      have hl : raw4245step0Labels = raw4245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4245 raw4245Labels permutation346 hz
    mixedMoment B raw4245step0 raw4245step0Labels = mixedMoment B raw4245step1 raw4245step1Labels := by
      have ha : raw4245step1 = (fun i j => raw4245step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4245step1 raw4245step0; decide +kernel
      have hl : raw4245step1Labels = raw4245step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4245step0 raw4245step0Labels permutation32 permutation4
    mixedMoment B raw4245step1 raw4245step1Labels = mixedMoment B raw4245step2 raw4245step2Labels := by
      have ha : raw4245step2 = -raw4245step1 := by apply Matrix.ext; change ∀ i j, raw4245step2 i j = -(raw4245step1 i j); unfold raw4245step2 raw4245step1; decide +kernel
      have hl : raw4245step2Labels = raw4245step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4245step2 raw4245step2Labels = mixedMoment B raw4245step3 raw4245step3Labels := by
      have ha : raw4245step3 = raw4245step2 := by apply Matrix.ext; unfold raw4245step3 raw4245step2; decide +kernel
      have hl : raw4245step2Labels = labelEmbedding7 ∘ raw4245step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4245step2 raw4245step2Labels raw4245step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw4246 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4246step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4246step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4246 raw4246Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw4246 raw4246Labels = mixedMoment B raw4246step0 raw4246step0Labels := by
      have hz : ∀ j, raw4246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4246step0 = (fun i j => raw4246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4246step0 raw4246; decide +kernel
      have hl : raw4246step0Labels = raw4246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4246 raw4246Labels permutation346 hz
    mixedMoment B raw4246step0 raw4246step0Labels = mixedMoment B raw4246step1 raw4246step1Labels := by
      have ha : raw4246step1 = (fun i j => raw4246step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4246step1 raw4246step0; decide +kernel
      have hl : raw4246step1Labels = raw4246step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4246step0 raw4246step0Labels permutation32 permutation6
    mixedMoment B raw4246step1 raw4246step1Labels = mixedMoment B raw4246step2 raw4246step2Labels := by
      have ha : raw4246step2 = raw4246step1 := by apply Matrix.ext; unfold raw4246step2 raw4246step1; decide +kernel
      have hl : raw4246step1Labels = labelEmbedding9 ∘ raw4246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4246step1 raw4246step1Labels raw4246step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw4247 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4247step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4247 raw4247Labels = mixedMoment B node5239 node5239Labels := by
  calc
    mixedMoment B raw4247 raw4247Labels = mixedMoment B raw4247step0 raw4247step0Labels := by
      have ha : raw4247step0 = (fun i j => raw4247 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4247step0 raw4247; decide +kernel
      have hl : raw4247step0Labels = raw4247Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4247 raw4247Labels permutation152 permutation6
    mixedMoment B raw4247step0 raw4247step0Labels = mixedMoment B raw4247step1 raw4247step1Labels := by
      have ha : raw4247step1 = raw4247step0 := by apply Matrix.ext; unfold raw4247step1 raw4247step0; decide +kernel
      have hl : raw4247step0Labels = labelEmbedding9 ∘ raw4247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4247step0 raw4247step0Labels raw4247step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5239 node5239Labels := by rfl

def raw4248 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4248step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4248step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4248step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4248 raw4248Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4248 raw4248Labels = mixedMoment B raw4248step0 raw4248step0Labels := by
      have hz : ∀ j, raw4248 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4248step0 = (fun i j => raw4248 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4248step0 raw4248; decide +kernel
      have hl : raw4248step0Labels = raw4248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4248 raw4248Labels permutation520 hz
    mixedMoment B raw4248step0 raw4248step0Labels = mixedMoment B raw4248step1 raw4248step1Labels := by
      have hz : ∀ j, raw4248step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4248step1 = (fun i j => raw4248step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4248step1 raw4248step0; decide +kernel
      have hl : raw4248step1Labels = raw4248step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4248step0 raw4248step0Labels permutation80 hz
    mixedMoment B raw4248step1 raw4248step1Labels = mixedMoment B raw4248step2 raw4248step2Labels := by
      have ha : raw4248step2 = (fun i j => raw4248step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4248step2 raw4248step1; decide +kernel
      have hl : raw4248step2Labels = raw4248step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4248step1 raw4248step1Labels permutation8 permutation6
    mixedMoment B raw4248step2 raw4248step2Labels = mixedMoment B raw4248step3 raw4248step3Labels := by
      have ha : raw4248step3 = raw4248step2 := by apply Matrix.ext; unfold raw4248step3 raw4248step2; decide +kernel
      have hl : raw4248step2Labels = labelEmbedding9 ∘ raw4248step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4248step2 raw4248step2Labels raw4248step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw4249 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4249step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4249step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4249 raw4249Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw4249 raw4249Labels = mixedMoment B raw4249step0 raw4249step0Labels := by
      have hz : ∀ j, raw4249 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4249step0 = (fun i j => raw4249 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4249step0 raw4249; decide +kernel
      have hl : raw4249step0Labels = raw4249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4249 raw4249Labels permutation346 hz
    mixedMoment B raw4249step0 raw4249step0Labels = mixedMoment B raw4249step1 raw4249step1Labels := by
      have ha : raw4249step1 = (fun i j => raw4249step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4249step1 raw4249step0; decide +kernel
      have hl : raw4249step1Labels = raw4249step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4249step0 raw4249step0Labels permutation32 permutation6
    _ = mixedMoment B node3031 node3031Labels := by rfl

def raw4250 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4250step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4250 raw4250Labels = mixedMoment B node3061 node3061Labels := by
  calc
    mixedMoment B raw4250 raw4250Labels = mixedMoment B raw4250step0 raw4250step0Labels := by
      have ha : raw4250step0 = (fun i j => raw4250 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4250step0 raw4250; decide +kernel
      have hl : raw4250step0Labels = raw4250Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4250 raw4250Labels permutation152 permutation6
    _ = mixedMoment B node3061 node3061Labels := by rfl

def raw4251 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4251step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw4251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4251 raw4251Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw4251 raw4251Labels = mixedMoment B raw4251step0 raw4251step0Labels := by
      have hz : ∀ j, raw4251 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4251step0 = (fun i j => raw4251 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4251step0 raw4251; decide +kernel
      have hl : raw4251step0Labels = raw4251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4251 raw4251Labels permutation520 hz
    mixedMoment B raw4251step0 raw4251step0Labels = mixedMoment B raw4251step1 raw4251step1Labels := by
      have hz : ∀ j, raw4251step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4251step1 = (fun i j => raw4251step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4251step1 raw4251step0; decide +kernel
      have hl : raw4251step1Labels = raw4251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4251step0 raw4251step0Labels permutation80 hz
    mixedMoment B raw4251step1 raw4251step1Labels = mixedMoment B raw4251step2 raw4251step2Labels := by
      have ha : raw4251step2 = (fun i j => raw4251step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4251step2 raw4251step1; decide +kernel
      have hl : raw4251step2Labels = raw4251step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4251step1 raw4251step1Labels permutation8 permutation6
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw4252 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4252 raw4252Labels = mixedMoment B node3082 node3082Labels := by
  calc
    mixedMoment B raw4252 raw4252Labels = mixedMoment B raw4252step0 raw4252step0Labels := by
      have hz : ∀ j, raw4252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4252step0 = (fun i j => raw4252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4252step0 raw4252; decide +kernel
      have hl : raw4252step0Labels = raw4252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4252 raw4252Labels permutation346 hz
    mixedMoment B raw4252step0 raw4252step0Labels = mixedMoment B raw4252step1 raw4252step1Labels := by
      have ha : raw4252step1 = (fun i j => raw4252step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4252step1 raw4252step0; decide +kernel
      have hl : raw4252step1Labels = raw4252step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4252step0 raw4252step0Labels permutation32 permutation6
    _ = mixedMoment B node3082 node3082Labels := by rfl

def raw4253 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4253step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4253 raw4253Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4253 raw4253Labels = mixedMoment B raw4253step0 raw4253step0Labels := by
      have hz : ∀ j, raw4253 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4253step0 = (fun i j => raw4253 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4253step0 raw4253; decide +kernel
      have hl : raw4253step0Labels = raw4253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4253 raw4253Labels permutation265 hz
    mixedMoment B raw4253step0 raw4253step0Labels = mixedMoment B raw4253step1 raw4253step1Labels := by
      have ha : raw4253step1 = (fun i j => raw4253step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4253step1 raw4253step0; decide +kernel
      have hl : raw4253step1Labels = raw4253step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4253step0 raw4253step0Labels permutation32 permutation6
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw4254 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4254step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4254step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4254step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4254step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4254step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4254 raw4254Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw4254 raw4254Labels = mixedMoment B raw4254step0 raw4254step0Labels := by
      have hz : ∀ j, raw4254 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4254step0 = (fun i j => raw4254 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4254step0 raw4254; decide +kernel
      have hl : raw4254step0Labels = raw4254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4254 raw4254Labels permutation520 hz
    mixedMoment B raw4254step0 raw4254step0Labels = mixedMoment B raw4254step1 raw4254step1Labels := by
      have hz : ∀ j, raw4254step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4254step1 = (fun i j => raw4254step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4254step1 raw4254step0; decide +kernel
      have hl : raw4254step1Labels = raw4254step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4254step0 raw4254step0Labels permutation80 hz
    mixedMoment B raw4254step1 raw4254step1Labels = mixedMoment B raw4254step2 raw4254step2Labels := by
      have hz : ∀ j, raw4254step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4254step2 = (fun i j => raw4254step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4254step2 raw4254step1; decide +kernel
      have hl : raw4254step2Labels = raw4254step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4254step1 raw4254step1Labels permutation14 hz
    mixedMoment B raw4254step2 raw4254step2Labels = mixedMoment B raw4254step3 raw4254step3Labels := by
      have ha : raw4254step3 = (fun i j => raw4254step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4254step3 raw4254step2; decide +kernel
      have hl : raw4254step3Labels = raw4254step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4254step2 raw4254step2Labels permutation2 permutation6
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw4255 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4255 raw4255Labels = mixedMoment B node2660 node2660Labels := by
  calc
    mixedMoment B raw4255 raw4255Labels = mixedMoment B raw4255step0 raw4255step0Labels := by
      have ha : raw4255step0 = (fun i j => raw4255 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4255step0 raw4255; decide +kernel
      have hl : raw4255step0Labels = raw4255Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4255 raw4255Labels permutation152 permutation6
    _ = mixedMoment B node2660 node2660Labels := by rfl

def raw4256 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4256 raw4256Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4256 raw4256Labels = mixedMoment B raw4256step0 raw4256step0Labels := by
      have hz : ∀ j, raw4256 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4256step0 = (fun i j => raw4256 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4256step0 raw4256; decide +kernel
      have hl : raw4256step0Labels = raw4256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4256 raw4256Labels permutation520 hz
    mixedMoment B raw4256step0 raw4256step0Labels = mixedMoment B raw4256step1 raw4256step1Labels := by
      have ha : raw4256step1 = (fun i j => raw4256step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4256step1 raw4256step0; decide +kernel
      have hl : raw4256step1Labels = raw4256step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4256step0 raw4256step0Labels permutation32 permutation6
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw4257 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4257step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4257 raw4257Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw4257 raw4257Labels = mixedMoment B raw4257step0 raw4257step0Labels := by
      have hz : ∀ j, raw4257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4257step0 = (fun i j => raw4257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4257step0 raw4257; decide +kernel
      have hl : raw4257step0Labels = raw4257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4257 raw4257Labels permutation346 hz
    mixedMoment B raw4257step0 raw4257step0Labels = mixedMoment B raw4257step1 raw4257step1Labels := by
      have ha : raw4257step1 = (fun i j => raw4257step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4257step1 raw4257step0; decide +kernel
      have hl : raw4257step1Labels = raw4257step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4257step0 raw4257step0Labels permutation34 permutation6
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw4258 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4258 raw4258Labels = mixedMoment B node2667 node2667Labels := by
  calc
    mixedMoment B raw4258 raw4258Labels = mixedMoment B raw4258step0 raw4258step0Labels := by
      have hz : ∀ j, raw4258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4258step0 = (fun i j => raw4258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4258step0 raw4258; decide +kernel
      have hl : raw4258step0Labels = raw4258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4258 raw4258Labels permutation346 hz
    mixedMoment B raw4258step0 raw4258step0Labels = mixedMoment B raw4258step1 raw4258step1Labels := by
      have ha : raw4258step1 = (fun i j => raw4258step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4258step1 raw4258step0; decide +kernel
      have hl : raw4258step1Labels = raw4258step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4258step0 raw4258step0Labels permutation34 permutation6
    _ = mixedMoment B node2667 node2667Labels := by rfl

def raw4259 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4259 raw4259Labels = mixedMoment B node2692 node2692Labels := by
  calc
    mixedMoment B raw4259 raw4259Labels = mixedMoment B raw4259step0 raw4259step0Labels := by
      have ha : raw4259step0 = (fun i j => raw4259 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4259step0 raw4259; decide +kernel
      have hl : raw4259step0Labels = raw4259Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4259 raw4259Labels permutation154 permutation6
    _ = mixedMoment B node2692 node2692Labels := by rfl

def raw4260 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4260step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4260step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4260step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4260 raw4260Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw4260 raw4260Labels = mixedMoment B raw4260step0 raw4260step0Labels := by
      have hz : ∀ j, raw4260 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4260step0 = (fun i j => raw4260 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4260step0 raw4260; decide +kernel
      have hl : raw4260step0Labels = raw4260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4260 raw4260Labels permutation520 hz
    mixedMoment B raw4260step0 raw4260step0Labels = mixedMoment B raw4260step1 raw4260step1Labels := by
      have hz : ∀ j, raw4260step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4260step1 = (fun i j => raw4260step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4260step1 raw4260step0; decide +kernel
      have hl : raw4260step1Labels = raw4260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4260step0 raw4260step0Labels permutation80 hz
    mixedMoment B raw4260step1 raw4260step1Labels = mixedMoment B raw4260step2 raw4260step2Labels := by
      have ha : raw4260step2 = (fun i j => raw4260step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4260step2 raw4260step1; decide +kernel
      have hl : raw4260step2Labels = raw4260step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4260step1 raw4260step1Labels permutation8 permutation6
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw4261 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4261 raw4261Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw4261 raw4261Labels = mixedMoment B raw4261step0 raw4261step0Labels := by
      have hz : ∀ j, raw4261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4261step0 = (fun i j => raw4261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4261step0 raw4261; decide +kernel
      have hl : raw4261step0Labels = raw4261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4261 raw4261Labels permutation346 hz
    mixedMoment B raw4261step0 raw4261step0Labels = mixedMoment B raw4261step1 raw4261step1Labels := by
      have ha : raw4261step1 = (fun i j => raw4261step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4261step1 raw4261step0; decide +kernel
      have hl : raw4261step1Labels = raw4261step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4261step0 raw4261step0Labels permutation34 permutation6
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw4262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4262step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4262step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4262 raw4262Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw4262 raw4262Labels = mixedMoment B raw4262step0 raw4262step0Labels := by
      have hz : ∀ j, raw4262 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4262step0 = (fun i j => raw4262 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4262step0 raw4262; decide +kernel
      have hl : raw4262step0Labels = raw4262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4262 raw4262Labels permutation434 hz
    mixedMoment B raw4262step0 raw4262step0Labels = mixedMoment B raw4262step1 raw4262step1Labels := by
      have hz : ∀ j, raw4262step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4262step1 = (fun i j => raw4262step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4262step1 raw4262step0; decide +kernel
      have hl : raw4262step1Labels = raw4262step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4262step0 raw4262step0Labels permutation80 hz
    mixedMoment B raw4262step1 raw4262step1Labels = mixedMoment B raw4262step2 raw4262step2Labels := by
      have ha : raw4262step2 = (fun i j => raw4262step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4262step2 raw4262step1; decide +kernel
      have hl : raw4262step2Labels = raw4262step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4262step1 raw4262step1Labels permutation8 permutation6
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw4263 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4263 raw4263Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw4263 raw4263Labels = mixedMoment B raw4263step0 raw4263step0Labels := by
      have hz : ∀ j, raw4263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4263step0 = (fun i j => raw4263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4263step0 raw4263; decide +kernel
      have hl : raw4263step0Labels = raw4263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4263 raw4263Labels permutation346 hz
    mixedMoment B raw4263step0 raw4263step0Labels = mixedMoment B raw4263step1 raw4263step1Labels := by
      have ha : raw4263step1 = (fun i j => raw4263step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4263step1 raw4263step0; decide +kernel
      have hl : raw4263step1Labels = raw4263step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4263step0 raw4263step0Labels permutation32 permutation6
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw4264 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4264 raw4264Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw4264 raw4264Labels = mixedMoment B raw4264step0 raw4264step0Labels := by
      have hz : ∀ j, raw4264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4264step0 = (fun i j => raw4264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4264step0 raw4264; decide +kernel
      have hl : raw4264step0Labels = raw4264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4264 raw4264Labels permutation346 hz
    mixedMoment B raw4264step0 raw4264step0Labels = mixedMoment B raw4264step1 raw4264step1Labels := by
      have ha : raw4264step1 = (fun i j => raw4264step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4264step1 raw4264step0; decide +kernel
      have hl : raw4264step1Labels = raw4264step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4264step0 raw4264step0Labels permutation32 permutation6
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw4265 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4265 raw4265Labels = mixedMoment B node2691 node2691Labels := by
  calc
    mixedMoment B raw4265 raw4265Labels = mixedMoment B raw4265step0 raw4265step0Labels := by
      have ha : raw4265step0 = (fun i j => raw4265 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4265step0 raw4265; decide +kernel
      have hl : raw4265step0Labels = raw4265Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4265 raw4265Labels permutation152 permutation6
    _ = mixedMoment B node2691 node2691Labels := by rfl

def raw4266 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4266step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4266step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4266step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4266 raw4266Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw4266 raw4266Labels = mixedMoment B raw4266step0 raw4266step0Labels := by
      have hz : ∀ j, raw4266 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4266step0 = (fun i j => raw4266 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4266step0 raw4266; decide +kernel
      have hl : raw4266step0Labels = raw4266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4266 raw4266Labels permutation520 hz
    mixedMoment B raw4266step0 raw4266step0Labels = mixedMoment B raw4266step1 raw4266step1Labels := by
      have hz : ∀ j, raw4266step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4266step1 = (fun i j => raw4266step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4266step1 raw4266step0; decide +kernel
      have hl : raw4266step1Labels = raw4266step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4266step0 raw4266step0Labels permutation80 hz
    mixedMoment B raw4266step1 raw4266step1Labels = mixedMoment B raw4266step2 raw4266step2Labels := by
      have ha : raw4266step2 = (fun i j => raw4266step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4266step2 raw4266step1; decide +kernel
      have hl : raw4266step2Labels = raw4266step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4266step1 raw4266step1Labels permutation8 permutation6
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw4267 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4267 raw4267Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw4267 raw4267Labels = mixedMoment B raw4267step0 raw4267step0Labels := by
      have hz : ∀ j, raw4267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4267step0 = (fun i j => raw4267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4267step0 raw4267; decide +kernel
      have hl : raw4267step0Labels = raw4267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4267 raw4267Labels permutation346 hz
    mixedMoment B raw4267step0 raw4267step0Labels = mixedMoment B raw4267step1 raw4267step1Labels := by
      have ha : raw4267step1 = (fun i j => raw4267step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4267step1 raw4267step0; decide +kernel
      have hl : raw4267step1Labels = raw4267step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4267step0 raw4267step0Labels permutation137 permutation2
    _ = mixedMoment B node3543 node3543Labels := by rfl

def raw4268 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4268 raw4268Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw4268 raw4268Labels = mixedMoment B raw4268step0 raw4268step0Labels := by
      have hz : ∀ j, raw4268 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4268step0 = (fun i j => raw4268 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4268step0 raw4268; decide +kernel
      have hl : raw4268step0Labels = raw4268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4268 raw4268Labels permutation346 hz
    mixedMoment B raw4268step0 raw4268step0Labels = mixedMoment B raw4268step1 raw4268step1Labels := by
      have ha : raw4268step1 = (fun i j => raw4268step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4268step1 raw4268step0; decide +kernel
      have hl : raw4268step1Labels = raw4268step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4268step0 raw4268step0Labels permutation137 permutation2
    _ = mixedMoment B node3389 node3389Labels := by rfl

def raw4269 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4269 raw4269Labels = mixedMoment B node3492 node3492Labels := by
  calc
    mixedMoment B raw4269 raw4269Labels = mixedMoment B raw4269step0 raw4269step0Labels := by
      have ha : raw4269step0 = (fun i j => raw4269 (permutation609 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4269step0 raw4269; decide +kernel
      have hl : raw4269step0Labels = raw4269Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4269 raw4269Labels permutation609 permutation2
    _ = mixedMoment B node3492 node3492Labels := by rfl

def raw4270 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4270step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4270 raw4270Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw4270 raw4270Labels = mixedMoment B raw4270step0 raw4270step0Labels := by
      have hz : ∀ j, raw4270 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4270step0 = (fun i j => raw4270 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4270step0 raw4270; decide +kernel
      have hl : raw4270step0Labels = raw4270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4270 raw4270Labels permutation520 hz
    mixedMoment B raw4270step0 raw4270step0Labels = mixedMoment B raw4270step1 raw4270step1Labels := by
      have hz : ∀ j, raw4270step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4270step1 = (fun i j => raw4270step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4270step1 raw4270step0; decide +kernel
      have hl : raw4270step1Labels = raw4270step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4270step0 raw4270step0Labels permutation80 hz
    mixedMoment B raw4270step1 raw4270step1Labels = mixedMoment B raw4270step2 raw4270step2Labels := by
      have ha : raw4270step2 = (fun i j => raw4270step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4270step2 raw4270step1; decide +kernel
      have hl : raw4270step2Labels = raw4270step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4270step1 raw4270step1Labels permutation29 permutation2
    _ = mixedMoment B node3545 node3545Labels := by rfl

def raw4271 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4271 raw4271Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw4271 raw4271Labels = mixedMoment B raw4271step0 raw4271step0Labels := by
      have hz : ∀ j, raw4271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4271step0 = (fun i j => raw4271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4271step0 raw4271; decide +kernel
      have hl : raw4271step0Labels = raw4271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4271 raw4271Labels permutation346 hz
    mixedMoment B raw4271step0 raw4271step0Labels = mixedMoment B raw4271step1 raw4271step1Labels := by
      have ha : raw4271step1 = (fun i j => raw4271step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4271step1 raw4271step0; decide +kernel
      have hl : raw4271step1Labels = raw4271step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4271step0 raw4271step0Labels permutation137 permutation2
    _ = mixedMoment B node2052 node2052Labels := by rfl

def raw4272 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4272step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4272step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4272step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4272step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4272 raw4272Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw4272 raw4272Labels = mixedMoment B raw4272step0 raw4272step0Labels := by
      have hz : ∀ j, raw4272 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4272step0 = (fun i j => raw4272 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4272step0 raw4272; decide +kernel
      have hl : raw4272step0Labels = raw4272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4272 raw4272Labels permutation346 hz
    mixedMoment B raw4272step0 raw4272step0Labels = mixedMoment B raw4272step1 raw4272step1Labels := by
      have hz : ∀ j, raw4272step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4272step1 = (fun i j => raw4272step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4272step1 raw4272step0; decide +kernel
      have hl : raw4272step1Labels = raw4272step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4272step0 raw4272step0Labels permutation56 hz
    mixedMoment B raw4272step1 raw4272step1Labels = mixedMoment B raw4272step2 raw4272step2Labels := by
      have ha : raw4272step2 = (fun i j => raw4272step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4272step2 raw4272step1; decide +kernel
      have hl : raw4272step2Labels = raw4272step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4272step1 raw4272step1Labels permutation8 permutation4
    mixedMoment B raw4272step2 raw4272step2Labels = mixedMoment B raw4272step3 raw4272step3Labels := by
      have ha : raw4272step3 = -raw4272step2 := by apply Matrix.ext; change ∀ i j, raw4272step3 i j = -(raw4272step2 i j); unfold raw4272step3 raw4272step2; decide +kernel
      have hl : raw4272step3Labels = raw4272step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw4273 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4273step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4273step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4273step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4273 raw4273Labels = mixedMoment B node2050 node2050Labels := by
  calc
    mixedMoment B raw4273 raw4273Labels = mixedMoment B raw4273step0 raw4273step0Labels := by
      have ha : raw4273step0 = (fun i j => raw4273 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4273step0 raw4273; decide +kernel
      have hl : raw4273step0Labels = raw4273Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4273 raw4273Labels permutation152 permutation4
    mixedMoment B raw4273step0 raw4273step0Labels = mixedMoment B raw4273step1 raw4273step1Labels := by
      have ha : raw4273step1 = -raw4273step0 := by apply Matrix.ext; change ∀ i j, raw4273step1 i j = -(raw4273step0 i j); unfold raw4273step1 raw4273step0; decide +kernel
      have hl : raw4273step1Labels = raw4273step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2050 node2050Labels := by rfl

def raw4274 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4274Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw4274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4274 raw4274Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw4274 raw4274Labels = mixedMoment B raw4274step0 raw4274step0Labels := by
      have hz : ∀ j, raw4274 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4274step0 = (fun i j => raw4274 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4274step0 raw4274; decide +kernel
      have hl : raw4274step0Labels = raw4274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4274 raw4274Labels permutation346 hz
    mixedMoment B raw4274step0 raw4274step0Labels = mixedMoment B raw4274step1 raw4274step1Labels := by
      have ha : raw4274step1 = (fun i j => raw4274step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4274step1 raw4274step0; decide +kernel
      have hl : raw4274step1Labels = raw4274step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4274step0 raw4274step0Labels permutation35 permutation4
    mixedMoment B raw4274step1 raw4274step1Labels = mixedMoment B raw4274step2 raw4274step2Labels := by
      have ha : raw4274step2 = -raw4274step1 := by apply Matrix.ext; change ∀ i j, raw4274step2 i j = -(raw4274step1 i j); unfold raw4274step2 raw4274step1; decide +kernel
      have hl : raw4274step2Labels = raw4274step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2055 node2055Labels := by rfl

def raw4275 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4275 raw4275Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw4275 raw4275Labels = mixedMoment B raw4275step0 raw4275step0Labels := by
      have hz : ∀ j, raw4275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4275step0 = (fun i j => raw4275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4275step0 raw4275; decide +kernel
      have hl : raw4275step0Labels = raw4275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4275 raw4275Labels permutation346 hz
    mixedMoment B raw4275step0 raw4275step0Labels = mixedMoment B raw4275step1 raw4275step1Labels := by
      have ha : raw4275step1 = (fun i j => raw4275step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4275step1 raw4275step0; decide +kernel
      have hl : raw4275step1Labels = raw4275step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4275step0 raw4275step0Labels permutation32 permutation4
    mixedMoment B raw4275step1 raw4275step1Labels = mixedMoment B raw4275step2 raw4275step2Labels := by
      have ha : raw4275step2 = -raw4275step1 := by apply Matrix.ext; change ∀ i j, raw4275step2 i j = -(raw4275step1 i j); unfold raw4275step2 raw4275step1; decide +kernel
      have hl : raw4275step2Labels = raw4275step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2052 node2052Labels := by rfl

def raw4276 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4276 raw4276Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw4276 raw4276Labels = mixedMoment B raw4276step0 raw4276step0Labels := by
      have hz : ∀ j, raw4276 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4276step0 = (fun i j => raw4276 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4276step0 raw4276; decide +kernel
      have hl : raw4276step0Labels = raw4276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4276 raw4276Labels permutation265 hz
    mixedMoment B raw4276step0 raw4276step0Labels = mixedMoment B raw4276step1 raw4276step1Labels := by
      have ha : raw4276step1 = (fun i j => raw4276step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4276step1 raw4276step0; decide +kernel
      have hl : raw4276step1Labels = raw4276step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4276step0 raw4276step0Labels permutation137 permutation2
    _ = mixedMoment B node3543 node3543Labels := by rfl

def raw4277 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4277step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4277step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4277step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]
def raw4277step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4277 raw4277Labels = mixedMoment B node3634 node3634Labels := by
  calc
    mixedMoment B raw4277 raw4277Labels = mixedMoment B raw4277step0 raw4277step0Labels := by
      have hz : ∀ j, raw4277 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4277step0 = (fun i j => raw4277 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4277step0 raw4277; decide +kernel
      have hl : raw4277step0Labels = raw4277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4277 raw4277Labels permutation520 hz
    mixedMoment B raw4277step0 raw4277step0Labels = mixedMoment B raw4277step1 raw4277step1Labels := by
      have hz : ∀ j, raw4277step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4277step1 = (fun i j => raw4277step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4277step1 raw4277step0; decide +kernel
      have hl : raw4277step1Labels = raw4277step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4277step0 raw4277step0Labels permutation80 hz
    mixedMoment B raw4277step1 raw4277step1Labels = mixedMoment B raw4277step2 raw4277step2Labels := by
      have hz : ∀ j, raw4277step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4277step2 = (fun i j => raw4277step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4277step2 raw4277step1; decide +kernel
      have hl : raw4277step2Labels = raw4277step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4277step1 raw4277step1Labels permutation14 hz
    mixedMoment B raw4277step2 raw4277step2Labels = mixedMoment B raw4277step3 raw4277step3Labels := by
      have ha : raw4277step3 = (fun i j => raw4277step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4277step3 raw4277step2; decide +kernel
      have hl : raw4277step3Labels = raw4277step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4277step2 raw4277step2Labels permutation7 permutation2
    _ = mixedMoment B node3634 node3634Labels := by rfl

def raw4278 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4278 raw4278Labels = mixedMoment B node3387 node3387Labels := by
  calc
    mixedMoment B raw4278 raw4278Labels = mixedMoment B raw4278step0 raw4278step0Labels := by
      have ha : raw4278step0 = (fun i j => raw4278 (permutation609 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4278step0 raw4278; decide +kernel
      have hl : raw4278step0Labels = raw4278Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4278 raw4278Labels permutation609 permutation2
    _ = mixedMoment B node3387 node3387Labels := by rfl

def raw4279 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4279 raw4279Labels = mixedMoment B node3393 node3393Labels := by
  calc
    mixedMoment B raw4279 raw4279Labels = mixedMoment B raw4279step0 raw4279step0Labels := by
      have hz : ∀ j, raw4279 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4279step0 = (fun i j => raw4279 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4279step0 raw4279; decide +kernel
      have hl : raw4279step0Labels = raw4279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4279 raw4279Labels permutation346 hz
    mixedMoment B raw4279step0 raw4279step0Labels = mixedMoment B raw4279step1 raw4279step1Labels := by
      have ha : raw4279step1 = (fun i j => raw4279step0 (permutation138 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4279step1 raw4279step0; decide +kernel
      have hl : raw4279step1Labels = raw4279step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4279step0 raw4279step0Labels permutation138 permutation2
    _ = mixedMoment B node3393 node3393Labels := by rfl

def raw4280 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4280Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4280step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4280step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4280 raw4280Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw4280 raw4280Labels = mixedMoment B raw4280step0 raw4280step0Labels := by
      have hz : ∀ j, raw4280 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4280step0 = (fun i j => raw4280 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4280step0 raw4280; decide +kernel
      have hl : raw4280step0Labels = raw4280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4280 raw4280Labels permutation346 hz
    mixedMoment B raw4280step0 raw4280step0Labels = mixedMoment B raw4280step1 raw4280step1Labels := by
      have ha : raw4280step1 = (fun i j => raw4280step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4280step1 raw4280step0; decide +kernel
      have hl : raw4280step1Labels = raw4280step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4280step0 raw4280step0Labels permutation32 permutation4
    mixedMoment B raw4280step1 raw4280step1Labels = mixedMoment B raw4280step2 raw4280step2Labels := by
      have ha : raw4280step2 = -raw4280step1 := by apply Matrix.ext; change ∀ i j, raw4280step2 i j = -(raw4280step1 i j); unfold raw4280step2 raw4280step1; decide +kernel
      have hl : raw4280step2Labels = raw4280step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3389 node3389Labels := by rfl

def raw4281 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4281step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4281 raw4281Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw4281 raw4281Labels = mixedMoment B raw4281step0 raw4281step0Labels := by
      have hz : ∀ j, raw4281 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4281step0 = (fun i j => raw4281 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4281step0 raw4281; decide +kernel
      have hl : raw4281step0Labels = raw4281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4281 raw4281Labels permutation520 hz
    mixedMoment B raw4281step0 raw4281step0Labels = mixedMoment B raw4281step1 raw4281step1Labels := by
      have ha : raw4281step1 = (fun i j => raw4281step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4281step1 raw4281step0; decide +kernel
      have hl : raw4281step1Labels = raw4281step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4281step0 raw4281step0Labels permutation137 permutation2
    _ = mixedMoment B node3543 node3543Labels := by rfl

def raw4282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4282step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4282step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4282step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4282step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4282 raw4282Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw4282 raw4282Labels = mixedMoment B raw4282step0 raw4282step0Labels := by
      have hz : ∀ j, raw4282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4282step0 = (fun i j => raw4282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4282step0 raw4282; decide +kernel
      have hl : raw4282step0Labels = raw4282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4282 raw4282Labels permutation434 hz
    mixedMoment B raw4282step0 raw4282step0Labels = mixedMoment B raw4282step1 raw4282step1Labels := by
      have hz : ∀ j, raw4282step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4282step1 = (fun i j => raw4282step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4282step1 raw4282step0; decide +kernel
      have hl : raw4282step1Labels = raw4282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4282step0 raw4282step0Labels permutation80 hz
    mixedMoment B raw4282step1 raw4282step1Labels = mixedMoment B raw4282step2 raw4282step2Labels := by
      have ha : raw4282step2 = (fun i j => raw4282step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4282step2 raw4282step1; decide +kernel
      have hl : raw4282step2Labels = raw4282step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4282step1 raw4282step1Labels permutation31 permutation3
    mixedMoment B raw4282step2 raw4282step2Labels = mixedMoment B raw4282step3 raw4282step3Labels := by
      have ha : raw4282step3 = -raw4282step2 := by apply Matrix.ext; change ∀ i j, raw4282step3 i j = -(raw4282step2 i j); unfold raw4282step3 raw4282step2; decide +kernel
      have hl : raw4282step3Labels = raw4282step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4282step3 raw4282step3Labels = mixedMoment B raw4282step4 raw4282step4Labels := by
      have ha : raw4282step4 = raw4282step3 := by apply Matrix.ext; unfold raw4282step4 raw4282step3; decide +kernel
      have hl : raw4282step3Labels = labelEmbedding6 ∘ raw4282step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4282step3 raw4282step3Labels raw4282step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw4283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4283step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4283step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4283step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4283step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4283step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4283 raw4283Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw4283 raw4283Labels = mixedMoment B raw4283step0 raw4283step0Labels := by
      have hz : ∀ j, raw4283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4283step0 = (fun i j => raw4283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4283step0 raw4283; decide +kernel
      have hl : raw4283step0Labels = raw4283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4283 raw4283Labels permutation434 hz
    mixedMoment B raw4283step0 raw4283step0Labels = mixedMoment B raw4283step1 raw4283step1Labels := by
      have hz : ∀ j, raw4283step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4283step1 = (fun i j => raw4283step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4283step1 raw4283step0; decide +kernel
      have hl : raw4283step1Labels = raw4283step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4283step0 raw4283step0Labels permutation56 hz
    mixedMoment B raw4283step1 raw4283step1Labels = mixedMoment B raw4283step2 raw4283step2Labels := by
      have ha : raw4283step2 = (fun i j => raw4283step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4283step2 raw4283step1; decide +kernel
      have hl : raw4283step2Labels = raw4283step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4283step1 raw4283step1Labels permutation31 permutation3
    mixedMoment B raw4283step2 raw4283step2Labels = mixedMoment B raw4283step3 raw4283step3Labels := by
      have ha : raw4283step3 = -raw4283step2 := by apply Matrix.ext; change ∀ i j, raw4283step3 i j = -(raw4283step2 i j); unfold raw4283step3 raw4283step2; decide +kernel
      have hl : raw4283step3Labels = raw4283step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4283step3 raw4283step3Labels = mixedMoment B raw4283step4 raw4283step4Labels := by
      have ha : raw4283step4 = raw4283step3 := by apply Matrix.ext; unfold raw4283step4 raw4283step3; decide +kernel
      have hl : raw4283step3Labels = labelEmbedding6 ∘ raw4283step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4283step3 raw4283step3Labels raw4283step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw4284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4284step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4284step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4284step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4284step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4284step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4284step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4284 raw4284Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw4284 raw4284Labels = mixedMoment B raw4284step0 raw4284step0Labels := by
      have hz : ∀ j, raw4284 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4284step0 = (fun i j => raw4284 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4284step0 raw4284; decide +kernel
      have hl : raw4284step0Labels = raw4284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4284 raw4284Labels permutation346 hz
    mixedMoment B raw4284step0 raw4284step0Labels = mixedMoment B raw4284step1 raw4284step1Labels := by
      have hz : ∀ j, raw4284step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4284step1 = (fun i j => raw4284step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4284step1 raw4284step0; decide +kernel
      have hl : raw4284step1Labels = raw4284step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4284step0 raw4284step0Labels permutation56 hz
    mixedMoment B raw4284step1 raw4284step1Labels = mixedMoment B raw4284step2 raw4284step2Labels := by
      have ha : raw4284step2 = (fun i j => raw4284step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4284step2 raw4284step1; decide +kernel
      have hl : raw4284step2Labels = raw4284step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4284step1 raw4284step1Labels permutation31 permutation3
    mixedMoment B raw4284step2 raw4284step2Labels = mixedMoment B raw4284step3 raw4284step3Labels := by
      have ha : raw4284step3 = -raw4284step2 := by apply Matrix.ext; change ∀ i j, raw4284step3 i j = -(raw4284step2 i j); unfold raw4284step3 raw4284step2; decide +kernel
      have hl : raw4284step3Labels = raw4284step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4284step3 raw4284step3Labels = mixedMoment B raw4284step4 raw4284step4Labels := by
      have ha : raw4284step4 = raw4284step3 := by apply Matrix.ext; unfold raw4284step4 raw4284step3; decide +kernel
      have hl : raw4284step3Labels = labelEmbedding6 ∘ raw4284step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4284step3 raw4284step3Labels raw4284step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw4285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4285step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![3, -2, -1]]
def raw4285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4285step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw4285step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4285step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4285step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4285step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4285step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4285 raw4285Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw4285 raw4285Labels = mixedMoment B raw4285step0 raw4285step0Labels := by
      have hz : ∀ j, raw4285 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4285step0 = (fun i j => raw4285 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4285step0 raw4285; decide +kernel
      have hl : raw4285step0Labels = raw4285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4285 raw4285Labels permutation434 hz
    mixedMoment B raw4285step0 raw4285step0Labels = mixedMoment B raw4285step1 raw4285step1Labels := by
      have hz : ∀ j, raw4285step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4285step1 = (fun i j => raw4285step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4285step1 raw4285step0; decide +kernel
      have hl : raw4285step1Labels = raw4285step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4285step0 raw4285step0Labels permutation80 hz
    mixedMoment B raw4285step1 raw4285step1Labels = mixedMoment B raw4285step2 raw4285step2Labels := by
      have hz : ∀ j, raw4285step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4285step2 = (fun i j => raw4285step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4285step2 raw4285step1; decide +kernel
      have hl : raw4285step2Labels = raw4285step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4285step1 raw4285step1Labels permutation14 hz
    mixedMoment B raw4285step2 raw4285step2Labels = mixedMoment B raw4285step3 raw4285step3Labels := by
      have ha : raw4285step3 = (fun i j => raw4285step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4285step3 raw4285step2; decide +kernel
      have hl : raw4285step3Labels = raw4285step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4285step2 raw4285step2Labels permutation7 permutation3
    mixedMoment B raw4285step3 raw4285step3Labels = mixedMoment B raw4285step4 raw4285step4Labels := by
      have ha : raw4285step4 = -raw4285step3 := by apply Matrix.ext; change ∀ i j, raw4285step4 i j = -(raw4285step3 i j); unfold raw4285step4 raw4285step3; decide +kernel
      have hl : raw4285step4Labels = raw4285step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4285step4 raw4285step4Labels = mixedMoment B raw4285step5 raw4285step5Labels := by
      have ha : raw4285step5 = raw4285step4 := by apply Matrix.ext; unfold raw4285step5 raw4285step4; decide +kernel
      have hl : raw4285step4Labels = labelEmbedding6 ∘ raw4285step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4285step4 raw4285step4Labels raw4285step5Labels labelEmbedding6 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw4286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4286step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw4286step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4286 raw4286Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw4286 raw4286Labels = mixedMoment B raw4286step0 raw4286step0Labels := by
      have hz : ∀ j, raw4286 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4286step0 = (fun i j => raw4286 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4286step0 raw4286; decide +kernel
      have hl : raw4286step0Labels = raw4286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4286 raw4286Labels permutation434 hz
    mixedMoment B raw4286step0 raw4286step0Labels = mixedMoment B raw4286step1 raw4286step1Labels := by
      have hz : ∀ j, raw4286step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4286step1 = (fun i j => raw4286step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4286step1 raw4286step0; decide +kernel
      have hl : raw4286step1Labels = raw4286step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4286step0 raw4286step0Labels permutation80 hz
    mixedMoment B raw4286step1 raw4286step1Labels = mixedMoment B raw4286step2 raw4286step2Labels := by
      have hz : ∀ j, raw4286step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4286step2 = (fun i j => raw4286step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4286step2 raw4286step1; decide +kernel
      have hl : raw4286step2Labels = raw4286step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4286step1 raw4286step1Labels permutation14 hz
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw4287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4287step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4287step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4287step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4287step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4287 raw4287Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw4287 raw4287Labels = mixedMoment B raw4287step0 raw4287step0Labels := by
      have hz : ∀ j, raw4287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4287step0 = (fun i j => raw4287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4287step0 raw4287; decide +kernel
      have hl : raw4287step0Labels = raw4287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4287 raw4287Labels permutation434 hz
    mixedMoment B raw4287step0 raw4287step0Labels = mixedMoment B raw4287step1 raw4287step1Labels := by
      have hz : ∀ j, raw4287step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4287step1 = (fun i j => raw4287step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4287step1 raw4287step0; decide +kernel
      have hl : raw4287step1Labels = raw4287step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4287step0 raw4287step0Labels permutation80 hz
    mixedMoment B raw4287step1 raw4287step1Labels = mixedMoment B raw4287step2 raw4287step2Labels := by
      have ha : raw4287step2 = (fun i j => raw4287step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4287step2 raw4287step1; decide +kernel
      have hl : raw4287step2Labels = raw4287step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4287step1 raw4287step1Labels permutation10 permutation3
    mixedMoment B raw4287step2 raw4287step2Labels = mixedMoment B raw4287step3 raw4287step3Labels := by
      have ha : raw4287step3 = raw4287step2 := by apply Matrix.ext; unfold raw4287step3 raw4287step2; decide +kernel
      have hl : raw4287step2Labels = labelEmbedding6 ∘ raw4287step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4287step2 raw4287step2Labels raw4287step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw4288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4288step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4288step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4288step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4288step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4288 raw4288Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw4288 raw4288Labels = mixedMoment B raw4288step0 raw4288step0Labels := by
      have hz : ∀ j, raw4288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4288step0 = (fun i j => raw4288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4288step0 raw4288; decide +kernel
      have hl : raw4288step0Labels = raw4288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4288 raw4288Labels permutation434 hz
    mixedMoment B raw4288step0 raw4288step0Labels = mixedMoment B raw4288step1 raw4288step1Labels := by
      have ha : raw4288step1 = (fun i j => raw4288step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4288step1 raw4288step0; decide +kernel
      have hl : raw4288step1Labels = raw4288step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4288step0 raw4288step0Labels permutation139 permutation3
    mixedMoment B raw4288step1 raw4288step1Labels = mixedMoment B raw4288step2 raw4288step2Labels := by
      have ha : raw4288step2 = -raw4288step1 := by apply Matrix.ext; change ∀ i j, raw4288step2 i j = -(raw4288step1 i j); unfold raw4288step2 raw4288step1; decide +kernel
      have hl : raw4288step2Labels = raw4288step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4288step2 raw4288step2Labels = mixedMoment B raw4288step3 raw4288step3Labels := by
      have ha : raw4288step3 = raw4288step2 := by apply Matrix.ext; unfold raw4288step3 raw4288step2; decide +kernel
      have hl : raw4288step2Labels = labelEmbedding6 ∘ raw4288step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4288step2 raw4288step2Labels raw4288step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw4289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4289step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4289step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4289step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4289 raw4289Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw4289 raw4289Labels = mixedMoment B raw4289step0 raw4289step0Labels := by
      have hz : ∀ j, raw4289 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4289step0 = (fun i j => raw4289 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4289step0 raw4289; decide +kernel
      have hl : raw4289step0Labels = raw4289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4289 raw4289Labels permutation346 hz
    mixedMoment B raw4289step0 raw4289step0Labels = mixedMoment B raw4289step1 raw4289step1Labels := by
      have ha : raw4289step1 = (fun i j => raw4289step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4289step1 raw4289step0; decide +kernel
      have hl : raw4289step1Labels = raw4289step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4289step0 raw4289step0Labels permutation139 permutation3
    mixedMoment B raw4289step1 raw4289step1Labels = mixedMoment B raw4289step2 raw4289step2Labels := by
      have ha : raw4289step2 = -raw4289step1 := by apply Matrix.ext; change ∀ i j, raw4289step2 i j = -(raw4289step1 i j); unfold raw4289step2 raw4289step1; decide +kernel
      have hl : raw4289step2Labels = raw4289step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4289step2 raw4289step2Labels = mixedMoment B raw4289step3 raw4289step3Labels := by
      have ha : raw4289step3 = raw4289step2 := by apply Matrix.ext; unfold raw4289step3 raw4289step2; decide +kernel
      have hl : raw4289step2Labels = labelEmbedding6 ∘ raw4289step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4289step2 raw4289step2Labels raw4289step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw4290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4290step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4290step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4290step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4290step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4290step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4290step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4290 raw4290Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw4290 raw4290Labels = mixedMoment B raw4290step0 raw4290step0Labels := by
      have hz : ∀ j, raw4290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4290step0 = (fun i j => raw4290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4290step0 raw4290; decide +kernel
      have hl : raw4290step0Labels = raw4290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4290 raw4290Labels permutation434 hz
    mixedMoment B raw4290step0 raw4290step0Labels = mixedMoment B raw4290step1 raw4290step1Labels := by
      have hz : ∀ j, raw4290step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4290step1 = (fun i j => raw4290step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4290step1 raw4290step0; decide +kernel
      have hl : raw4290step1Labels = raw4290step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4290step0 raw4290step0Labels permutation80 hz
    mixedMoment B raw4290step1 raw4290step1Labels = mixedMoment B raw4290step2 raw4290step2Labels := by
      have ha : raw4290step2 = (fun i j => raw4290step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4290step2 raw4290step1; decide +kernel
      have hl : raw4290step2Labels = raw4290step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4290step1 raw4290step1Labels permutation29 permutation3
    mixedMoment B raw4290step2 raw4290step2Labels = mixedMoment B raw4290step3 raw4290step3Labels := by
      have ha : raw4290step3 = -raw4290step2 := by apply Matrix.ext; change ∀ i j, raw4290step3 i j = -(raw4290step2 i j); unfold raw4290step3 raw4290step2; decide +kernel
      have hl : raw4290step3Labels = raw4290step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4290step3 raw4290step3Labels = mixedMoment B raw4290step4 raw4290step4Labels := by
      have ha : raw4290step4 = raw4290step3 := by apply Matrix.ext; unfold raw4290step4 raw4290step3; decide +kernel
      have hl : raw4290step3Labels = labelEmbedding6 ∘ raw4290step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4290step3 raw4290step3Labels raw4290step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw4291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4291step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4291step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4291 raw4291Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw4291 raw4291Labels = mixedMoment B raw4291step0 raw4291step0Labels := by
      have hz : ∀ j, raw4291 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4291step0 = (fun i j => raw4291 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4291step0 raw4291; decide +kernel
      have hl : raw4291step0Labels = raw4291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4291 raw4291Labels permutation434 hz
    mixedMoment B raw4291step0 raw4291step0Labels = mixedMoment B raw4291step1 raw4291step1Labels := by
      have hz : ∀ j, raw4291step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4291step1 = (fun i j => raw4291step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4291step1 raw4291step0; decide +kernel
      have hl : raw4291step1Labels = raw4291step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4291step0 raw4291step0Labels permutation80 hz
    mixedMoment B raw4291step1 raw4291step1Labels = mixedMoment B raw4291step2 raw4291step2Labels := by
      have ha : raw4291step2 = (fun i j => raw4291step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4291step2 raw4291step1; decide +kernel
      have hl : raw4291step2Labels = raw4291step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4291step1 raw4291step1Labels permutation10 permutation2
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw4292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4292step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4292step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4292step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4292step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4292 raw4292Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw4292 raw4292Labels = mixedMoment B raw4292step0 raw4292step0Labels := by
      have hz : ∀ j, raw4292 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4292step0 = (fun i j => raw4292 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4292step0 raw4292; decide +kernel
      have hl : raw4292step0Labels = raw4292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4292 raw4292Labels permutation434 hz
    mixedMoment B raw4292step0 raw4292step0Labels = mixedMoment B raw4292step1 raw4292step1Labels := by
      have hz : ∀ j, raw4292step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4292step1 = (fun i j => raw4292step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4292step1 raw4292step0; decide +kernel
      have hl : raw4292step1Labels = raw4292step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4292step0 raw4292step0Labels permutation56 hz
    mixedMoment B raw4292step1 raw4292step1Labels = mixedMoment B raw4292step2 raw4292step2Labels := by
      have ha : raw4292step2 = (fun i j => raw4292step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4292step2 raw4292step1; decide +kernel
      have hl : raw4292step2Labels = raw4292step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4292step1 raw4292step1Labels permutation10 permutation3
    mixedMoment B raw4292step2 raw4292step2Labels = mixedMoment B raw4292step3 raw4292step3Labels := by
      have ha : raw4292step3 = raw4292step2 := by apply Matrix.ext; unfold raw4292step3 raw4292step2; decide +kernel
      have hl : raw4292step2Labels = labelEmbedding6 ∘ raw4292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4292step2 raw4292step2Labels raw4292step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw4293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4293step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4293step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4293step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4293 raw4293Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw4293 raw4293Labels = mixedMoment B raw4293step0 raw4293step0Labels := by
      have hz : ∀ j, raw4293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4293step0 = (fun i j => raw4293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4293step0 raw4293; decide +kernel
      have hl : raw4293step0Labels = raw4293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4293 raw4293Labels permutation434 hz
    mixedMoment B raw4293step0 raw4293step0Labels = mixedMoment B raw4293step1 raw4293step1Labels := by
      have ha : raw4293step1 = (fun i j => raw4293step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4293step1 raw4293step0; decide +kernel
      have hl : raw4293step1Labels = raw4293step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4293step0 raw4293step0Labels permutation145 permutation3
    mixedMoment B raw4293step1 raw4293step1Labels = mixedMoment B raw4293step2 raw4293step2Labels := by
      have ha : raw4293step2 = -raw4293step1 := by apply Matrix.ext; change ∀ i j, raw4293step2 i j = -(raw4293step1 i j); unfold raw4293step2 raw4293step1; decide +kernel
      have hl : raw4293step2Labels = raw4293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4293step2 raw4293step2Labels = mixedMoment B raw4293step3 raw4293step3Labels := by
      have ha : raw4293step3 = raw4293step2 := by apply Matrix.ext; unfold raw4293step3 raw4293step2; decide +kernel
      have hl : raw4293step2Labels = labelEmbedding6 ∘ raw4293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4293step2 raw4293step2Labels raw4293step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw4294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4294step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4294step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4294step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4294step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4294 raw4294Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw4294 raw4294Labels = mixedMoment B raw4294step0 raw4294step0Labels := by
      have hz : ∀ j, raw4294 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4294step0 = (fun i j => raw4294 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4294step0 raw4294; decide +kernel
      have hl : raw4294step0Labels = raw4294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4294 raw4294Labels permutation265 hz
    mixedMoment B raw4294step0 raw4294step0Labels = mixedMoment B raw4294step1 raw4294step1Labels := by
      have ha : raw4294step1 = (fun i j => raw4294step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4294step1 raw4294step0; decide +kernel
      have hl : raw4294step1Labels = raw4294step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4294step0 raw4294step0Labels permutation139 permutation3
    mixedMoment B raw4294step1 raw4294step1Labels = mixedMoment B raw4294step2 raw4294step2Labels := by
      have ha : raw4294step2 = -raw4294step1 := by apply Matrix.ext; change ∀ i j, raw4294step2 i j = -(raw4294step1 i j); unfold raw4294step2 raw4294step1; decide +kernel
      have hl : raw4294step2Labels = raw4294step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4294step2 raw4294step2Labels = mixedMoment B raw4294step3 raw4294step3Labels := by
      have ha : raw4294step3 = raw4294step2 := by apply Matrix.ext; unfold raw4294step3 raw4294step2; decide +kernel
      have hl : raw4294step2Labels = labelEmbedding6 ∘ raw4294step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4294step2 raw4294step2Labels raw4294step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw4295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4295step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4295step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4295step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4295step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4295step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4295 raw4295Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw4295 raw4295Labels = mixedMoment B raw4295step0 raw4295step0Labels := by
      have hz : ∀ j, raw4295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4295step0 = (fun i j => raw4295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4295step0 raw4295; decide +kernel
      have hl : raw4295step0Labels = raw4295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4295 raw4295Labels permutation434 hz
    mixedMoment B raw4295step0 raw4295step0Labels = mixedMoment B raw4295step1 raw4295step1Labels := by
      have hz : ∀ j, raw4295step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4295step1 = (fun i j => raw4295step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4295step1 raw4295step0; decide +kernel
      have hl : raw4295step1Labels = raw4295step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4295step0 raw4295step0Labels permutation56 hz
    mixedMoment B raw4295step1 raw4295step1Labels = mixedMoment B raw4295step2 raw4295step2Labels := by
      have ha : raw4295step2 = (fun i j => raw4295step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4295step2 raw4295step1; decide +kernel
      have hl : raw4295step2Labels = raw4295step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4295step1 raw4295step1Labels permutation29 permutation3
    mixedMoment B raw4295step2 raw4295step2Labels = mixedMoment B raw4295step3 raw4295step3Labels := by
      have ha : raw4295step3 = -raw4295step2 := by apply Matrix.ext; change ∀ i j, raw4295step3 i j = -(raw4295step2 i j); unfold raw4295step3 raw4295step2; decide +kernel
      have hl : raw4295step3Labels = raw4295step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4295step3 raw4295step3Labels = mixedMoment B raw4295step4 raw4295step4Labels := by
      have ha : raw4295step4 = raw4295step3 := by apply Matrix.ext; unfold raw4295step4 raw4295step3; decide +kernel
      have hl : raw4295step3Labels = labelEmbedding6 ∘ raw4295step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4295step3 raw4295step3Labels raw4295step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw4296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4296step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4296step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4296 raw4296Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw4296 raw4296Labels = mixedMoment B raw4296step0 raw4296step0Labels := by
      have hz : ∀ j, raw4296 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4296step0 = (fun i j => raw4296 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4296step0 raw4296; decide +kernel
      have hl : raw4296step0Labels = raw4296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4296 raw4296Labels permutation434 hz
    mixedMoment B raw4296step0 raw4296step0Labels = mixedMoment B raw4296step1 raw4296step1Labels := by
      have hz : ∀ j, raw4296step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4296step1 = (fun i j => raw4296step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4296step1 raw4296step0; decide +kernel
      have hl : raw4296step1Labels = raw4296step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4296step0 raw4296step0Labels permutation56 hz
    mixedMoment B raw4296step1 raw4296step1Labels = mixedMoment B raw4296step2 raw4296step2Labels := by
      have ha : raw4296step2 = (fun i j => raw4296step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4296step2 raw4296step1; decide +kernel
      have hl : raw4296step2Labels = raw4296step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4296step1 raw4296step1Labels permutation10 permutation2
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw4297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4297step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4297step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4297 raw4297Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw4297 raw4297Labels = mixedMoment B raw4297step0 raw4297step0Labels := by
      have hz : ∀ j, raw4297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4297step0 = (fun i j => raw4297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4297step0 raw4297; decide +kernel
      have hl : raw4297step0Labels = raw4297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4297 raw4297Labels permutation346 hz
    mixedMoment B raw4297step0 raw4297step0Labels = mixedMoment B raw4297step1 raw4297step1Labels := by
      have hz : ∀ j, raw4297step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4297step1 = (fun i j => raw4297step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4297step1 raw4297step0; decide +kernel
      have hl : raw4297step1Labels = raw4297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4297step0 raw4297step0Labels permutation56 hz
    mixedMoment B raw4297step1 raw4297step1Labels = mixedMoment B raw4297step2 raw4297step2Labels := by
      have ha : raw4297step2 = (fun i j => raw4297step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4297step2 raw4297step1; decide +kernel
      have hl : raw4297step2Labels = raw4297step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4297step1 raw4297step1Labels permutation10 permutation3
    mixedMoment B raw4297step2 raw4297step2Labels = mixedMoment B raw4297step3 raw4297step3Labels := by
      have ha : raw4297step3 = raw4297step2 := by apply Matrix.ext; unfold raw4297step3 raw4297step2; decide +kernel
      have hl : raw4297step2Labels = labelEmbedding6 ∘ raw4297step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4297step2 raw4297step2Labels raw4297step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw4298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4298step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4298step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4298step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4298step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4298 raw4298Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw4298 raw4298Labels = mixedMoment B raw4298step0 raw4298step0Labels := by
      have hz : ∀ j, raw4298 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4298step0 = (fun i j => raw4298 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4298step0 raw4298; decide +kernel
      have hl : raw4298step0Labels = raw4298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4298 raw4298Labels permutation346 hz
    mixedMoment B raw4298step0 raw4298step0Labels = mixedMoment B raw4298step1 raw4298step1Labels := by
      have ha : raw4298step1 = (fun i j => raw4298step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4298step1 raw4298step0; decide +kernel
      have hl : raw4298step1Labels = raw4298step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4298step0 raw4298step0Labels permutation145 permutation3
    mixedMoment B raw4298step1 raw4298step1Labels = mixedMoment B raw4298step2 raw4298step2Labels := by
      have ha : raw4298step2 = -raw4298step1 := by apply Matrix.ext; change ∀ i j, raw4298step2 i j = -(raw4298step1 i j); unfold raw4298step2 raw4298step1; decide +kernel
      have hl : raw4298step2Labels = raw4298step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4298step2 raw4298step2Labels = mixedMoment B raw4298step3 raw4298step3Labels := by
      have ha : raw4298step3 = raw4298step2 := by apply Matrix.ext; unfold raw4298step3 raw4298step2; decide +kernel
      have hl : raw4298step2Labels = labelEmbedding6 ∘ raw4298step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4298step2 raw4298step2Labels raw4298step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw4299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4299step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4299step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4299step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4299step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4299step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4299 raw4299Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw4299 raw4299Labels = mixedMoment B raw4299step0 raw4299step0Labels := by
      have hz : ∀ j, raw4299 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4299step0 = (fun i j => raw4299 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4299step0 raw4299; decide +kernel
      have hl : raw4299step0Labels = raw4299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4299 raw4299Labels permutation265 hz
    mixedMoment B raw4299step0 raw4299step0Labels = mixedMoment B raw4299step1 raw4299step1Labels := by
      have ha : raw4299step1 = (fun i j => raw4299step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4299step1 raw4299step0; decide +kernel
      have hl : raw4299step1Labels = raw4299step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4299step0 raw4299step0Labels permutation145 permutation3
    mixedMoment B raw4299step1 raw4299step1Labels = mixedMoment B raw4299step2 raw4299step2Labels := by
      have ha : raw4299step2 = -raw4299step1 := by apply Matrix.ext; change ∀ i j, raw4299step2 i j = -(raw4299step1 i j); unfold raw4299step2 raw4299step1; decide +kernel
      have hl : raw4299step2Labels = raw4299step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4299step2 raw4299step2Labels = mixedMoment B raw4299step3 raw4299step3Labels := by
      have ha : raw4299step3 = raw4299step2 := by apply Matrix.ext; unfold raw4299step3 raw4299step2; decide +kernel
      have hl : raw4299step2Labels = labelEmbedding6 ∘ raw4299step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4299step2 raw4299step2Labels raw4299step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw4300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4300step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4300step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4300step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4300step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4300step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4300step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4300 raw4300Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw4300 raw4300Labels = mixedMoment B raw4300step0 raw4300step0Labels := by
      have hz : ∀ j, raw4300 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4300step0 = (fun i j => raw4300 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4300step0 raw4300; decide +kernel
      have hl : raw4300step0Labels = raw4300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4300 raw4300Labels permutation346 hz
    mixedMoment B raw4300step0 raw4300step0Labels = mixedMoment B raw4300step1 raw4300step1Labels := by
      have hz : ∀ j, raw4300step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4300step1 = (fun i j => raw4300step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4300step1 raw4300step0; decide +kernel
      have hl : raw4300step1Labels = raw4300step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4300step0 raw4300step0Labels permutation56 hz
    mixedMoment B raw4300step1 raw4300step1Labels = mixedMoment B raw4300step2 raw4300step2Labels := by
      have ha : raw4300step2 = (fun i j => raw4300step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4300step2 raw4300step1; decide +kernel
      have hl : raw4300step2Labels = raw4300step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4300step1 raw4300step1Labels permutation29 permutation3
    mixedMoment B raw4300step2 raw4300step2Labels = mixedMoment B raw4300step3 raw4300step3Labels := by
      have ha : raw4300step3 = -raw4300step2 := by apply Matrix.ext; change ∀ i j, raw4300step3 i j = -(raw4300step2 i j); unfold raw4300step3 raw4300step2; decide +kernel
      have hl : raw4300step3Labels = raw4300step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4300step3 raw4300step3Labels = mixedMoment B raw4300step4 raw4300step4Labels := by
      have ha : raw4300step4 = raw4300step3 := by apply Matrix.ext; unfold raw4300step4 raw4300step3; decide +kernel
      have hl : raw4300step3Labels = labelEmbedding6 ∘ raw4300step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4300step3 raw4300step3Labels raw4300step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw4301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4301step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4301 raw4301Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw4301 raw4301Labels = mixedMoment B raw4301step0 raw4301step0Labels := by
      have hz : ∀ j, raw4301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4301step0 = (fun i j => raw4301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4301step0 raw4301; decide +kernel
      have hl : raw4301step0Labels = raw4301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4301 raw4301Labels permutation346 hz
    mixedMoment B raw4301step0 raw4301step0Labels = mixedMoment B raw4301step1 raw4301step1Labels := by
      have hz : ∀ j, raw4301step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4301step1 = (fun i j => raw4301step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4301step1 raw4301step0; decide +kernel
      have hl : raw4301step1Labels = raw4301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4301step0 raw4301step0Labels permutation56 hz
    mixedMoment B raw4301step1 raw4301step1Labels = mixedMoment B raw4301step2 raw4301step2Labels := by
      have ha : raw4301step2 = (fun i j => raw4301step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4301step2 raw4301step1; decide +kernel
      have hl : raw4301step2Labels = raw4301step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4301step1 raw4301step1Labels permutation10 permutation2
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw4302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4302step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw4302step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4302step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw4302step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4302step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw4302step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4302 raw4302Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw4302 raw4302Labels = mixedMoment B raw4302step0 raw4302step0Labels := by
      have hz : ∀ j, raw4302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4302step0 = (fun i j => raw4302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4302step0 raw4302; decide +kernel
      have hl : raw4302step0Labels = raw4302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4302 raw4302Labels permutation434 hz
    mixedMoment B raw4302step0 raw4302step0Labels = mixedMoment B raw4302step1 raw4302step1Labels := by
      have hz : ∀ j, raw4302step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4302step1 = (fun i j => raw4302step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4302step1 raw4302step0; decide +kernel
      have hl : raw4302step1Labels = raw4302step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4302step0 raw4302step0Labels permutation80 hz
    mixedMoment B raw4302step1 raw4302step1Labels = mixedMoment B raw4302step2 raw4302step2Labels := by
      have hz : ∀ j, raw4302step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4302step2 = (fun i j => raw4302step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4302step2 raw4302step1; decide +kernel
      have hl : raw4302step2Labels = raw4302step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4302step1 raw4302step1Labels permutation14 hz
    mixedMoment B raw4302step2 raw4302step2Labels = mixedMoment B raw4302step3 raw4302step3Labels := by
      have ha : raw4302step3 = (fun i j => raw4302step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4302step3 raw4302step2; decide +kernel
      have hl : raw4302step3Labels = raw4302step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4302step2 raw4302step2Labels permutation2 permutation3
    mixedMoment B raw4302step3 raw4302step3Labels = mixedMoment B raw4302step4 raw4302step4Labels := by
      have ha : raw4302step4 = raw4302step3 := by apply Matrix.ext; unfold raw4302step4 raw4302step3; decide +kernel
      have hl : raw4302step3Labels = labelEmbedding6 ∘ raw4302step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4302step3 raw4302step3Labels raw4302step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw4303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4303step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4303 raw4303Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw4303 raw4303Labels = mixedMoment B raw4303step0 raw4303step0Labels := by
      have hz : ∀ j, raw4303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4303step0 = (fun i j => raw4303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4303step0 raw4303; decide +kernel
      have hl : raw4303step0Labels = raw4303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4303 raw4303Labels permutation434 hz
    mixedMoment B raw4303step0 raw4303step0Labels = mixedMoment B raw4303step1 raw4303step1Labels := by
      have hz : ∀ j, raw4303step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4303step1 = (fun i j => raw4303step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4303step1 raw4303step0; decide +kernel
      have hl : raw4303step1Labels = raw4303step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4303step0 raw4303step0Labels permutation80 hz
    _ = mixedMoment B node5174 node5174Labels := by rfl

def raw4304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4304 raw4304Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw4304 raw4304Labels = mixedMoment B raw4304step0 raw4304step0Labels := by
      have hz : ∀ j, raw4304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4304step0 = (fun i j => raw4304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4304step0 raw4304; decide +kernel
      have hl : raw4304step0Labels = raw4304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4304 raw4304Labels permutation434 hz
    mixedMoment B raw4304step0 raw4304step0Labels = mixedMoment B raw4304step1 raw4304step1Labels := by
      have hz : ∀ j, raw4304step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4304step1 = (fun i j => raw4304step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4304step1 raw4304step0; decide +kernel
      have hl : raw4304step1Labels = raw4304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4304step0 raw4304step0Labels permutation56 hz
    _ = mixedMoment B node5174 node5174Labels := by rfl

def raw4305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4305 raw4305Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw4305 raw4305Labels = mixedMoment B raw4305step0 raw4305step0Labels := by
      have hz : ∀ j, raw4305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4305step0 = (fun i j => raw4305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4305step0 raw4305; decide +kernel
      have hl : raw4305step0Labels = raw4305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4305 raw4305Labels permutation346 hz
    mixedMoment B raw4305step0 raw4305step0Labels = mixedMoment B raw4305step1 raw4305step1Labels := by
      have hz : ∀ j, raw4305step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4305step1 = (fun i j => raw4305step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4305step1 raw4305step0; decide +kernel
      have hl : raw4305step1Labels = raw4305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4305step0 raw4305step0Labels permutation56 hz
    _ = mixedMoment B node5174 node5174Labels := by rfl

def raw4306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw4306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw4306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw4306step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4306step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw4306step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4306 raw4306Labels = mixedMoment B node5309 node5309Labels := by
  calc
    mixedMoment B raw4306 raw4306Labels = mixedMoment B raw4306step0 raw4306step0Labels := by
      have hz : ∀ j, raw4306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4306step0 = (fun i j => raw4306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4306step0 raw4306; decide +kernel
      have hl : raw4306step0Labels = raw4306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4306 raw4306Labels permutation434 hz
    mixedMoment B raw4306step0 raw4306step0Labels = mixedMoment B raw4306step1 raw4306step1Labels := by
      have hz : ∀ j, raw4306step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4306step1 = (fun i j => raw4306step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4306step1 raw4306step0; decide +kernel
      have hl : raw4306step1Labels = raw4306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4306step0 raw4306step0Labels permutation80 hz
    mixedMoment B raw4306step1 raw4306step1Labels = mixedMoment B raw4306step2 raw4306step2Labels := by
      have hz : ∀ j, raw4306step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4306step2 = (fun i j => raw4306step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4306step2 raw4306step1; decide +kernel
      have hl : raw4306step2Labels = raw4306step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4306step1 raw4306step1Labels permutation14 hz
    _ = mixedMoment B node5309 node5309Labels := by rfl

def raw4307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4307step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw4307step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4307step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw4307step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4307step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw4307step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4307step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw4307step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4307 raw4307Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw4307 raw4307Labels = mixedMoment B raw4307step0 raw4307step0Labels := by
      have hz : ∀ j, raw4307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4307step0 = (fun i j => raw4307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4307step0 raw4307; decide +kernel
      have hl : raw4307step0Labels = raw4307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4307 raw4307Labels permutation434 hz
    mixedMoment B raw4307step0 raw4307step0Labels = mixedMoment B raw4307step1 raw4307step1Labels := by
      have hz : ∀ j, raw4307step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4307step1 = (fun i j => raw4307step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4307step1 raw4307step0; decide +kernel
      have hl : raw4307step1Labels = raw4307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4307step0 raw4307step0Labels permutation80 hz
    mixedMoment B raw4307step1 raw4307step1Labels = mixedMoment B raw4307step2 raw4307step2Labels := by
      have hz : ∀ j, raw4307step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4307step2 = (fun i j => raw4307step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4307step2 raw4307step1; decide +kernel
      have hl : raw4307step2Labels = raw4307step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4307step1 raw4307step1Labels permutation14 hz
    mixedMoment B raw4307step2 raw4307step2Labels = mixedMoment B raw4307step3 raw4307step3Labels := by
      have ha : raw4307step3 = (fun i j => raw4307step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4307step3 raw4307step2; decide +kernel
      have hl : raw4307step3Labels = raw4307step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4307step2 raw4307step2Labels permutation7 permutation3
    mixedMoment B raw4307step3 raw4307step3Labels = mixedMoment B raw4307step4 raw4307step4Labels := by
      have ha : raw4307step4 = -raw4307step3 := by apply Matrix.ext; change ∀ i j, raw4307step4 i j = -(raw4307step3 i j); unfold raw4307step4 raw4307step3; decide +kernel
      have hl : raw4307step4Labels = raw4307step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4307step4 raw4307step4Labels = mixedMoment B raw4307step5 raw4307step5Labels := by
      have ha : raw4307step5 = raw4307step4 := by apply Matrix.ext; unfold raw4307step5 raw4307step4; decide +kernel
      have hl : raw4307step4Labels = labelEmbedding6 ∘ raw4307step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4307step4 raw4307step4Labels raw4307step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw4308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4308step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4308step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4308step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4308step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4308step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4308 raw4308Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw4308 raw4308Labels = mixedMoment B raw4308step0 raw4308step0Labels := by
      have hz : ∀ j, raw4308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4308step0 = (fun i j => raw4308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4308step0 raw4308; decide +kernel
      have hl : raw4308step0Labels = raw4308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4308 raw4308Labels permutation434 hz
    mixedMoment B raw4308step0 raw4308step0Labels = mixedMoment B raw4308step1 raw4308step1Labels := by
      have hz : ∀ j, raw4308step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4308step1 = (fun i j => raw4308step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4308step1 raw4308step0; decide +kernel
      have hl : raw4308step1Labels = raw4308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4308step0 raw4308step0Labels permutation80 hz
    mixedMoment B raw4308step1 raw4308step1Labels = mixedMoment B raw4308step2 raw4308step2Labels := by
      have ha : raw4308step2 = (fun i j => raw4308step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4308step2 raw4308step1; decide +kernel
      have hl : raw4308step2Labels = raw4308step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4308step1 raw4308step1Labels permutation31 permutation3
    mixedMoment B raw4308step2 raw4308step2Labels = mixedMoment B raw4308step3 raw4308step3Labels := by
      have ha : raw4308step3 = -raw4308step2 := by apply Matrix.ext; change ∀ i j, raw4308step3 i j = -(raw4308step2 i j); unfold raw4308step3 raw4308step2; decide +kernel
      have hl : raw4308step3Labels = raw4308step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4308step3 raw4308step3Labels = mixedMoment B raw4308step4 raw4308step4Labels := by
      have ha : raw4308step4 = raw4308step3 := by apply Matrix.ext; unfold raw4308step4 raw4308step3; decide +kernel
      have hl : raw4308step3Labels = labelEmbedding6 ∘ raw4308step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4308step3 raw4308step3Labels raw4308step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw4309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4309step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4309step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4309step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4309step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4309step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4309step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4309 raw4309Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw4309 raw4309Labels = mixedMoment B raw4309step0 raw4309step0Labels := by
      have hz : ∀ j, raw4309 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4309step0 = (fun i j => raw4309 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4309step0 raw4309; decide +kernel
      have hl : raw4309step0Labels = raw4309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4309 raw4309Labels permutation434 hz
    mixedMoment B raw4309step0 raw4309step0Labels = mixedMoment B raw4309step1 raw4309step1Labels := by
      have hz : ∀ j, raw4309step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4309step1 = (fun i j => raw4309step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4309step1 raw4309step0; decide +kernel
      have hl : raw4309step1Labels = raw4309step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4309step0 raw4309step0Labels permutation56 hz
    mixedMoment B raw4309step1 raw4309step1Labels = mixedMoment B raw4309step2 raw4309step2Labels := by
      have ha : raw4309step2 = (fun i j => raw4309step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4309step2 raw4309step1; decide +kernel
      have hl : raw4309step2Labels = raw4309step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4309step1 raw4309step1Labels permutation31 permutation3
    mixedMoment B raw4309step2 raw4309step2Labels = mixedMoment B raw4309step3 raw4309step3Labels := by
      have ha : raw4309step3 = -raw4309step2 := by apply Matrix.ext; change ∀ i j, raw4309step3 i j = -(raw4309step2 i j); unfold raw4309step3 raw4309step2; decide +kernel
      have hl : raw4309step3Labels = raw4309step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4309step3 raw4309step3Labels = mixedMoment B raw4309step4 raw4309step4Labels := by
      have ha : raw4309step4 = raw4309step3 := by apply Matrix.ext; unfold raw4309step4 raw4309step3; decide +kernel
      have hl : raw4309step3Labels = labelEmbedding6 ∘ raw4309step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4309step3 raw4309step3Labels raw4309step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw4310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4310step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4310step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4310step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4310step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4310step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4310step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4310 raw4310Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw4310 raw4310Labels = mixedMoment B raw4310step0 raw4310step0Labels := by
      have hz : ∀ j, raw4310 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4310step0 = (fun i j => raw4310 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4310step0 raw4310; decide +kernel
      have hl : raw4310step0Labels = raw4310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4310 raw4310Labels permutation346 hz
    mixedMoment B raw4310step0 raw4310step0Labels = mixedMoment B raw4310step1 raw4310step1Labels := by
      have hz : ∀ j, raw4310step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4310step1 = (fun i j => raw4310step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4310step1 raw4310step0; decide +kernel
      have hl : raw4310step1Labels = raw4310step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4310step0 raw4310step0Labels permutation56 hz
    mixedMoment B raw4310step1 raw4310step1Labels = mixedMoment B raw4310step2 raw4310step2Labels := by
      have ha : raw4310step2 = (fun i j => raw4310step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4310step2 raw4310step1; decide +kernel
      have hl : raw4310step2Labels = raw4310step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4310step1 raw4310step1Labels permutation31 permutation3
    mixedMoment B raw4310step2 raw4310step2Labels = mixedMoment B raw4310step3 raw4310step3Labels := by
      have ha : raw4310step3 = -raw4310step2 := by apply Matrix.ext; change ∀ i j, raw4310step3 i j = -(raw4310step2 i j); unfold raw4310step3 raw4310step2; decide +kernel
      have hl : raw4310step3Labels = raw4310step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4310step3 raw4310step3Labels = mixedMoment B raw4310step4 raw4310step4Labels := by
      have ha : raw4310step4 = raw4310step3 := by apply Matrix.ext; unfold raw4310step4 raw4310step3; decide +kernel
      have hl : raw4310step3Labels = labelEmbedding6 ∘ raw4310step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4310step3 raw4310step3Labels raw4310step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw4311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4311step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4311step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4311step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![4, -3, -1]]
def raw4311step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4311step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw4311step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4311step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw4311step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4311step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw4311step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4311 raw4311Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw4311 raw4311Labels = mixedMoment B raw4311step0 raw4311step0Labels := by
      have hz : ∀ j, raw4311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4311step0 = (fun i j => raw4311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4311step0 raw4311; decide +kernel
      have hl : raw4311step0Labels = raw4311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4311 raw4311Labels permutation434 hz
    mixedMoment B raw4311step0 raw4311step0Labels = mixedMoment B raw4311step1 raw4311step1Labels := by
      have hz : ∀ j, raw4311step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4311step1 = (fun i j => raw4311step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4311step1 raw4311step0; decide +kernel
      have hl : raw4311step1Labels = raw4311step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4311step0 raw4311step0Labels permutation80 hz
    mixedMoment B raw4311step1 raw4311step1Labels = mixedMoment B raw4311step2 raw4311step2Labels := by
      have hz : ∀ j, raw4311step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4311step2 = (fun i j => raw4311step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4311step2 raw4311step1; decide +kernel
      have hl : raw4311step2Labels = raw4311step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4311step1 raw4311step1Labels permutation14 hz
    mixedMoment B raw4311step2 raw4311step2Labels = mixedMoment B raw4311step3 raw4311step3Labels := by
      have ha : raw4311step3 = (fun i j => raw4311step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4311step3 raw4311step2; decide +kernel
      have hl : raw4311step3Labels = raw4311step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4311step2 raw4311step2Labels permutation7 permutation3
    mixedMoment B raw4311step3 raw4311step3Labels = mixedMoment B raw4311step4 raw4311step4Labels := by
      have ha : raw4311step4 = -raw4311step3 := by apply Matrix.ext; change ∀ i j, raw4311step4 i j = -(raw4311step3 i j); unfold raw4311step4 raw4311step3; decide +kernel
      have hl : raw4311step4Labels = raw4311step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4311step4 raw4311step4Labels = mixedMoment B raw4311step5 raw4311step5Labels := by
      have ha : raw4311step5 = raw4311step4 := by apply Matrix.ext; unfold raw4311step5 raw4311step4; decide +kernel
      have hl : raw4311step4Labels = labelEmbedding6 ∘ raw4311step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4311step4 raw4311step4Labels raw4311step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4507 node4507Labels := by rfl

def raw4312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4312step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4312step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4312step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4312step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4312 raw4312Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw4312 raw4312Labels = mixedMoment B raw4312step0 raw4312step0Labels := by
      have hz : ∀ j, raw4312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4312step0 = (fun i j => raw4312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4312step0 raw4312; decide +kernel
      have hl : raw4312step0Labels = raw4312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4312 raw4312Labels permutation434 hz
    mixedMoment B raw4312step0 raw4312step0Labels = mixedMoment B raw4312step1 raw4312step1Labels := by
      have hz : ∀ j, raw4312step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4312step1 = (fun i j => raw4312step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4312step1 raw4312step0; decide +kernel
      have hl : raw4312step1Labels = raw4312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4312step0 raw4312step0Labels permutation80 hz
    mixedMoment B raw4312step1 raw4312step1Labels = mixedMoment B raw4312step2 raw4312step2Labels := by
      have ha : raw4312step2 = (fun i j => raw4312step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4312step2 raw4312step1; decide +kernel
      have hl : raw4312step2Labels = raw4312step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4312step1 raw4312step1Labels permutation31 permutation3
    mixedMoment B raw4312step2 raw4312step2Labels = mixedMoment B raw4312step3 raw4312step3Labels := by
      have ha : raw4312step3 = -raw4312step2 := by apply Matrix.ext; change ∀ i j, raw4312step3 i j = -(raw4312step2 i j); unfold raw4312step3 raw4312step2; decide +kernel
      have hl : raw4312step3Labels = raw4312step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw4313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4313step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4313step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4313step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4313step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4313 raw4313Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw4313 raw4313Labels = mixedMoment B raw4313step0 raw4313step0Labels := by
      have hz : ∀ j, raw4313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4313step0 = (fun i j => raw4313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4313step0 raw4313; decide +kernel
      have hl : raw4313step0Labels = raw4313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4313 raw4313Labels permutation434 hz
    mixedMoment B raw4313step0 raw4313step0Labels = mixedMoment B raw4313step1 raw4313step1Labels := by
      have hz : ∀ j, raw4313step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4313step1 = (fun i j => raw4313step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4313step1 raw4313step0; decide +kernel
      have hl : raw4313step1Labels = raw4313step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4313step0 raw4313step0Labels permutation56 hz
    mixedMoment B raw4313step1 raw4313step1Labels = mixedMoment B raw4313step2 raw4313step2Labels := by
      have ha : raw4313step2 = (fun i j => raw4313step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4313step2 raw4313step1; decide +kernel
      have hl : raw4313step2Labels = raw4313step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4313step1 raw4313step1Labels permutation31 permutation3
    mixedMoment B raw4313step2 raw4313step2Labels = mixedMoment B raw4313step3 raw4313step3Labels := by
      have ha : raw4313step3 = -raw4313step2 := by apply Matrix.ext; change ∀ i j, raw4313step3 i j = -(raw4313step2 i j); unfold raw4313step3 raw4313step2; decide +kernel
      have hl : raw4313step3Labels = raw4313step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw4314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4314Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4314step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4314step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4314step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4314step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4314step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4314 raw4314Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw4314 raw4314Labels = mixedMoment B raw4314step0 raw4314step0Labels := by
      have hz : ∀ j, raw4314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4314step0 = (fun i j => raw4314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4314step0 raw4314; decide +kernel
      have hl : raw4314step0Labels = raw4314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4314 raw4314Labels permutation346 hz
    mixedMoment B raw4314step0 raw4314step0Labels = mixedMoment B raw4314step1 raw4314step1Labels := by
      have hz : ∀ j, raw4314step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4314step1 = (fun i j => raw4314step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4314step1 raw4314step0; decide +kernel
      have hl : raw4314step1Labels = raw4314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4314step0 raw4314step0Labels permutation56 hz
    mixedMoment B raw4314step1 raw4314step1Labels = mixedMoment B raw4314step2 raw4314step2Labels := by
      have ha : raw4314step2 = (fun i j => raw4314step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4314step2 raw4314step1; decide +kernel
      have hl : raw4314step2Labels = raw4314step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4314step1 raw4314step1Labels permutation31 permutation3
    mixedMoment B raw4314step2 raw4314step2Labels = mixedMoment B raw4314step3 raw4314step3Labels := by
      have ha : raw4314step3 = -raw4314step2 := by apply Matrix.ext; change ∀ i j, raw4314step3 i j = -(raw4314step2 i j); unfold raw4314step3 raw4314step2; decide +kernel
      have hl : raw4314step3Labels = raw4314step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw4315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4315step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4315step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![3, -2, -1]]
def raw4315step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4315step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw4315step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4315step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4315step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4315 raw4315Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw4315 raw4315Labels = mixedMoment B raw4315step0 raw4315step0Labels := by
      have hz : ∀ j, raw4315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4315step0 = (fun i j => raw4315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4315step0 raw4315; decide +kernel
      have hl : raw4315step0Labels = raw4315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4315 raw4315Labels permutation434 hz
    mixedMoment B raw4315step0 raw4315step0Labels = mixedMoment B raw4315step1 raw4315step1Labels := by
      have hz : ∀ j, raw4315step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4315step1 = (fun i j => raw4315step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4315step1 raw4315step0; decide +kernel
      have hl : raw4315step1Labels = raw4315step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4315step0 raw4315step0Labels permutation80 hz
    mixedMoment B raw4315step1 raw4315step1Labels = mixedMoment B raw4315step2 raw4315step2Labels := by
      have hz : ∀ j, raw4315step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4315step2 = (fun i j => raw4315step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4315step2 raw4315step1; decide +kernel
      have hl : raw4315step2Labels = raw4315step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4315step1 raw4315step1Labels permutation14 hz
    mixedMoment B raw4315step2 raw4315step2Labels = mixedMoment B raw4315step3 raw4315step3Labels := by
      have ha : raw4315step3 = (fun i j => raw4315step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4315step3 raw4315step2; decide +kernel
      have hl : raw4315step3Labels = raw4315step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4315step2 raw4315step2Labels permutation7 permutation3
    mixedMoment B raw4315step3 raw4315step3Labels = mixedMoment B raw4315step4 raw4315step4Labels := by
      have ha : raw4315step4 = -raw4315step3 := by apply Matrix.ext; change ∀ i j, raw4315step4 i j = -(raw4315step3 i j); unfold raw4315step4 raw4315step3; decide +kernel
      have hl : raw4315step4Labels = raw4315step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2788 node2788Labels := by rfl

def raw4316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4316step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4316step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4316step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw4316step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4316step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-2, 2, 0]]
def raw4316step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4316step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw4316step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4316 raw4316Labels = mixedMoment B node4019 node4019Labels := by
  calc
    mixedMoment B raw4316 raw4316Labels = mixedMoment B raw4316step0 raw4316step0Labels := by
      have hz : ∀ j, raw4316 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4316step0 = (fun i j => raw4316 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4316step0 raw4316; decide +kernel
      have hl : raw4316step0Labels = raw4316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4316 raw4316Labels permutation434 hz
    mixedMoment B raw4316step0 raw4316step0Labels = mixedMoment B raw4316step1 raw4316step1Labels := by
      have hz : ∀ j, raw4316step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4316step1 = (fun i j => raw4316step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4316step1 raw4316step0; decide +kernel
      have hl : raw4316step1Labels = raw4316step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4316step0 raw4316step0Labels permutation80 hz
    mixedMoment B raw4316step1 raw4316step1Labels = mixedMoment B raw4316step2 raw4316step2Labels := by
      have hz : ∀ j, raw4316step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4316step2 = (fun i j => raw4316step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4316step2 raw4316step1; decide +kernel
      have hl : raw4316step2Labels = raw4316step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4316step1 raw4316step1Labels permutation14 hz
    mixedMoment B raw4316step2 raw4316step2Labels = mixedMoment B raw4316step3 raw4316step3Labels := by
      have ha : raw4316step3 = (fun i j => raw4316step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4316step3 raw4316step2; decide +kernel
      have hl : raw4316step3Labels = raw4316step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4316step2 raw4316step2Labels permutation7 permutation3
    mixedMoment B raw4316step3 raw4316step3Labels = mixedMoment B raw4316step4 raw4316step4Labels := by
      have ha : raw4316step4 = -raw4316step3 := by apply Matrix.ext; change ∀ i j, raw4316step4 i j = -(raw4316step3 i j); unfold raw4316step4 raw4316step3; decide +kernel
      have hl : raw4316step4Labels = raw4316step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4019 node4019Labels := by rfl

def raw4317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4317step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4317step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4317step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4317 raw4317Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw4317 raw4317Labels = mixedMoment B raw4317step0 raw4317step0Labels := by
      have hz : ∀ j, raw4317 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4317step0 = (fun i j => raw4317 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4317step0 raw4317; decide +kernel
      have hl : raw4317step0Labels = raw4317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4317 raw4317Labels permutation434 hz
    mixedMoment B raw4317step0 raw4317step0Labels = mixedMoment B raw4317step1 raw4317step1Labels := by
      have hz : ∀ j, raw4317step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4317step1 = (fun i j => raw4317step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4317step1 raw4317step0; decide +kernel
      have hl : raw4317step1Labels = raw4317step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4317step0 raw4317step0Labels permutation80 hz
    mixedMoment B raw4317step1 raw4317step1Labels = mixedMoment B raw4317step2 raw4317step2Labels := by
      have ha : raw4317step2 = (fun i j => raw4317step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4317step2 raw4317step1; decide +kernel
      have hl : raw4317step2Labels = raw4317step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4317step1 raw4317step1Labels permutation10 permutation3
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw4318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4318step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4318 raw4318Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw4318 raw4318Labels = mixedMoment B raw4318step0 raw4318step0Labels := by
      have hz : ∀ j, raw4318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4318step0 = (fun i j => raw4318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4318step0 raw4318; decide +kernel
      have hl : raw4318step0Labels = raw4318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4318 raw4318Labels permutation434 hz
    mixedMoment B raw4318step0 raw4318step0Labels = mixedMoment B raw4318step1 raw4318step1Labels := by
      have ha : raw4318step1 = (fun i j => raw4318step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4318step1 raw4318step0; decide +kernel
      have hl : raw4318step1Labels = raw4318step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4318step0 raw4318step0Labels permutation139 permutation3
    mixedMoment B raw4318step1 raw4318step1Labels = mixedMoment B raw4318step2 raw4318step2Labels := by
      have ha : raw4318step2 = -raw4318step1 := by apply Matrix.ext; change ∀ i j, raw4318step2 i j = -(raw4318step1 i j); unfold raw4318step2 raw4318step1; decide +kernel
      have hl : raw4318step2Labels = raw4318step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw4319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4319 raw4319Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw4319 raw4319Labels = mixedMoment B raw4319step0 raw4319step0Labels := by
      have hz : ∀ j, raw4319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4319step0 = (fun i j => raw4319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4319step0 raw4319; decide +kernel
      have hl : raw4319step0Labels = raw4319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4319 raw4319Labels permutation346 hz
    mixedMoment B raw4319step0 raw4319step0Labels = mixedMoment B raw4319step1 raw4319step1Labels := by
      have ha : raw4319step1 = (fun i j => raw4319step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4319step1 raw4319step0; decide +kernel
      have hl : raw4319step1Labels = raw4319step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4319step0 raw4319step0Labels permutation139 permutation3
    mixedMoment B raw4319step1 raw4319step1Labels = mixedMoment B raw4319step2 raw4319step2Labels := by
      have ha : raw4319step2 = -raw4319step1 := by apply Matrix.ext; change ∀ i j, raw4319step2 i j = -(raw4319step1 i j); unfold raw4319step2 raw4319step1; decide +kernel
      have hl : raw4319step2Labels = raw4319step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw4320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4320step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4320step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4320step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4320step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4320step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4320 raw4320Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw4320 raw4320Labels = mixedMoment B raw4320step0 raw4320step0Labels := by
      have hz : ∀ j, raw4320 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4320step0 = (fun i j => raw4320 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4320step0 raw4320; decide +kernel
      have hl : raw4320step0Labels = raw4320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4320 raw4320Labels permutation434 hz
    mixedMoment B raw4320step0 raw4320step0Labels = mixedMoment B raw4320step1 raw4320step1Labels := by
      have hz : ∀ j, raw4320step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4320step1 = (fun i j => raw4320step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4320step1 raw4320step0; decide +kernel
      have hl : raw4320step1Labels = raw4320step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4320step0 raw4320step0Labels permutation80 hz
    mixedMoment B raw4320step1 raw4320step1Labels = mixedMoment B raw4320step2 raw4320step2Labels := by
      have ha : raw4320step2 = (fun i j => raw4320step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4320step2 raw4320step1; decide +kernel
      have hl : raw4320step2Labels = raw4320step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4320step1 raw4320step1Labels permutation29 permutation3
    mixedMoment B raw4320step2 raw4320step2Labels = mixedMoment B raw4320step3 raw4320step3Labels := by
      have ha : raw4320step3 = -raw4320step2 := by apply Matrix.ext; change ∀ i j, raw4320step3 i j = -(raw4320step2 i j); unfold raw4320step3 raw4320step2; decide +kernel
      have hl : raw4320step3Labels = raw4320step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw4321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4321step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4321step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4321step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw4321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4321 raw4321Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw4321 raw4321Labels = mixedMoment B raw4321step0 raw4321step0Labels := by
      have hz : ∀ j, raw4321 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4321step0 = (fun i j => raw4321 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4321step0 raw4321; decide +kernel
      have hl : raw4321step0Labels = raw4321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4321 raw4321Labels permutation434 hz
    mixedMoment B raw4321step0 raw4321step0Labels = mixedMoment B raw4321step1 raw4321step1Labels := by
      have hz : ∀ j, raw4321step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4321step1 = (fun i j => raw4321step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4321step1 raw4321step0; decide +kernel
      have hl : raw4321step1Labels = raw4321step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4321step0 raw4321step0Labels permutation80 hz
    mixedMoment B raw4321step1 raw4321step1Labels = mixedMoment B raw4321step2 raw4321step2Labels := by
      have ha : raw4321step2 = (fun i j => raw4321step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4321step2 raw4321step1; decide +kernel
      have hl : raw4321step2Labels = raw4321step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4321step1 raw4321step1Labels permutation10 permutation3
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw4322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4322step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4322 raw4322Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw4322 raw4322Labels = mixedMoment B raw4322step0 raw4322step0Labels := by
      have hz : ∀ j, raw4322 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4322step0 = (fun i j => raw4322 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4322step0 raw4322; decide +kernel
      have hl : raw4322step0Labels = raw4322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4322 raw4322Labels permutation434 hz
    mixedMoment B raw4322step0 raw4322step0Labels = mixedMoment B raw4322step1 raw4322step1Labels := by
      have hz : ∀ j, raw4322step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4322step1 = (fun i j => raw4322step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4322step1 raw4322step0; decide +kernel
      have hl : raw4322step1Labels = raw4322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4322step0 raw4322step0Labels permutation56 hz
    mixedMoment B raw4322step1 raw4322step1Labels = mixedMoment B raw4322step2 raw4322step2Labels := by
      have ha : raw4322step2 = (fun i j => raw4322step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4322step2 raw4322step1; decide +kernel
      have hl : raw4322step2Labels = raw4322step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4322step1 raw4322step1Labels permutation10 permutation3
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw4323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4323step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4323 raw4323Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw4323 raw4323Labels = mixedMoment B raw4323step0 raw4323step0Labels := by
      have hz : ∀ j, raw4323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4323step0 = (fun i j => raw4323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4323step0 raw4323; decide +kernel
      have hl : raw4323step0Labels = raw4323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4323 raw4323Labels permutation434 hz
    mixedMoment B raw4323step0 raw4323step0Labels = mixedMoment B raw4323step1 raw4323step1Labels := by
      have ha : raw4323step1 = (fun i j => raw4323step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4323step1 raw4323step0; decide +kernel
      have hl : raw4323step1Labels = raw4323step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4323step0 raw4323step0Labels permutation145 permutation3
    mixedMoment B raw4323step1 raw4323step1Labels = mixedMoment B raw4323step2 raw4323step2Labels := by
      have ha : raw4323step2 = -raw4323step1 := by apply Matrix.ext; change ∀ i j, raw4323step2 i j = -(raw4323step1 i j); unfold raw4323step2 raw4323step1; decide +kernel
      have hl : raw4323step2Labels = raw4323step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw4324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4324step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4324 raw4324Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw4324 raw4324Labels = mixedMoment B raw4324step0 raw4324step0Labels := by
      have hz : ∀ j, raw4324 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4324step0 = (fun i j => raw4324 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4324step0 raw4324; decide +kernel
      have hl : raw4324step0Labels = raw4324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4324 raw4324Labels permutation265 hz
    mixedMoment B raw4324step0 raw4324step0Labels = mixedMoment B raw4324step1 raw4324step1Labels := by
      have ha : raw4324step1 = (fun i j => raw4324step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4324step1 raw4324step0; decide +kernel
      have hl : raw4324step1Labels = raw4324step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4324step0 raw4324step0Labels permutation139 permutation3
    mixedMoment B raw4324step1 raw4324step1Labels = mixedMoment B raw4324step2 raw4324step2Labels := by
      have ha : raw4324step2 = -raw4324step1 := by apply Matrix.ext; change ∀ i j, raw4324step2 i j = -(raw4324step1 i j); unfold raw4324step2 raw4324step1; decide +kernel
      have hl : raw4324step2Labels = raw4324step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw4325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4325step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4325step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4325step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4325step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4325step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4325step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4325 raw4325Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw4325 raw4325Labels = mixedMoment B raw4325step0 raw4325step0Labels := by
      have hz : ∀ j, raw4325 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4325step0 = (fun i j => raw4325 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4325step0 raw4325; decide +kernel
      have hl : raw4325step0Labels = raw4325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4325 raw4325Labels permutation434 hz
    mixedMoment B raw4325step0 raw4325step0Labels = mixedMoment B raw4325step1 raw4325step1Labels := by
      have hz : ∀ j, raw4325step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4325step1 = (fun i j => raw4325step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4325step1 raw4325step0; decide +kernel
      have hl : raw4325step1Labels = raw4325step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4325step0 raw4325step0Labels permutation56 hz
    mixedMoment B raw4325step1 raw4325step1Labels = mixedMoment B raw4325step2 raw4325step2Labels := by
      have ha : raw4325step2 = (fun i j => raw4325step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4325step2 raw4325step1; decide +kernel
      have hl : raw4325step2Labels = raw4325step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4325step1 raw4325step1Labels permutation29 permutation3
    mixedMoment B raw4325step2 raw4325step2Labels = mixedMoment B raw4325step3 raw4325step3Labels := by
      have ha : raw4325step3 = -raw4325step2 := by apply Matrix.ext; change ∀ i j, raw4325step3 i j = -(raw4325step2 i j); unfold raw4325step3 raw4325step2; decide +kernel
      have hl : raw4325step3Labels = raw4325step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw4326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4326step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4326step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw4326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4326 raw4326Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw4326 raw4326Labels = mixedMoment B raw4326step0 raw4326step0Labels := by
      have hz : ∀ j, raw4326 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4326step0 = (fun i j => raw4326 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4326step0 raw4326; decide +kernel
      have hl : raw4326step0Labels = raw4326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4326 raw4326Labels permutation434 hz
    mixedMoment B raw4326step0 raw4326step0Labels = mixedMoment B raw4326step1 raw4326step1Labels := by
      have hz : ∀ j, raw4326step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4326step1 = (fun i j => raw4326step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4326step1 raw4326step0; decide +kernel
      have hl : raw4326step1Labels = raw4326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4326step0 raw4326step0Labels permutation56 hz
    mixedMoment B raw4326step1 raw4326step1Labels = mixedMoment B raw4326step2 raw4326step2Labels := by
      have ha : raw4326step2 = (fun i j => raw4326step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4326step2 raw4326step1; decide +kernel
      have hl : raw4326step2Labels = raw4326step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4326step1 raw4326step1Labels permutation10 permutation3
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw4327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4327step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4327step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4327 raw4327Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw4327 raw4327Labels = mixedMoment B raw4327step0 raw4327step0Labels := by
      have hz : ∀ j, raw4327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4327step0 = (fun i j => raw4327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4327step0 raw4327; decide +kernel
      have hl : raw4327step0Labels = raw4327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4327 raw4327Labels permutation346 hz
    mixedMoment B raw4327step0 raw4327step0Labels = mixedMoment B raw4327step1 raw4327step1Labels := by
      have hz : ∀ j, raw4327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4327step1 = (fun i j => raw4327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4327step1 raw4327step0; decide +kernel
      have hl : raw4327step1Labels = raw4327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4327step0 raw4327step0Labels permutation56 hz
    mixedMoment B raw4327step1 raw4327step1Labels = mixedMoment B raw4327step2 raw4327step2Labels := by
      have ha : raw4327step2 = (fun i j => raw4327step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4327step2 raw4327step1; decide +kernel
      have hl : raw4327step2Labels = raw4327step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4327step1 raw4327step1Labels permutation10 permutation3
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw4328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4328step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4328 raw4328Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw4328 raw4328Labels = mixedMoment B raw4328step0 raw4328step0Labels := by
      have hz : ∀ j, raw4328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4328step0 = (fun i j => raw4328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4328step0 raw4328; decide +kernel
      have hl : raw4328step0Labels = raw4328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4328 raw4328Labels permutation346 hz
    mixedMoment B raw4328step0 raw4328step0Labels = mixedMoment B raw4328step1 raw4328step1Labels := by
      have ha : raw4328step1 = (fun i j => raw4328step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4328step1 raw4328step0; decide +kernel
      have hl : raw4328step1Labels = raw4328step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4328step0 raw4328step0Labels permutation145 permutation3
    mixedMoment B raw4328step1 raw4328step1Labels = mixedMoment B raw4328step2 raw4328step2Labels := by
      have ha : raw4328step2 = -raw4328step1 := by apply Matrix.ext; change ∀ i j, raw4328step2 i j = -(raw4328step1 i j); unfold raw4328step2 raw4328step1; decide +kernel
      have hl : raw4328step2Labels = raw4328step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw4329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4329step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4329 raw4329Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw4329 raw4329Labels = mixedMoment B raw4329step0 raw4329step0Labels := by
      have hz : ∀ j, raw4329 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4329step0 = (fun i j => raw4329 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4329step0 raw4329; decide +kernel
      have hl : raw4329step0Labels = raw4329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4329 raw4329Labels permutation265 hz
    mixedMoment B raw4329step0 raw4329step0Labels = mixedMoment B raw4329step1 raw4329step1Labels := by
      have ha : raw4329step1 = (fun i j => raw4329step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4329step1 raw4329step0; decide +kernel
      have hl : raw4329step1Labels = raw4329step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4329step0 raw4329step0Labels permutation145 permutation3
    mixedMoment B raw4329step1 raw4329step1Labels = mixedMoment B raw4329step2 raw4329step2Labels := by
      have ha : raw4329step2 = -raw4329step1 := by apply Matrix.ext; change ∀ i j, raw4329step2 i j = -(raw4329step1 i j); unfold raw4329step2 raw4329step1; decide +kernel
      have hl : raw4329step2Labels = raw4329step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw4330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4330step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4330step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4330step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4330step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4330 raw4330Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw4330 raw4330Labels = mixedMoment B raw4330step0 raw4330step0Labels := by
      have hz : ∀ j, raw4330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4330step0 = (fun i j => raw4330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4330step0 raw4330; decide +kernel
      have hl : raw4330step0Labels = raw4330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4330 raw4330Labels permutation346 hz
    mixedMoment B raw4330step0 raw4330step0Labels = mixedMoment B raw4330step1 raw4330step1Labels := by
      have hz : ∀ j, raw4330step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4330step1 = (fun i j => raw4330step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4330step1 raw4330step0; decide +kernel
      have hl : raw4330step1Labels = raw4330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4330step0 raw4330step0Labels permutation56 hz
    mixedMoment B raw4330step1 raw4330step1Labels = mixedMoment B raw4330step2 raw4330step2Labels := by
      have ha : raw4330step2 = (fun i j => raw4330step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4330step2 raw4330step1; decide +kernel
      have hl : raw4330step2Labels = raw4330step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4330step1 raw4330step1Labels permutation29 permutation3
    mixedMoment B raw4330step2 raw4330step2Labels = mixedMoment B raw4330step3 raw4330step3Labels := by
      have ha : raw4330step3 = -raw4330step2 := by apply Matrix.ext; change ∀ i j, raw4330step3 i j = -(raw4330step2 i j); unfold raw4330step3 raw4330step2; decide +kernel
      have hl : raw4330step3Labels = raw4330step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw4331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4331step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4331step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4331step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw4331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4331 raw4331Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw4331 raw4331Labels = mixedMoment B raw4331step0 raw4331step0Labels := by
      have hz : ∀ j, raw4331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4331step0 = (fun i j => raw4331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4331step0 raw4331; decide +kernel
      have hl : raw4331step0Labels = raw4331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4331 raw4331Labels permutation346 hz
    mixedMoment B raw4331step0 raw4331step0Labels = mixedMoment B raw4331step1 raw4331step1Labels := by
      have hz : ∀ j, raw4331step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4331step1 = (fun i j => raw4331step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4331step1 raw4331step0; decide +kernel
      have hl : raw4331step1Labels = raw4331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4331step0 raw4331step0Labels permutation56 hz
    mixedMoment B raw4331step1 raw4331step1Labels = mixedMoment B raw4331step2 raw4331step2Labels := by
      have ha : raw4331step2 = (fun i j => raw4331step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4331step2 raw4331step1; decide +kernel
      have hl : raw4331step2Labels = raw4331step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4331step1 raw4331step1Labels permutation10 permutation3
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw4332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4332step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4332step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw4332step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4332step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw4332step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4332 raw4332Labels = mixedMoment B node1304 node1304Labels := by
  calc
    mixedMoment B raw4332 raw4332Labels = mixedMoment B raw4332step0 raw4332step0Labels := by
      have hz : ∀ j, raw4332 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4332step0 = (fun i j => raw4332 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4332step0 raw4332; decide +kernel
      have hl : raw4332step0Labels = raw4332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4332 raw4332Labels permutation434 hz
    mixedMoment B raw4332step0 raw4332step0Labels = mixedMoment B raw4332step1 raw4332step1Labels := by
      have hz : ∀ j, raw4332step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4332step1 = (fun i j => raw4332step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4332step1 raw4332step0; decide +kernel
      have hl : raw4332step1Labels = raw4332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4332step0 raw4332step0Labels permutation80 hz
    mixedMoment B raw4332step1 raw4332step1Labels = mixedMoment B raw4332step2 raw4332step2Labels := by
      have hz : ∀ j, raw4332step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4332step2 = (fun i j => raw4332step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4332step2 raw4332step1; decide +kernel
      have hl : raw4332step2Labels = raw4332step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4332step1 raw4332step1Labels permutation14 hz
    mixedMoment B raw4332step2 raw4332step2Labels = mixedMoment B raw4332step3 raw4332step3Labels := by
      have ha : raw4332step3 = (fun i j => raw4332step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4332step3 raw4332step2; decide +kernel
      have hl : raw4332step3Labels = raw4332step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4332step2 raw4332step2Labels permutation2 permutation3
    _ = mixedMoment B node1304 node1304Labels := by rfl

def raw4333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4333step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4333step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw4333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4333step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4333step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4333 raw4333Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw4333 raw4333Labels = mixedMoment B raw4333step0 raw4333step0Labels := by
      have hz : ∀ j, raw4333 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4333step0 = (fun i j => raw4333 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4333step0 raw4333; decide +kernel
      have hl : raw4333step0Labels = raw4333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4333 raw4333Labels permutation434 hz
    mixedMoment B raw4333step0 raw4333step0Labels = mixedMoment B raw4333step1 raw4333step1Labels := by
      have hz : ∀ j, raw4333step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4333step1 = (fun i j => raw4333step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4333step1 raw4333step0; decide +kernel
      have hl : raw4333step1Labels = raw4333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4333step0 raw4333step0Labels permutation80 hz
    mixedMoment B raw4333step1 raw4333step1Labels = mixedMoment B raw4333step2 raw4333step2Labels := by
      have ha : raw4333step2 = (fun i j => raw4333step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4333step2 raw4333step1; decide +kernel
      have hl : raw4333step2Labels = raw4333step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4333step1 raw4333step1Labels permutation31 permutation3
    mixedMoment B raw4333step2 raw4333step2Labels = mixedMoment B raw4333step3 raw4333step3Labels := by
      have ha : raw4333step3 = -raw4333step2 := by apply Matrix.ext; change ∀ i j, raw4333step3 i j = -(raw4333step2 i j); unfold raw4333step3 raw4333step2; decide +kernel
      have hl : raw4333step3Labels = raw4333step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw4334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4334step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4334step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw4334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4334step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4334step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4334 raw4334Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw4334 raw4334Labels = mixedMoment B raw4334step0 raw4334step0Labels := by
      have hz : ∀ j, raw4334 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4334step0 = (fun i j => raw4334 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4334step0 raw4334; decide +kernel
      have hl : raw4334step0Labels = raw4334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4334 raw4334Labels permutation434 hz
    mixedMoment B raw4334step0 raw4334step0Labels = mixedMoment B raw4334step1 raw4334step1Labels := by
      have hz : ∀ j, raw4334step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4334step1 = (fun i j => raw4334step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4334step1 raw4334step0; decide +kernel
      have hl : raw4334step1Labels = raw4334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4334step0 raw4334step0Labels permutation56 hz
    mixedMoment B raw4334step1 raw4334step1Labels = mixedMoment B raw4334step2 raw4334step2Labels := by
      have ha : raw4334step2 = (fun i j => raw4334step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4334step2 raw4334step1; decide +kernel
      have hl : raw4334step2Labels = raw4334step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4334step1 raw4334step1Labels permutation31 permutation3
    mixedMoment B raw4334step2 raw4334step2Labels = mixedMoment B raw4334step3 raw4334step3Labels := by
      have ha : raw4334step3 = -raw4334step2 := by apply Matrix.ext; change ∀ i j, raw4334step3 i j = -(raw4334step2 i j); unfold raw4334step3 raw4334step2; decide +kernel
      have hl : raw4334step3Labels = raw4334step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw4335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4335step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw4335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4335step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4335step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4335 raw4335Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw4335 raw4335Labels = mixedMoment B raw4335step0 raw4335step0Labels := by
      have hz : ∀ j, raw4335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4335step0 = (fun i j => raw4335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4335step0 raw4335; decide +kernel
      have hl : raw4335step0Labels = raw4335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4335 raw4335Labels permutation346 hz
    mixedMoment B raw4335step0 raw4335step0Labels = mixedMoment B raw4335step1 raw4335step1Labels := by
      have hz : ∀ j, raw4335step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4335step1 = (fun i j => raw4335step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4335step1 raw4335step0; decide +kernel
      have hl : raw4335step1Labels = raw4335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4335step0 raw4335step0Labels permutation56 hz
    mixedMoment B raw4335step1 raw4335step1Labels = mixedMoment B raw4335step2 raw4335step2Labels := by
      have ha : raw4335step2 = (fun i j => raw4335step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4335step2 raw4335step1; decide +kernel
      have hl : raw4335step2Labels = raw4335step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4335step1 raw4335step1Labels permutation31 permutation3
    mixedMoment B raw4335step2 raw4335step2Labels = mixedMoment B raw4335step3 raw4335step3Labels := by
      have ha : raw4335step3 = -raw4335step2 := by apply Matrix.ext; change ∀ i j, raw4335step3 i j = -(raw4335step2 i j); unfold raw4335step3 raw4335step2; decide +kernel
      have hl : raw4335step3Labels = raw4335step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw4336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw4336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw4336step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw4336step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4336step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw4336step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4336step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw4336step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4336 raw4336Labels = mixedMoment B node3123 node3123Labels := by
  calc
    mixedMoment B raw4336 raw4336Labels = mixedMoment B raw4336step0 raw4336step0Labels := by
      have hz : ∀ j, raw4336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4336step0 = (fun i j => raw4336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4336step0 raw4336; decide +kernel
      have hl : raw4336step0Labels = raw4336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4336 raw4336Labels permutation434 hz
    mixedMoment B raw4336step0 raw4336step0Labels = mixedMoment B raw4336step1 raw4336step1Labels := by
      have hz : ∀ j, raw4336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4336step1 = (fun i j => raw4336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4336step1 raw4336step0; decide +kernel
      have hl : raw4336step1Labels = raw4336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4336step0 raw4336step0Labels permutation80 hz
    mixedMoment B raw4336step1 raw4336step1Labels = mixedMoment B raw4336step2 raw4336step2Labels := by
      have hz : ∀ j, raw4336step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4336step2 = (fun i j => raw4336step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4336step2 raw4336step1; decide +kernel
      have hl : raw4336step2Labels = raw4336step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4336step1 raw4336step1Labels permutation14 hz
    mixedMoment B raw4336step2 raw4336step2Labels = mixedMoment B raw4336step3 raw4336step3Labels := by
      have ha : raw4336step3 = (fun i j => raw4336step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4336step3 raw4336step2; decide +kernel
      have hl : raw4336step3Labels = raw4336step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4336step2 raw4336step2Labels permutation2 permutation3
    _ = mixedMoment B node3123 node3123Labels := by rfl

def raw4337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4337step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4337step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw4337step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4337step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw4337step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4337step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw4337step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4337 raw4337Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw4337 raw4337Labels = mixedMoment B raw4337step0 raw4337step0Labels := by
      have hz : ∀ j, raw4337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4337step0 = (fun i j => raw4337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4337step0 raw4337; decide +kernel
      have hl : raw4337step0Labels = raw4337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4337 raw4337Labels permutation434 hz
    mixedMoment B raw4337step0 raw4337step0Labels = mixedMoment B raw4337step1 raw4337step1Labels := by
      have hz : ∀ j, raw4337step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4337step1 = (fun i j => raw4337step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4337step1 raw4337step0; decide +kernel
      have hl : raw4337step1Labels = raw4337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4337step0 raw4337step0Labels permutation80 hz
    mixedMoment B raw4337step1 raw4337step1Labels = mixedMoment B raw4337step2 raw4337step2Labels := by
      have hz : ∀ j, raw4337step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4337step2 = (fun i j => raw4337step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4337step2 raw4337step1; decide +kernel
      have hl : raw4337step2Labels = raw4337step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4337step1 raw4337step1Labels permutation14 hz
    mixedMoment B raw4337step2 raw4337step2Labels = mixedMoment B raw4337step3 raw4337step3Labels := by
      have ha : raw4337step3 = (fun i j => raw4337step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4337step3 raw4337step2; decide +kernel
      have hl : raw4337step3Labels = raw4337step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4337step2 raw4337step2Labels permutation7 permutation3
    mixedMoment B raw4337step3 raw4337step3Labels = mixedMoment B raw4337step4 raw4337step4Labels := by
      have ha : raw4337step4 = -raw4337step3 := by apply Matrix.ext; change ∀ i j, raw4337step4 i j = -(raw4337step3 i j); unfold raw4337step4 raw4337step3; decide +kernel
      have hl : raw4337step4Labels = raw4337step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw4338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4338step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4338step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4338step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4338 raw4338Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw4338 raw4338Labels = mixedMoment B raw4338step0 raw4338step0Labels := by
      have hz : ∀ j, raw4338 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4338step0 = (fun i j => raw4338 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4338step0 raw4338; decide +kernel
      have hl : raw4338step0Labels = raw4338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4338 raw4338Labels permutation434 hz
    mixedMoment B raw4338step0 raw4338step0Labels = mixedMoment B raw4338step1 raw4338step1Labels := by
      have hz : ∀ j, raw4338step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4338step1 = (fun i j => raw4338step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4338step1 raw4338step0; decide +kernel
      have hl : raw4338step1Labels = raw4338step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4338step0 raw4338step0Labels permutation80 hz
    mixedMoment B raw4338step1 raw4338step1Labels = mixedMoment B raw4338step2 raw4338step2Labels := by
      have ha : raw4338step2 = (fun i j => raw4338step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4338step2 raw4338step1; decide +kernel
      have hl : raw4338step2Labels = raw4338step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4338step1 raw4338step1Labels permutation31 permutation3
    mixedMoment B raw4338step2 raw4338step2Labels = mixedMoment B raw4338step3 raw4338step3Labels := by
      have ha : raw4338step3 = -raw4338step2 := by apply Matrix.ext; change ∀ i j, raw4338step3 i j = -(raw4338step2 i j); unfold raw4338step3 raw4338step2; decide +kernel
      have hl : raw4338step3Labels = raw4338step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw4339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4339step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4339step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4339step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4339step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4339 raw4339Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw4339 raw4339Labels = mixedMoment B raw4339step0 raw4339step0Labels := by
      have hz : ∀ j, raw4339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4339step0 = (fun i j => raw4339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4339step0 raw4339; decide +kernel
      have hl : raw4339step0Labels = raw4339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4339 raw4339Labels permutation434 hz
    mixedMoment B raw4339step0 raw4339step0Labels = mixedMoment B raw4339step1 raw4339step1Labels := by
      have hz : ∀ j, raw4339step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4339step1 = (fun i j => raw4339step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4339step1 raw4339step0; decide +kernel
      have hl : raw4339step1Labels = raw4339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4339step0 raw4339step0Labels permutation56 hz
    mixedMoment B raw4339step1 raw4339step1Labels = mixedMoment B raw4339step2 raw4339step2Labels := by
      have ha : raw4339step2 = (fun i j => raw4339step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4339step2 raw4339step1; decide +kernel
      have hl : raw4339step2Labels = raw4339step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4339step1 raw4339step1Labels permutation31 permutation3
    mixedMoment B raw4339step2 raw4339step2Labels = mixedMoment B raw4339step3 raw4339step3Labels := by
      have ha : raw4339step3 = -raw4339step2 := by apply Matrix.ext; change ∀ i j, raw4339step3 i j = -(raw4339step2 i j); unfold raw4339step3 raw4339step2; decide +kernel
      have hl : raw4339step3Labels = raw4339step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw4340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4340step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4340step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4340step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4340step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4340 raw4340Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw4340 raw4340Labels = mixedMoment B raw4340step0 raw4340step0Labels := by
      have hz : ∀ j, raw4340 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4340step0 = (fun i j => raw4340 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4340step0 raw4340; decide +kernel
      have hl : raw4340step0Labels = raw4340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4340 raw4340Labels permutation346 hz
    mixedMoment B raw4340step0 raw4340step0Labels = mixedMoment B raw4340step1 raw4340step1Labels := by
      have hz : ∀ j, raw4340step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4340step1 = (fun i j => raw4340step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4340step1 raw4340step0; decide +kernel
      have hl : raw4340step1Labels = raw4340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4340step0 raw4340step0Labels permutation56 hz
    mixedMoment B raw4340step1 raw4340step1Labels = mixedMoment B raw4340step2 raw4340step2Labels := by
      have ha : raw4340step2 = (fun i j => raw4340step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4340step2 raw4340step1; decide +kernel
      have hl : raw4340step2Labels = raw4340step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4340step1 raw4340step1Labels permutation31 permutation3
    mixedMoment B raw4340step2 raw4340step2Labels = mixedMoment B raw4340step3 raw4340step3Labels := by
      have ha : raw4340step3 = -raw4340step2 := by apply Matrix.ext; change ∀ i j, raw4340step3 i j = -(raw4340step2 i j); unfold raw4340step3 raw4340step2; decide +kernel
      have hl : raw4340step3Labels = raw4340step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw4341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4341step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4341step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4341step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![4, -3, -1]]
def raw4341step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4341step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw4341step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4341step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw4341step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4341 raw4341Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw4341 raw4341Labels = mixedMoment B raw4341step0 raw4341step0Labels := by
      have hz : ∀ j, raw4341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4341step0 = (fun i j => raw4341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4341step0 raw4341; decide +kernel
      have hl : raw4341step0Labels = raw4341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4341 raw4341Labels permutation434 hz
    mixedMoment B raw4341step0 raw4341step0Labels = mixedMoment B raw4341step1 raw4341step1Labels := by
      have hz : ∀ j, raw4341step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4341step1 = (fun i j => raw4341step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4341step1 raw4341step0; decide +kernel
      have hl : raw4341step1Labels = raw4341step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4341step0 raw4341step0Labels permutation80 hz
    mixedMoment B raw4341step1 raw4341step1Labels = mixedMoment B raw4341step2 raw4341step2Labels := by
      have hz : ∀ j, raw4341step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4341step2 = (fun i j => raw4341step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4341step2 raw4341step1; decide +kernel
      have hl : raw4341step2Labels = raw4341step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4341step1 raw4341step1Labels permutation14 hz
    mixedMoment B raw4341step2 raw4341step2Labels = mixedMoment B raw4341step3 raw4341step3Labels := by
      have ha : raw4341step3 = (fun i j => raw4341step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4341step3 raw4341step2; decide +kernel
      have hl : raw4341step3Labels = raw4341step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4341step2 raw4341step2Labels permutation7 permutation3
    mixedMoment B raw4341step3 raw4341step3Labels = mixedMoment B raw4341step4 raw4341step4Labels := by
      have ha : raw4341step4 = -raw4341step3 := by apply Matrix.ext; change ∀ i j, raw4341step4 i j = -(raw4341step3 i j); unfold raw4341step4 raw4341step3; decide +kernel
      have hl : raw4341step4Labels = raw4341step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw4342 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4342step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4342step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4342step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4342step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4342step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4342 raw4342Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4342 raw4342Labels = mixedMoment B raw4342step0 raw4342step0Labels := by
      have hz : ∀ j, raw4342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4342step0 = (fun i j => raw4342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4342step0 raw4342; decide +kernel
      have hl : raw4342step0Labels = raw4342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4342 raw4342Labels permutation434 hz
    mixedMoment B raw4342step0 raw4342step0Labels = mixedMoment B raw4342step1 raw4342step1Labels := by
      have hz : ∀ j, raw4342step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4342step1 = (fun i j => raw4342step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4342step1 raw4342step0; decide +kernel
      have hl : raw4342step1Labels = raw4342step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4342step0 raw4342step0Labels permutation56 hz
    mixedMoment B raw4342step1 raw4342step1Labels = mixedMoment B raw4342step2 raw4342step2Labels := by
      have ha : raw4342step2 = (fun i j => raw4342step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4342step2 raw4342step1; decide +kernel
      have hl : raw4342step2Labels = raw4342step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4342step1 raw4342step1Labels permutation10 permutation7
    mixedMoment B raw4342step2 raw4342step2Labels = mixedMoment B raw4342step3 raw4342step3Labels := by
      have ha : raw4342step3 = raw4342step2 := by apply Matrix.ext; unfold raw4342step3 raw4342step2; decide +kernel
      have hl : raw4342step2Labels = labelEmbedding10 ∘ raw4342step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4342step2 raw4342step2Labels raw4342step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw4343 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4343step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4343step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4343step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4343step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4343step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4343step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4343 raw4343Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4343 raw4343Labels = mixedMoment B raw4343step0 raw4343step0Labels := by
      have hz : ∀ j, raw4343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4343step0 = (fun i j => raw4343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4343step0 raw4343; decide +kernel
      have hl : raw4343step0Labels = raw4343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4343 raw4343Labels permutation346 hz
    mixedMoment B raw4343step0 raw4343step0Labels = mixedMoment B raw4343step1 raw4343step1Labels := by
      have hz : ∀ j, raw4343step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4343step1 = (fun i j => raw4343step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4343step1 raw4343step0; decide +kernel
      have hl : raw4343step1Labels = raw4343step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4343step0 raw4343step0Labels permutation56 hz
    mixedMoment B raw4343step1 raw4343step1Labels = mixedMoment B raw4343step2 raw4343step2Labels := by
      have ha : raw4343step2 = (fun i j => raw4343step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4343step2 raw4343step1; decide +kernel
      have hl : raw4343step2Labels = raw4343step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4343step1 raw4343step1Labels permutation10 permutation7
    mixedMoment B raw4343step2 raw4343step2Labels = mixedMoment B raw4343step3 raw4343step3Labels := by
      have ha : raw4343step3 = raw4343step2 := by apply Matrix.ext; unfold raw4343step3 raw4343step2; decide +kernel
      have hl : raw4343step2Labels = labelEmbedding10 ∘ raw4343step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4343step2 raw4343step2Labels raw4343step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw4344 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4344step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, -1, 3]]
def raw4344step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4344step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 1, -3], ![-2, -1, 3]]
def raw4344step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4344step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw4344step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4344step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw4344step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4344 raw4344Labels = mixedMoment B node5312 node5312Labels := by
  calc
    mixedMoment B raw4344 raw4344Labels = mixedMoment B raw4344step0 raw4344step0Labels := by
      have hz : ∀ j, raw4344 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4344step0 = (fun i j => raw4344 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4344step0 raw4344; decide +kernel
      have hl : raw4344step0Labels = raw4344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4344 raw4344Labels permutation520 hz
    mixedMoment B raw4344step0 raw4344step0Labels = mixedMoment B raw4344step1 raw4344step1Labels := by
      have hz : ∀ j, raw4344step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4344step1 = (fun i j => raw4344step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4344step1 raw4344step0; decide +kernel
      have hl : raw4344step1Labels = raw4344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4344step0 raw4344step0Labels permutation104 hz
    mixedMoment B raw4344step1 raw4344step1Labels = mixedMoment B raw4344step2 raw4344step2Labels := by
      have hz : ∀ j, raw4344step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw4344step2 = (fun i j => raw4344step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw4344step2 raw4344step1; decide +kernel
      have hl : raw4344step2Labels = raw4344step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4344step1 raw4344step1Labels permutation20 hz
    mixedMoment B raw4344step2 raw4344step2Labels = mixedMoment B raw4344step3 raw4344step3Labels := by
      have hz : ∀ j, raw4344step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw4344step3 = (fun i j => raw4344step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw4344step3 raw4344step2; decide +kernel
      have hl : raw4344step3Labels = raw4344step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4344step2 raw4344step2Labels permutation4 hz
    mixedMoment B raw4344step3 raw4344step3Labels = mixedMoment B raw4344step4 raw4344step4Labels := by
      have ha : raw4344step4 = (fun i j => raw4344step3 (permutation0 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4344step4 raw4344step3; decide +kernel
      have hl : raw4344step4Labels = raw4344step3Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4344step3 raw4344step3Labels permutation0 permutation7
    mixedMoment B raw4344step4 raw4344step4Labels = mixedMoment B raw4344step5 raw4344step5Labels := by
      have ha : raw4344step5 = raw4344step4 := by apply Matrix.ext; unfold raw4344step5 raw4344step4; decide +kernel
      have hl : raw4344step4Labels = labelEmbedding10 ∘ raw4344step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4344step4 raw4344step4Labels raw4344step5Labels labelEmbedding10 hl
    _ = mixedMoment B node5312 node5312Labels := by rfl

def raw4345 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4345step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4345step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4345step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4345step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw4345step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4345step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4345step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4345step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4345step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4345 raw4345Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw4345 raw4345Labels = mixedMoment B raw4345step0 raw4345step0Labels := by
      have hz : ∀ j, raw4345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4345step0 = (fun i j => raw4345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4345step0 raw4345; decide +kernel
      have hl : raw4345step0Labels = raw4345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4345 raw4345Labels permutation434 hz
    mixedMoment B raw4345step0 raw4345step0Labels = mixedMoment B raw4345step1 raw4345step1Labels := by
      have hz : ∀ j, raw4345step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4345step1 = (fun i j => raw4345step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4345step1 raw4345step0; decide +kernel
      have hl : raw4345step1Labels = raw4345step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4345step0 raw4345step0Labels permutation80 hz
    mixedMoment B raw4345step1 raw4345step1Labels = mixedMoment B raw4345step2 raw4345step2Labels := by
      have hz : ∀ j, raw4345step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4345step2 = (fun i j => raw4345step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4345step2 raw4345step1; decide +kernel
      have hl : raw4345step2Labels = raw4345step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4345step1 raw4345step1Labels permutation14 hz
    mixedMoment B raw4345step2 raw4345step2Labels = mixedMoment B raw4345step3 raw4345step3Labels := by
      have ha : raw4345step3 = (fun i j => raw4345step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4345step3 raw4345step2; decide +kernel
      have hl : raw4345step3Labels = raw4345step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4345step2 raw4345step2Labels permutation7 permutation7
    mixedMoment B raw4345step3 raw4345step3Labels = mixedMoment B raw4345step4 raw4345step4Labels := by
      have ha : raw4345step4 = -raw4345step3 := by apply Matrix.ext; change ∀ i j, raw4345step4 i j = -(raw4345step3 i j); unfold raw4345step4 raw4345step3; decide +kernel
      have hl : raw4345step4Labels = raw4345step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4345step4 raw4345step4Labels = mixedMoment B raw4345step5 raw4345step5Labels := by
      have ha : raw4345step5 = raw4345step4 := by apply Matrix.ext; unfold raw4345step5 raw4345step4; decide +kernel
      have hl : raw4345step4Labels = labelEmbedding10 ∘ raw4345step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4345step4 raw4345step4Labels raw4345step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw4346 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4346step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4346step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4346step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4346step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4346 raw4346Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw4346 raw4346Labels = mixedMoment B raw4346step0 raw4346step0Labels := by
      have hz : ∀ j, raw4346 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4346step0 = (fun i j => raw4346 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4346step0 raw4346; decide +kernel
      have hl : raw4346step0Labels = raw4346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4346 raw4346Labels permutation434 hz
    mixedMoment B raw4346step0 raw4346step0Labels = mixedMoment B raw4346step1 raw4346step1Labels := by
      have hz : ∀ j, raw4346step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4346step1 = (fun i j => raw4346step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4346step1 raw4346step0; decide +kernel
      have hl : raw4346step1Labels = raw4346step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4346step0 raw4346step0Labels permutation80 hz
    mixedMoment B raw4346step1 raw4346step1Labels = mixedMoment B raw4346step2 raw4346step2Labels := by
      have ha : raw4346step2 = (fun i j => raw4346step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4346step2 raw4346step1; decide +kernel
      have hl : raw4346step2Labels = raw4346step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4346step1 raw4346step1Labels permutation8 permutation6
    mixedMoment B raw4346step2 raw4346step2Labels = mixedMoment B raw4346step3 raw4346step3Labels := by
      have ha : raw4346step3 = raw4346step2 := by apply Matrix.ext; unfold raw4346step3 raw4346step2; decide +kernel
      have hl : raw4346step2Labels = labelEmbedding9 ∘ raw4346step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4346step2 raw4346step2Labels raw4346step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw4347 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4347step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4347 raw4347Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4347 raw4347Labels = mixedMoment B raw4347step0 raw4347step0Labels := by
      have hz : ∀ j, raw4347 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4347step0 = (fun i j => raw4347 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4347step0 raw4347; decide +kernel
      have hl : raw4347step0Labels = raw4347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4347 raw4347Labels permutation434 hz
    mixedMoment B raw4347step0 raw4347step0Labels = mixedMoment B raw4347step1 raw4347step1Labels := by
      have ha : raw4347step1 = (fun i j => raw4347step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4347step1 raw4347step0; decide +kernel
      have hl : raw4347step1Labels = raw4347step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4347step0 raw4347step0Labels permutation38 permutation6
    mixedMoment B raw4347step1 raw4347step1Labels = mixedMoment B raw4347step2 raw4347step2Labels := by
      have ha : raw4347step2 = raw4347step1 := by apply Matrix.ext; unfold raw4347step2 raw4347step1; decide +kernel
      have hl : raw4347step1Labels = labelEmbedding9 ∘ raw4347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4347step1 raw4347step1Labels raw4347step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw4348 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4348step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4348step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4348 raw4348Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4348 raw4348Labels = mixedMoment B raw4348step0 raw4348step0Labels := by
      have hz : ∀ j, raw4348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4348step0 = (fun i j => raw4348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4348step0 raw4348; decide +kernel
      have hl : raw4348step0Labels = raw4348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4348 raw4348Labels permutation346 hz
    mixedMoment B raw4348step0 raw4348step0Labels = mixedMoment B raw4348step1 raw4348step1Labels := by
      have ha : raw4348step1 = (fun i j => raw4348step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4348step1 raw4348step0; decide +kernel
      have hl : raw4348step1Labels = raw4348step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4348step0 raw4348step0Labels permutation38 permutation6
    mixedMoment B raw4348step1 raw4348step1Labels = mixedMoment B raw4348step2 raw4348step2Labels := by
      have ha : raw4348step2 = raw4348step1 := by apply Matrix.ext; unfold raw4348step2 raw4348step1; decide +kernel
      have hl : raw4348step1Labels = labelEmbedding9 ∘ raw4348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4348step1 raw4348step1Labels raw4348step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw4349 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4349step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4349step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4349step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4349step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4349step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4349step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4349 raw4349Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw4349 raw4349Labels = mixedMoment B raw4349step0 raw4349step0Labels := by
      have hz : ∀ j, raw4349 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw4349step0 = (fun i j => raw4349 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw4349step0 raw4349; decide +kernel
      have hl : raw4349step0Labels = raw4349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4349 raw4349Labels permutation520 hz
    mixedMoment B raw4349step0 raw4349step0Labels = mixedMoment B raw4349step1 raw4349step1Labels := by
      have hz : ∀ j, raw4349step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw4349step1 = (fun i j => raw4349step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw4349step1 raw4349step0; decide +kernel
      have hl : raw4349step1Labels = raw4349step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4349step0 raw4349step0Labels permutation104 hz
    mixedMoment B raw4349step1 raw4349step1Labels = mixedMoment B raw4349step2 raw4349step2Labels := by
      have hz : ∀ j, raw4349step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw4349step2 = (fun i j => raw4349step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw4349step2 raw4349step1; decide +kernel
      have hl : raw4349step2Labels = raw4349step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4349step1 raw4349step1Labels permutation20 hz
    mixedMoment B raw4349step2 raw4349step2Labels = mixedMoment B raw4349step3 raw4349step3Labels := by
      have ha : raw4349step3 = (fun i j => raw4349step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4349step3 raw4349step2; decide +kernel
      have hl : raw4349step3Labels = raw4349step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4349step2 raw4349step2Labels permutation2 permutation6
    mixedMoment B raw4349step3 raw4349step3Labels = mixedMoment B raw4349step4 raw4349step4Labels := by
      have ha : raw4349step4 = raw4349step3 := by apply Matrix.ext; unfold raw4349step4 raw4349step3; decide +kernel
      have hl : raw4349step3Labels = labelEmbedding9 ∘ raw4349step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4349step3 raw4349step3Labels raw4349step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw4350 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4350step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4350step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4350step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4350step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4350step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4350step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4350 raw4350Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw4350 raw4350Labels = mixedMoment B raw4350step0 raw4350step0Labels := by
      have hz : ∀ j, raw4350 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4350step0 = (fun i j => raw4350 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4350step0 raw4350; decide +kernel
      have hl : raw4350step0Labels = raw4350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4350 raw4350Labels permutation434 hz
    mixedMoment B raw4350step0 raw4350step0Labels = mixedMoment B raw4350step1 raw4350step1Labels := by
      have hz : ∀ j, raw4350step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4350step1 = (fun i j => raw4350step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4350step1 raw4350step0; decide +kernel
      have hl : raw4350step1Labels = raw4350step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4350step0 raw4350step0Labels permutation80 hz
    mixedMoment B raw4350step1 raw4350step1Labels = mixedMoment B raw4350step2 raw4350step2Labels := by
      have ha : raw4350step2 = (fun i j => raw4350step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4350step2 raw4350step1; decide +kernel
      have hl : raw4350step2Labels = raw4350step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4350step1 raw4350step1Labels permutation29 permutation7
    mixedMoment B raw4350step2 raw4350step2Labels = mixedMoment B raw4350step3 raw4350step3Labels := by
      have ha : raw4350step3 = -raw4350step2 := by apply Matrix.ext; change ∀ i j, raw4350step3 i j = -(raw4350step2 i j); unfold raw4350step3 raw4350step2; decide +kernel
      have hl : raw4350step3Labels = raw4350step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4350step3 raw4350step3Labels = mixedMoment B raw4350step4 raw4350step4Labels := by
      have ha : raw4350step4 = raw4350step3 := by apply Matrix.ext; unfold raw4350step4 raw4350step3; decide +kernel
      have hl : raw4350step3Labels = labelEmbedding10 ∘ raw4350step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4350step3 raw4350step3Labels raw4350step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw4351 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4351step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4351step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4351 raw4351Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4351 raw4351Labels = mixedMoment B raw4351step0 raw4351step0Labels := by
      have hz : ∀ j, raw4351 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4351step0 = (fun i j => raw4351 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4351step0 raw4351; decide +kernel
      have hl : raw4351step0Labels = raw4351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4351 raw4351Labels permutation265 hz
    mixedMoment B raw4351step0 raw4351step0Labels = mixedMoment B raw4351step1 raw4351step1Labels := by
      have ha : raw4351step1 = (fun i j => raw4351step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4351step1 raw4351step0; decide +kernel
      have hl : raw4351step1Labels = raw4351step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4351step0 raw4351step0Labels permutation38 permutation6
    mixedMoment B raw4351step1 raw4351step1Labels = mixedMoment B raw4351step2 raw4351step2Labels := by
      have ha : raw4351step2 = raw4351step1 := by apply Matrix.ext; unfold raw4351step2 raw4351step1; decide +kernel
      have hl : raw4351step1Labels = labelEmbedding9 ∘ raw4351step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4351step1 raw4351step1Labels raw4351step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
