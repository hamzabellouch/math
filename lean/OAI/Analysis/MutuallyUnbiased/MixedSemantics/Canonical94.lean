import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12032 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12032Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12032 raw12032Labels = mixedMoment B node2131 node2131Labels := by
  calc
    mixedMoment B raw12032 raw12032Labels = mixedMoment B raw12032step0 raw12032step0Labels := by
      have ha : raw12032step0 = (fun i j => raw12032 (permutation355 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12032step0 raw12032; decide +kernel
      have hl : raw12032step0Labels = raw12032Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12032 raw12032Labels permutation355 permutation3
    mixedMoment B raw12032step0 raw12032step0Labels = mixedMoment B raw12032step1 raw12032step1Labels := by
      have ha : raw12032step1 = -raw12032step0 := by apply Matrix.ext; change ∀ i j, raw12032step1 i j = -(raw12032step0 i j); unfold raw12032step1 raw12032step0; decide +kernel
      have hl : raw12032step1Labels = raw12032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2131 node2131Labels := by rfl

def raw12033 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12033 raw12033Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw12033 raw12033Labels = mixedMoment B raw12033step0 raw12033step0Labels := by
      have ha : raw12033step0 = (fun i j => raw12033 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12033step0 raw12033; decide +kernel
      have hl : raw12033step0Labels = raw12033Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12033 raw12033Labels permutation154 permutation6
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw12034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12034 raw12034Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw12034 raw12034Labels = mixedMoment B raw12034step0 raw12034step0Labels := by
      have ha : raw12034step0 = (fun i j => raw12034 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12034step0 raw12034; decide +kernel
      have hl : raw12034step0Labels = raw12034Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12034 raw12034Labels permutation154 permutation6
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw12035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12035 raw12035Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw12035 raw12035Labels = mixedMoment B raw12035step0 raw12035step0Labels := by
      have ha : raw12035step0 = (fun i j => raw12035 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12035step0 raw12035; decide +kernel
      have hl : raw12035step0Labels = raw12035Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12035 raw12035Labels permutation154 permutation6
    _ = mixedMoment B node2728 node2728Labels := by rfl

def raw12036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12036 raw12036Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw12036 raw12036Labels = mixedMoment B raw12036step0 raw12036step0Labels := by
      have ha : raw12036step0 = (fun i j => raw12036 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12036step0 raw12036; decide +kernel
      have hl : raw12036step0Labels = raw12036Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12036 raw12036Labels permutation155 permutation6
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw12037 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12037 raw12037Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw12037 raw12037Labels = mixedMoment B raw12037step0 raw12037step0Labels := by
      have ha : raw12037step0 = (fun i j => raw12037 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12037step0 raw12037; decide +kernel
      have hl : raw12037step0Labels = raw12037Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12037 raw12037Labels permutation152 permutation6
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw12038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12038 raw12038Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw12038 raw12038Labels = mixedMoment B raw12038step0 raw12038step0Labels := by
      have ha : raw12038step0 = (fun i j => raw12038 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12038step0 raw12038; decide +kernel
      have hl : raw12038step0Labels = raw12038Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12038 raw12038Labels permutation152 permutation6
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw12039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12039 raw12039Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw12039 raw12039Labels = mixedMoment B raw12039step0 raw12039step0Labels := by
      have ha : raw12039step0 = (fun i j => raw12039 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12039step0 raw12039; decide +kernel
      have hl : raw12039step0Labels = raw12039Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12039 raw12039Labels permutation152 permutation6
    _ = mixedMoment B node2728 node2728Labels := by rfl

def raw12040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12040 raw12040Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw12040 raw12040Labels = mixedMoment B raw12040step0 raw12040step0Labels := by
      have ha : raw12040step0 = (fun i j => raw12040 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12040step0 raw12040; decide +kernel
      have hl : raw12040step0Labels = raw12040Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12040 raw12040Labels permutation153 permutation6
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw12041 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12041 raw12041Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw12041 raw12041Labels = mixedMoment B raw12041step0 raw12041step0Labels := by
      have ha : raw12041step0 = (fun i j => raw12041 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12041step0 raw12041; decide +kernel
      have hl : raw12041step0Labels = raw12041Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12041 raw12041Labels permutation152 permutation6
    _ = mixedMoment B node2720 node2720Labels := by rfl

def raw12042 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12042Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12042step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12042 raw12042Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw12042 raw12042Labels = mixedMoment B raw12042step0 raw12042step0Labels := by
      have ha : raw12042step0 = (fun i j => raw12042 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12042step0 raw12042; decide +kernel
      have hl : raw12042step0Labels = raw12042Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12042 raw12042Labels permutation180 permutation7
    mixedMoment B raw12042step0 raw12042step0Labels = mixedMoment B raw12042step1 raw12042step1Labels := by
      have ha : raw12042step1 = raw12042step0 := by apply Matrix.ext; unfold raw12042step1 raw12042step0; decide +kernel
      have hl : raw12042step0Labels = labelEmbedding1 ∘ raw12042step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12042step0 raw12042step0Labels raw12042step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw12043 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12043Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12043step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12043 raw12043Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw12043 raw12043Labels = mixedMoment B raw12043step0 raw12043step0Labels := by
      have ha : raw12043step0 = (fun i j => raw12043 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12043step0 raw12043; decide +kernel
      have hl : raw12043step0Labels = raw12043Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12043 raw12043Labels permutation181 permutation7
    mixedMoment B raw12043step0 raw12043step0Labels = mixedMoment B raw12043step1 raw12043step1Labels := by
      have ha : raw12043step1 = raw12043step0 := by apply Matrix.ext; unfold raw12043step1 raw12043step0; decide +kernel
      have hl : raw12043step0Labels = labelEmbedding1 ∘ raw12043step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12043step0 raw12043step0Labels raw12043step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw12044 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12044Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12044step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12044 raw12044Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw12044 raw12044Labels = mixedMoment B raw12044step0 raw12044step0Labels := by
      have ha : raw12044step0 = (fun i j => raw12044 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12044step0 raw12044; decide +kernel
      have hl : raw12044step0Labels = raw12044Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12044 raw12044Labels permutation180 permutation7
    mixedMoment B raw12044step0 raw12044step0Labels = mixedMoment B raw12044step1 raw12044step1Labels := by
      have ha : raw12044step1 = raw12044step0 := by apply Matrix.ext; unfold raw12044step1 raw12044step0; decide +kernel
      have hl : raw12044step0Labels = labelEmbedding1 ∘ raw12044step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12044step0 raw12044step0Labels raw12044step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw12045 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12045Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12045step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12045 raw12045Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw12045 raw12045Labels = mixedMoment B raw12045step0 raw12045step0Labels := by
      have ha : raw12045step0 = (fun i j => raw12045 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12045step0 raw12045; decide +kernel
      have hl : raw12045step0Labels = raw12045Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12045 raw12045Labels permutation176 permutation7
    mixedMoment B raw12045step0 raw12045step0Labels = mixedMoment B raw12045step1 raw12045step1Labels := by
      have ha : raw12045step1 = raw12045step0 := by apply Matrix.ext; unfold raw12045step1 raw12045step0; decide +kernel
      have hl : raw12045step0Labels = labelEmbedding1 ∘ raw12045step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12045step0 raw12045step0Labels raw12045step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2671 node2671Labels := by rfl

def raw12046 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12046Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12046step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12046 raw12046Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw12046 raw12046Labels = mixedMoment B raw12046step0 raw12046step0Labels := by
      have hz : ∀ j, raw12046 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12046step0 = (fun i j => raw12046 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12046step0 raw12046; decide +kernel
      have hl : raw12046step0Labels = raw12046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12046 raw12046Labels permutation265 hz
    mixedMoment B raw12046step0 raw12046step0Labels = mixedMoment B raw12046step1 raw12046step1Labels := by
      have ha : raw12046step1 = (fun i j => raw12046step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12046step1 raw12046step0; decide +kernel
      have hl : raw12046step1Labels = raw12046step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12046step0 raw12046step0Labels permutation36 permutation7
    mixedMoment B raw12046step1 raw12046step1Labels = mixedMoment B raw12046step2 raw12046step2Labels := by
      have ha : raw12046step2 = raw12046step1 := by apply Matrix.ext; unfold raw12046step2 raw12046step1; decide +kernel
      have hl : raw12046step1Labels = labelEmbedding1 ∘ raw12046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12046step1 raw12046step1Labels raw12046step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw12047 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12047Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12047step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12047step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12047 raw12047Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12047 raw12047Labels = mixedMoment B raw12047step0 raw12047step0Labels := by
      have hz : ∀ j, raw12047 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12047step0 = (fun i j => raw12047 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12047step0 raw12047; decide +kernel
      have hl : raw12047step0Labels = raw12047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12047 raw12047Labels permutation265 hz
    mixedMoment B raw12047step0 raw12047step0Labels = mixedMoment B raw12047step1 raw12047step1Labels := by
      have ha : raw12047step1 = (fun i j => raw12047step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12047step1 raw12047step0; decide +kernel
      have hl : raw12047step1Labels = raw12047step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12047step0 raw12047step0Labels permutation37 permutation7
    mixedMoment B raw12047step1 raw12047step1Labels = mixedMoment B raw12047step2 raw12047step2Labels := by
      have ha : raw12047step2 = raw12047step1 := by apply Matrix.ext; unfold raw12047step2 raw12047step1; decide +kernel
      have hl : raw12047step1Labels = labelEmbedding1 ∘ raw12047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12047step1 raw12047step1Labels raw12047step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw12048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12048Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12048step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12048step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12048 raw12048Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12048 raw12048Labels = mixedMoment B raw12048step0 raw12048step0Labels := by
      have hz : ∀ j, raw12048 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12048step0 = (fun i j => raw12048 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12048step0 raw12048; decide +kernel
      have hl : raw12048step0Labels = raw12048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12048 raw12048Labels permutation265 hz
    mixedMoment B raw12048step0 raw12048step0Labels = mixedMoment B raw12048step1 raw12048step1Labels := by
      have ha : raw12048step1 = (fun i j => raw12048step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12048step1 raw12048step0; decide +kernel
      have hl : raw12048step1Labels = raw12048step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12048step0 raw12048step0Labels permutation36 permutation7
    mixedMoment B raw12048step1 raw12048step1Labels = mixedMoment B raw12048step2 raw12048step2Labels := by
      have ha : raw12048step2 = raw12048step1 := by apply Matrix.ext; unfold raw12048step2 raw12048step1; decide +kernel
      have hl : raw12048step1Labels = labelEmbedding1 ∘ raw12048step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12048step1 raw12048step1Labels raw12048step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw12049 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12049step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12049 raw12049Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw12049 raw12049Labels = mixedMoment B raw12049step0 raw12049step0Labels := by
      have hz : ∀ j, raw12049 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12049step0 = (fun i j => raw12049 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12049step0 raw12049; decide +kernel
      have hl : raw12049step0Labels = raw12049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12049 raw12049Labels permutation265 hz
    mixedMoment B raw12049step0 raw12049step0Labels = mixedMoment B raw12049step1 raw12049step1Labels := by
      have ha : raw12049step1 = (fun i j => raw12049step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12049step1 raw12049step0; decide +kernel
      have hl : raw12049step1Labels = raw12049step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12049step0 raw12049step0Labels permutation32 permutation7
    mixedMoment B raw12049step1 raw12049step1Labels = mixedMoment B raw12049step2 raw12049step2Labels := by
      have ha : raw12049step2 = raw12049step1 := by apply Matrix.ext; unfold raw12049step2 raw12049step1; decide +kernel
      have hl : raw12049step1Labels = labelEmbedding1 ∘ raw12049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12049step1 raw12049step1Labels raw12049step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw12050 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw12050step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw12050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12050 raw12050Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw12050 raw12050Labels = mixedMoment B raw12050step0 raw12050step0Labels := by
      have ha : raw12050step0 = (fun i j => raw12050 (permutation427 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12050step0 raw12050; decide +kernel
      have hl : raw12050step0Labels = raw12050Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12050 raw12050Labels permutation427 permutation5
    mixedMoment B raw12050step0 raw12050step0Labels = mixedMoment B raw12050step1 raw12050step1Labels := by
      have ha : raw12050step1 = raw12050step0 := by apply Matrix.ext; unfold raw12050step1 raw12050step0; decide +kernel
      have hl : raw12050step0Labels = labelEmbedding1 ∘ raw12050step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12050step0 raw12050step0Labels raw12050step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2010 node2010Labels := by rfl

def raw12051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12051step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12051 raw12051Labels = mixedMoment B node2011 node2011Labels := by
  calc
    mixedMoment B raw12051 raw12051Labels = mixedMoment B raw12051step0 raw12051step0Labels := by
      have ha : raw12051step0 = (fun i j => raw12051 (permutation426 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12051step0 raw12051; decide +kernel
      have hl : raw12051step0Labels = raw12051Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12051 raw12051Labels permutation426 permutation5
    mixedMoment B raw12051step0 raw12051step0Labels = mixedMoment B raw12051step1 raw12051step1Labels := by
      have ha : raw12051step1 = raw12051step0 := by apply Matrix.ext; unfold raw12051step1 raw12051step0; decide +kernel
      have hl : raw12051step0Labels = labelEmbedding1 ∘ raw12051step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12051step0 raw12051step0Labels raw12051step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2011 node2011Labels := by rfl

def raw12052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12052step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12052 raw12052Labels = mixedMoment B node2024 node2024Labels := by
  calc
    mixedMoment B raw12052 raw12052Labels = mixedMoment B raw12052step0 raw12052step0Labels := by
      have ha : raw12052step0 = (fun i j => raw12052 (permutation431 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12052step0 raw12052; decide +kernel
      have hl : raw12052step0Labels = raw12052Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12052 raw12052Labels permutation431 permutation5
    mixedMoment B raw12052step0 raw12052step0Labels = mixedMoment B raw12052step1 raw12052step1Labels := by
      have ha : raw12052step1 = raw12052step0 := by apply Matrix.ext; unfold raw12052step1 raw12052step0; decide +kernel
      have hl : raw12052step0Labels = labelEmbedding1 ∘ raw12052step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12052step0 raw12052step0Labels raw12052step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2024 node2024Labels := by rfl

def raw12053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12053step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12053 raw12053Labels = mixedMoment B node2024 node2024Labels := by
  calc
    mixedMoment B raw12053 raw12053Labels = mixedMoment B raw12053step0 raw12053step0Labels := by
      have ha : raw12053step0 = (fun i j => raw12053 (permutation425 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12053step0 raw12053; decide +kernel
      have hl : raw12053step0Labels = raw12053Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12053 raw12053Labels permutation425 permutation5
    mixedMoment B raw12053step0 raw12053step0Labels = mixedMoment B raw12053step1 raw12053step1Labels := by
      have ha : raw12053step1 = raw12053step0 := by apply Matrix.ext; unfold raw12053step1 raw12053step0; decide +kernel
      have hl : raw12053step0Labels = labelEmbedding1 ∘ raw12053step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12053step0 raw12053step0Labels raw12053step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2024 node2024Labels := by rfl

def raw12054 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12054step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12054 raw12054Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw12054 raw12054Labels = mixedMoment B raw12054step0 raw12054step0Labels := by
      have ha : raw12054step0 = (fun i j => raw12054 (permutation394 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12054step0 raw12054; decide +kernel
      have hl : raw12054step0Labels = raw12054Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12054 raw12054Labels permutation394 permutation5
    mixedMoment B raw12054step0 raw12054step0Labels = mixedMoment B raw12054step1 raw12054step1Labels := by
      have ha : raw12054step1 = raw12054step0 := by apply Matrix.ext; unfold raw12054step1 raw12054step0; decide +kernel
      have hl : raw12054step0Labels = labelEmbedding1 ∘ raw12054step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12054step0 raw12054step0Labels raw12054step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2234 node2234Labels := by rfl

def raw12055 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12055Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw12055step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12055step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12055step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12055 raw12055Labels = mixedMoment B node3203 node3203Labels := by
  calc
    mixedMoment B raw12055 raw12055Labels = mixedMoment B raw12055step0 raw12055step0Labels := by
      have ha : raw12055step0 = (fun i j => raw12055 (permutation167 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12055step0 raw12055; decide +kernel
      have hl : raw12055step0Labels = raw12055Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12055 raw12055Labels permutation167 permutation5
    mixedMoment B raw12055step0 raw12055step0Labels = mixedMoment B raw12055step1 raw12055step1Labels := by
      have ha : raw12055step1 = -raw12055step0 := by apply Matrix.ext; change ∀ i j, raw12055step1 i j = -(raw12055step0 i j); unfold raw12055step1 raw12055step0; decide +kernel
      have hl : raw12055step1Labels = raw12055step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12055step1 raw12055step1Labels = mixedMoment B raw12055step2 raw12055step2Labels := by
      have ha : raw12055step2 = raw12055step1 := by apply Matrix.ext; unfold raw12055step2 raw12055step1; decide +kernel
      have hl : raw12055step1Labels = labelEmbedding1 ∘ raw12055step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12055step1 raw12055step1Labels raw12055step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3203 node3203Labels := by rfl

def raw12056 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12056Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12056step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12056 raw12056Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw12056 raw12056Labels = mixedMoment B raw12056step0 raw12056step0Labels := by
      have ha : raw12056step0 = (fun i j => raw12056 (permutation177 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12056step0 raw12056; decide +kernel
      have hl : raw12056step0Labels = raw12056Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12056 raw12056Labels permutation177 permutation7
    mixedMoment B raw12056step0 raw12056step0Labels = mixedMoment B raw12056step1 raw12056step1Labels := by
      have ha : raw12056step1 = raw12056step0 := by apply Matrix.ext; unfold raw12056step1 raw12056step0; decide +kernel
      have hl : raw12056step0Labels = labelEmbedding1 ∘ raw12056step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12056step0 raw12056step0Labels raw12056step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3043 node3043Labels := by rfl

def raw12057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12057step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12057 raw12057Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw12057 raw12057Labels = mixedMoment B raw12057step0 raw12057step0Labels := by
      have ha : raw12057step0 = (fun i j => raw12057 (permutation177 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12057step0 raw12057; decide +kernel
      have hl : raw12057step0Labels = raw12057Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12057 raw12057Labels permutation177 permutation7
    mixedMoment B raw12057step0 raw12057step0Labels = mixedMoment B raw12057step1 raw12057step1Labels := by
      have ha : raw12057step1 = raw12057step0 := by apply Matrix.ext; unfold raw12057step1 raw12057step0; decide +kernel
      have hl : raw12057step0Labels = labelEmbedding1 ∘ raw12057step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12057step0 raw12057step0Labels raw12057step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3036 node3036Labels := by rfl

def raw12058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12058Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12058step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12058 raw12058Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw12058 raw12058Labels = mixedMoment B raw12058step0 raw12058step0Labels := by
      have ha : raw12058step0 = (fun i j => raw12058 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12058step0 raw12058; decide +kernel
      have hl : raw12058step0Labels = raw12058Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12058 raw12058Labels permutation176 permutation7
    mixedMoment B raw12058step0 raw12058step0Labels = mixedMoment B raw12058step1 raw12058step1Labels := by
      have ha : raw12058step1 = raw12058step0 := by apply Matrix.ext; unfold raw12058step1 raw12058step0; decide +kernel
      have hl : raw12058step0Labels = labelEmbedding1 ∘ raw12058step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12058step0 raw12058step0Labels raw12058step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw12059 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12059Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw12059step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12059step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12059step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12059 raw12059Labels = mixedMoment B node3203 node3203Labels := by
  calc
    mixedMoment B raw12059 raw12059Labels = mixedMoment B raw12059step0 raw12059step0Labels := by
      have ha : raw12059step0 = (fun i j => raw12059 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12059step0 raw12059; decide +kernel
      have hl : raw12059step0Labels = raw12059Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12059 raw12059Labels permutation161 permutation5
    mixedMoment B raw12059step0 raw12059step0Labels = mixedMoment B raw12059step1 raw12059step1Labels := by
      have ha : raw12059step1 = -raw12059step0 := by apply Matrix.ext; change ∀ i j, raw12059step1 i j = -(raw12059step0 i j); unfold raw12059step1 raw12059step0; decide +kernel
      have hl : raw12059step1Labels = raw12059step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12059step1 raw12059step1Labels = mixedMoment B raw12059step2 raw12059step2Labels := by
      have ha : raw12059step2 = raw12059step1 := by apply Matrix.ext; unfold raw12059step2 raw12059step1; decide +kernel
      have hl : raw12059step1Labels = labelEmbedding1 ∘ raw12059step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12059step1 raw12059step1Labels raw12059step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3203 node3203Labels := by rfl

def raw12060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12060Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12060step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12060 raw12060Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw12060 raw12060Labels = mixedMoment B raw12060step0 raw12060step0Labels := by
      have ha : raw12060step0 = (fun i j => raw12060 (permutation179 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12060step0 raw12060; decide +kernel
      have hl : raw12060step0Labels = raw12060Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12060 raw12060Labels permutation179 permutation7
    mixedMoment B raw12060step0 raw12060step0Labels = mixedMoment B raw12060step1 raw12060step1Labels := by
      have ha : raw12060step1 = raw12060step0 := by apply Matrix.ext; unfold raw12060step1 raw12060step0; decide +kernel
      have hl : raw12060step0Labels = labelEmbedding1 ∘ raw12060step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12060step0 raw12060step0Labels raw12060step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3043 node3043Labels := by rfl

def raw12061 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12061Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12061step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12061step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12061 raw12061Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw12061 raw12061Labels = mixedMoment B raw12061step0 raw12061step0Labels := by
      have ha : raw12061step0 = (fun i j => raw12061 (permutation179 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12061step0 raw12061; decide +kernel
      have hl : raw12061step0Labels = raw12061Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12061 raw12061Labels permutation179 permutation7
    mixedMoment B raw12061step0 raw12061step0Labels = mixedMoment B raw12061step1 raw12061step1Labels := by
      have ha : raw12061step1 = raw12061step0 := by apply Matrix.ext; unfold raw12061step1 raw12061step0; decide +kernel
      have hl : raw12061step0Labels = labelEmbedding1 ∘ raw12061step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12061step0 raw12061step0Labels raw12061step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3036 node3036Labels := by rfl

def raw12062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12062Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12062step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12062 raw12062Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw12062 raw12062Labels = mixedMoment B raw12062step0 raw12062step0Labels := by
      have ha : raw12062step0 = (fun i j => raw12062 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12062step0 raw12062; decide +kernel
      have hl : raw12062step0Labels = raw12062Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12062 raw12062Labels permutation178 permutation7
    mixedMoment B raw12062step0 raw12062step0Labels = mixedMoment B raw12062step1 raw12062step1Labels := by
      have ha : raw12062step1 = raw12062step0 := by apply Matrix.ext; unfold raw12062step1 raw12062step0; decide +kernel
      have hl : raw12062step0Labels = labelEmbedding1 ∘ raw12062step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12062step0 raw12062step0Labels raw12062step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw12063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12063Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12063step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12063 raw12063Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw12063 raw12063Labels = mixedMoment B raw12063step0 raw12063step0Labels := by
      have ha : raw12063step0 = (fun i j => raw12063 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12063step0 raw12063; decide +kernel
      have hl : raw12063step0Labels = raw12063Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12063 raw12063Labels permutation180 permutation7
    mixedMoment B raw12063step0 raw12063step0Labels = mixedMoment B raw12063step1 raw12063step1Labels := by
      have ha : raw12063step1 = raw12063step0 := by apply Matrix.ext; unfold raw12063step1 raw12063step0; decide +kernel
      have hl : raw12063step0Labels = labelEmbedding1 ∘ raw12063step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12063step0 raw12063step0Labels raw12063step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3085 node3085Labels := by rfl

def raw12064 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12064 raw12064Labels = mixedMoment B node3378 node3378Labels := by
  calc
    mixedMoment B raw12064 raw12064Labels = mixedMoment B raw12064step0 raw12064step0Labels := by
      have ha : raw12064step0 = (fun i j => raw12064 (permutation197 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12064step0 raw12064; decide +kernel
      have hl : raw12064step0Labels = raw12064Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12064 raw12064Labels permutation197 permutation2
    mixedMoment B raw12064step0 raw12064step0Labels = mixedMoment B raw12064step1 raw12064step1Labels := by
      have ha : raw12064step1 = -raw12064step0 := by apply Matrix.ext; change ∀ i j, raw12064step1 i j = -(raw12064step0 i j); unfold raw12064step1 raw12064step0; decide +kernel
      have hl : raw12064step1Labels = raw12064step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3378 node3378Labels := by rfl

def raw12065 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12065 raw12065Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw12065 raw12065Labels = mixedMoment B raw12065step0 raw12065step0Labels := by
      have ha : raw12065step0 = (fun i j => raw12065 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12065step0 raw12065; decide +kernel
      have hl : raw12065step0Labels = raw12065Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12065 raw12065Labels permutation195 permutation2
    mixedMoment B raw12065step0 raw12065step0Labels = mixedMoment B raw12065step1 raw12065step1Labels := by
      have ha : raw12065step1 = -raw12065step0 := by apply Matrix.ext; change ∀ i j, raw12065step1 i j = -(raw12065step0 i j); unfold raw12065step1 raw12065step0; decide +kernel
      have hl : raw12065step1Labels = raw12065step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3376 node3376Labels := by rfl

def raw12066 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12066 raw12066Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw12066 raw12066Labels = mixedMoment B raw12066step0 raw12066step0Labels := by
      have ha : raw12066step0 = (fun i j => raw12066 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12066step0 raw12066; decide +kernel
      have hl : raw12066step0Labels = raw12066Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12066 raw12066Labels permutation194 permutation2
    mixedMoment B raw12066step0 raw12066step0Labels = mixedMoment B raw12066step1 raw12066step1Labels := by
      have ha : raw12066step1 = -raw12066step0 := by apply Matrix.ext; change ∀ i j, raw12066step1 i j = -(raw12066step0 i j); unfold raw12066step1 raw12066step0; decide +kernel
      have hl : raw12066step1Labels = raw12066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3376 node3376Labels := by rfl

def raw12067 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12067 raw12067Labels = mixedMoment B node3390 node3390Labels := by
  calc
    mixedMoment B raw12067 raw12067Labels = mixedMoment B raw12067step0 raw12067step0Labels := by
      have ha : raw12067step0 = (fun i j => raw12067 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12067step0 raw12067; decide +kernel
      have hl : raw12067step0Labels = raw12067Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12067 raw12067Labels permutation176 permutation2
    mixedMoment B raw12067step0 raw12067step0Labels = mixedMoment B raw12067step1 raw12067step1Labels := by
      have ha : raw12067step1 = -raw12067step0 := by apply Matrix.ext; change ∀ i j, raw12067step1 i j = -(raw12067step0 i j); unfold raw12067step1 raw12067step0; decide +kernel
      have hl : raw12067step1Labels = raw12067step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3390 node3390Labels := by rfl

def raw12068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12068 raw12068Labels = mixedMoment B node3150 node3150Labels := by
  calc
    mixedMoment B raw12068 raw12068Labels = mixedMoment B raw12068step0 raw12068step0Labels := by
      have ha : raw12068step0 = (fun i j => raw12068 (permutation364 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12068step0 raw12068; decide +kernel
      have hl : raw12068step0Labels = raw12068Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12068 raw12068Labels permutation364 permutation2
    mixedMoment B raw12068step0 raw12068step0Labels = mixedMoment B raw12068step1 raw12068step1Labels := by
      have ha : raw12068step1 = -raw12068step0 := by apply Matrix.ext; change ∀ i j, raw12068step1 i j = -(raw12068step0 i j); unfold raw12068step1 raw12068step0; decide +kernel
      have hl : raw12068step1Labels = raw12068step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3150 node3150Labels := by rfl

def raw12069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12069 raw12069Labels = mixedMoment B node3378 node3378Labels := by
  calc
    mixedMoment B raw12069 raw12069Labels = mixedMoment B raw12069step0 raw12069step0Labels := by
      have ha : raw12069step0 = (fun i j => raw12069 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12069step0 raw12069; decide +kernel
      have hl : raw12069step0Labels = raw12069Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12069 raw12069Labels permutation167 permutation4
    mixedMoment B raw12069step0 raw12069step0Labels = mixedMoment B raw12069step1 raw12069step1Labels := by
      have ha : raw12069step1 = -raw12069step0 := by apply Matrix.ext; change ∀ i j, raw12069step1 i j = -(raw12069step0 i j); unfold raw12069step1 raw12069step0; decide +kernel
      have hl : raw12069step1Labels = raw12069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3378 node3378Labels := by rfl

def raw12070 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12070 raw12070Labels = mixedMoment B node3378 node3378Labels := by
  calc
    mixedMoment B raw12070 raw12070Labels = mixedMoment B raw12070step0 raw12070step0Labels := by
      have ha : raw12070step0 = (fun i j => raw12070 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12070step0 raw12070; decide +kernel
      have hl : raw12070step0Labels = raw12070Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12070 raw12070Labels permutation161 permutation4
    mixedMoment B raw12070step0 raw12070step0Labels = mixedMoment B raw12070step1 raw12070step1Labels := by
      have ha : raw12070step1 = -raw12070step0 := by apply Matrix.ext; change ∀ i j, raw12070step1 i j = -(raw12070step0 i j); unfold raw12070step1 raw12070step0; decide +kernel
      have hl : raw12070step1Labels = raw12070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3378 node3378Labels := by rfl

def raw12071 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw12071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw12071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12071 raw12071Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw12071 raw12071Labels = mixedMoment B raw12071step0 raw12071step0Labels := by
      have ha : raw12071step0 = (fun i j => raw12071 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12071step0 raw12071; decide +kernel
      have hl : raw12071step0Labels = raw12071Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12071 raw12071Labels permutation161 permutation4
    mixedMoment B raw12071step0 raw12071step0Labels = mixedMoment B raw12071step1 raw12071step1Labels := by
      have ha : raw12071step1 = -raw12071step0 := by apply Matrix.ext; change ∀ i j, raw12071step1 i j = -(raw12071step0 i j); unfold raw12071step1 raw12071step0; decide +kernel
      have hl : raw12071step1Labels = raw12071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2010 node2010Labels := by rfl

def raw12072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12072 raw12072Labels = mixedMoment B node3149 node3149Labels := by
  calc
    mixedMoment B raw12072 raw12072Labels = mixedMoment B raw12072step0 raw12072step0Labels := by
      have ha : raw12072step0 = (fun i j => raw12072 (permutation362 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12072step0 raw12072; decide +kernel
      have hl : raw12072step0Labels = raw12072Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12072 raw12072Labels permutation362 permutation2
    mixedMoment B raw12072step0 raw12072step0Labels = mixedMoment B raw12072step1 raw12072step1Labels := by
      have ha : raw12072step1 = -raw12072step0 := by apply Matrix.ext; change ∀ i j, raw12072step1 i j = -(raw12072step0 i j); unfold raw12072step1 raw12072step0; decide +kernel
      have hl : raw12072step1Labels = raw12072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3149 node3149Labels := by rfl

def raw12073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12073 raw12073Labels = mixedMoment B node3149 node3149Labels := by
  calc
    mixedMoment B raw12073 raw12073Labels = mixedMoment B raw12073step0 raw12073step0Labels := by
      have ha : raw12073step0 = (fun i j => raw12073 (permutation361 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12073step0 raw12073; decide +kernel
      have hl : raw12073step0Labels = raw12073Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12073 raw12073Labels permutation361 permutation2
    mixedMoment B raw12073step0 raw12073step0Labels = mixedMoment B raw12073step1 raw12073step1Labels := by
      have ha : raw12073step1 = -raw12073step0 := by apply Matrix.ext; change ∀ i j, raw12073step1 i j = -(raw12073step0 i j); unfold raw12073step1 raw12073step0; decide +kernel
      have hl : raw12073step1Labels = raw12073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3149 node3149Labels := by rfl

def raw12074 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12074 raw12074Labels = mixedMoment B node3155 node3155Labels := by
  calc
    mixedMoment B raw12074 raw12074Labels = mixedMoment B raw12074step0 raw12074step0Labels := by
      have ha : raw12074step0 = (fun i j => raw12074 (permutation346 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12074step0 raw12074; decide +kernel
      have hl : raw12074step0Labels = raw12074Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12074 raw12074Labels permutation346 permutation2
    mixedMoment B raw12074step0 raw12074step0Labels = mixedMoment B raw12074step1 raw12074step1Labels := by
      have ha : raw12074step1 = -raw12074step0 := by apply Matrix.ext; change ∀ i j, raw12074step1 i j = -(raw12074step0 i j); unfold raw12074step1 raw12074step0; decide +kernel
      have hl : raw12074step1Labels = raw12074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3155 node3155Labels := by rfl

def raw12075 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12075 raw12075Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw12075 raw12075Labels = mixedMoment B raw12075step0 raw12075step0Labels := by
      have ha : raw12075step0 = (fun i j => raw12075 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12075step0 raw12075; decide +kernel
      have hl : raw12075step0Labels = raw12075Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12075 raw12075Labels permutation167 permutation4
    mixedMoment B raw12075step0 raw12075step0Labels = mixedMoment B raw12075step1 raw12075step1Labels := by
      have ha : raw12075step1 = -raw12075step0 := by apply Matrix.ext; change ∀ i j, raw12075step1 i j = -(raw12075step0 i j); unfold raw12075step1 raw12075step0; decide +kernel
      have hl : raw12075step1Labels = raw12075step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2023 node2023Labels := by rfl

def raw12076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12076 raw12076Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw12076 raw12076Labels = mixedMoment B raw12076step0 raw12076step0Labels := by
      have ha : raw12076step0 = (fun i j => raw12076 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12076step0 raw12076; decide +kernel
      have hl : raw12076step0Labels = raw12076Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12076 raw12076Labels permutation167 permutation4
    mixedMoment B raw12076step0 raw12076step0Labels = mixedMoment B raw12076step1 raw12076step1Labels := by
      have ha : raw12076step1 = -raw12076step0 := by apply Matrix.ext; change ∀ i j, raw12076step1 i j = -(raw12076step0 i j); unfold raw12076step1 raw12076step0; decide +kernel
      have hl : raw12076step1Labels = raw12076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3505 node3505Labels := by rfl

def raw12077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12077 raw12077Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw12077 raw12077Labels = mixedMoment B raw12077step0 raw12077step0Labels := by
      have ha : raw12077step0 = (fun i j => raw12077 (permutation169 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12077step0 raw12077; decide +kernel
      have hl : raw12077step0Labels = raw12077Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12077 raw12077Labels permutation169 permutation4
    mixedMoment B raw12077step0 raw12077step0Labels = mixedMoment B raw12077step1 raw12077step1Labels := by
      have ha : raw12077step1 = -raw12077step0 := by apply Matrix.ext; change ∀ i j, raw12077step1 i j = -(raw12077step0 i j); unfold raw12077step1 raw12077step0; decide +kernel
      have hl : raw12077step1Labels = raw12077step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw12078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12078 raw12078Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw12078 raw12078Labels = mixedMoment B raw12078step0 raw12078step0Labels := by
      have hz : ∀ j, raw12078 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12078step0 = (fun i j => raw12078 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12078step0 raw12078; decide +kernel
      have hl : raw12078step0Labels = raw12078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12078 raw12078Labels permutation265 hz
    mixedMoment B raw12078step0 raw12078step0Labels = mixedMoment B raw12078step1 raw12078step1Labels := by
      have ha : raw12078step1 = (fun i j => raw12078step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12078step1 raw12078step0; decide +kernel
      have hl : raw12078step1Labels = raw12078step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12078step0 raw12078step0Labels permutation41 permutation4
    mixedMoment B raw12078step1 raw12078step1Labels = mixedMoment B raw12078step2 raw12078step2Labels := by
      have ha : raw12078step2 = -raw12078step1 := by apply Matrix.ext; change ∀ i j, raw12078step2 i j = -(raw12078step1 i j); unfold raw12078step2 raw12078step1; decide +kernel
      have hl : raw12078step2Labels = raw12078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw12079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12079 raw12079Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw12079 raw12079Labels = mixedMoment B raw12079step0 raw12079step0Labels := by
      have ha : raw12079step0 = (fun i j => raw12079 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12079step0 raw12079; decide +kernel
      have hl : raw12079step0Labels = raw12079Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12079 raw12079Labels permutation161 permutation4
    mixedMoment B raw12079step0 raw12079step0Labels = mixedMoment B raw12079step1 raw12079step1Labels := by
      have ha : raw12079step1 = -raw12079step0 := by apply Matrix.ext; change ∀ i j, raw12079step1 i j = -(raw12079step0 i j); unfold raw12079step1 raw12079step0; decide +kernel
      have hl : raw12079step1Labels = raw12079step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3505 node3505Labels := by rfl

def raw12080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12080 raw12080Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw12080 raw12080Labels = mixedMoment B raw12080step0 raw12080step0Labels := by
      have hz : ∀ j, raw12080 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12080step0 = (fun i j => raw12080 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12080step0 raw12080; decide +kernel
      have hl : raw12080step0Labels = raw12080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12080 raw12080Labels permutation346 hz
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw12081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12081 raw12081Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw12081 raw12081Labels = mixedMoment B raw12081step0 raw12081step0Labels := by
      have hz : ∀ j, raw12081 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12081step0 = (fun i j => raw12081 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12081step0 raw12081; decide +kernel
      have hl : raw12081step0Labels = raw12081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12081 raw12081Labels permutation265 hz
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw12082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12082step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12082step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, 1, -2]]
def raw12082step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12082step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw12082step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12082step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw12082step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12082step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw12082step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12082 raw12082Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw12082 raw12082Labels = mixedMoment B raw12082step0 raw12082step0Labels := by
      have hz : ∀ j, raw12082 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12082step0 = (fun i j => raw12082 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12082step0 raw12082; decide +kernel
      have hl : raw12082step0Labels = raw12082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12082 raw12082Labels permutation520 hz
    mixedMoment B raw12082step0 raw12082step0Labels = mixedMoment B raw12082step1 raw12082step1Labels := by
      have hz : ∀ j, raw12082step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw12082step1 = (fun i j => raw12082step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw12082step1 raw12082step0; decide +kernel
      have hl : raw12082step1Labels = raw12082step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12082step0 raw12082step0Labels permutation80 hz
    mixedMoment B raw12082step1 raw12082step1Labels = mixedMoment B raw12082step2 raw12082step2Labels := by
      have hz : ∀ j, raw12082step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw12082step2 = (fun i j => raw12082step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw12082step2 raw12082step1; decide +kernel
      have hl : raw12082step2Labels = raw12082step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12082step1 raw12082step1Labels permutation14 hz
    mixedMoment B raw12082step2 raw12082step2Labels = mixedMoment B raw12082step3 raw12082step3Labels := by
      have ha : raw12082step3 = (fun i j => raw12082step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12082step3 raw12082step2; decide +kernel
      have hl : raw12082step3Labels = raw12082step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12082step2 raw12082step2Labels permutation2 permutation7
    mixedMoment B raw12082step3 raw12082step3Labels = mixedMoment B raw12082step4 raw12082step4Labels := by
      have ha : raw12082step4 = -raw12082step3 := by apply Matrix.ext; change ∀ i j, raw12082step4 i j = -(raw12082step3 i j); unfold raw12082step4 raw12082step3; decide +kernel
      have hl : raw12082step4Labels = raw12082step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12082step4 raw12082step4Labels = mixedMoment B raw12082step5 raw12082step5Labels := by
      have ha : raw12082step5 = raw12082step4 := by apply Matrix.ext; unfold raw12082step5 raw12082step4; decide +kernel
      have hl : raw12082step4Labels = labelEmbedding10 ∘ raw12082step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12082step4 raw12082step4Labels raw12082step5Labels labelEmbedding10 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw12083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12083step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12083step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12083step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12083 raw12083Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw12083 raw12083Labels = mixedMoment B raw12083step0 raw12083step0Labels := by
      have hz : ∀ j, raw12083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12083step0 = (fun i j => raw12083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12083step0 raw12083; decide +kernel
      have hl : raw12083step0Labels = raw12083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12083 raw12083Labels permutation346 hz
    mixedMoment B raw12083step0 raw12083step0Labels = mixedMoment B raw12083step1 raw12083step1Labels := by
      have hz : ∀ j, raw12083step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12083step1 = (fun i j => raw12083step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12083step1 raw12083step0; decide +kernel
      have hl : raw12083step1Labels = raw12083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12083step0 raw12083step0Labels permutation56 hz
    mixedMoment B raw12083step1 raw12083step1Labels = mixedMoment B raw12083step2 raw12083step2Labels := by
      have ha : raw12083step2 = (fun i j => raw12083step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12083step2 raw12083step1; decide +kernel
      have hl : raw12083step2Labels = raw12083step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12083step1 raw12083step1Labels permutation29 permutation6
    mixedMoment B raw12083step2 raw12083step2Labels = mixedMoment B raw12083step3 raw12083step3Labels := by
      have ha : raw12083step3 = raw12083step2 := by apply Matrix.ext; unfold raw12083step3 raw12083step2; decide +kernel
      have hl : raw12083step2Labels = labelEmbedding9 ∘ raw12083step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12083step2 raw12083step2Labels raw12083step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw12084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12084step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12084step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12084 raw12084Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw12084 raw12084Labels = mixedMoment B raw12084step0 raw12084step0Labels := by
      have hz : ∀ j, raw12084 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12084step0 = (fun i j => raw12084 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12084step0 raw12084; decide +kernel
      have hl : raw12084step0Labels = raw12084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12084 raw12084Labels permutation346 hz
    mixedMoment B raw12084step0 raw12084step0Labels = mixedMoment B raw12084step1 raw12084step1Labels := by
      have ha : raw12084step1 = (fun i j => raw12084step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12084step1 raw12084step0; decide +kernel
      have hl : raw12084step1Labels = raw12084step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12084step0 raw12084step0Labels permutation50 permutation3
    mixedMoment B raw12084step1 raw12084step1Labels = mixedMoment B raw12084step2 raw12084step2Labels := by
      have ha : raw12084step2 = raw12084step1 := by apply Matrix.ext; unfold raw12084step2 raw12084step1; decide +kernel
      have hl : raw12084step1Labels = labelEmbedding6 ∘ raw12084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12084step1 raw12084step1Labels raw12084step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw12085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12085 raw12085Labels = mixedMoment B node5166 node5166Labels := by
  calc
    mixedMoment B raw12085 raw12085Labels = mixedMoment B raw12085step0 raw12085step0Labels := by
      have ha : raw12085step0 = (fun i j => raw12085 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12085step0 raw12085; decide +kernel
      have hl : raw12085step0Labels = raw12085Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12085 raw12085Labels permutation176 permutation2
    _ = mixedMoment B node5166 node5166Labels := by rfl

def raw12086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12086 raw12086Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw12086 raw12086Labels = mixedMoment B raw12086step0 raw12086step0Labels := by
      have hz : ∀ j, raw12086 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12086step0 = (fun i j => raw12086 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12086step0 raw12086; decide +kernel
      have hl : raw12086step0Labels = raw12086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12086 raw12086Labels permutation520 hz
    mixedMoment B raw12086step0 raw12086step0Labels = mixedMoment B raw12086step1 raw12086step1Labels := by
      have hz : ∀ j, raw12086step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw12086step1 = (fun i j => raw12086step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw12086step1 raw12086step0; decide +kernel
      have hl : raw12086step1Labels = raw12086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12086step0 raw12086step0Labels permutation80 hz
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw12087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12087 raw12087Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw12087 raw12087Labels = mixedMoment B raw12087step0 raw12087step0Labels := by
      have hz : ∀ j, raw12087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12087step0 = (fun i j => raw12087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12087step0 raw12087; decide +kernel
      have hl : raw12087step0Labels = raw12087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12087 raw12087Labels permutation346 hz
    mixedMoment B raw12087step0 raw12087step0Labels = mixedMoment B raw12087step1 raw12087step1Labels := by
      have ha : raw12087step1 = (fun i j => raw12087step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12087step1 raw12087step0; decide +kernel
      have hl : raw12087step1Labels = raw12087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12087step0 raw12087step0Labels permutation50 permutation2
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw12088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12088step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12088 raw12088Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw12088 raw12088Labels = mixedMoment B raw12088step0 raw12088step0Labels := by
      have hz : ∀ j, raw12088 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12088step0 = (fun i j => raw12088 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12088step0 raw12088; decide +kernel
      have hl : raw12088step0Labels = raw12088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12088 raw12088Labels permutation265 hz
    mixedMoment B raw12088step0 raw12088step0Labels = mixedMoment B raw12088step1 raw12088step1Labels := by
      have ha : raw12088step1 = (fun i j => raw12088step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12088step1 raw12088step0; decide +kernel
      have hl : raw12088step1Labels = raw12088step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12088step0 raw12088step0Labels permutation50 permutation3
    mixedMoment B raw12088step1 raw12088step1Labels = mixedMoment B raw12088step2 raw12088step2Labels := by
      have ha : raw12088step2 = raw12088step1 := by apply Matrix.ext; unfold raw12088step2 raw12088step1; decide +kernel
      have hl : raw12088step1Labels = labelEmbedding6 ∘ raw12088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12088step1 raw12088step1Labels raw12088step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw12089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12089 raw12089Labels = mixedMoment B node5166 node5166Labels := by
  calc
    _ = mixedMoment B node5166 node5166Labels := by rfl

def raw12090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12090 raw12090Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw12090 raw12090Labels = mixedMoment B raw12090step0 raw12090step0Labels := by
      have hz : ∀ j, raw12090 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12090step0 = (fun i j => raw12090 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12090step0 raw12090; decide +kernel
      have hl : raw12090step0Labels = raw12090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12090 raw12090Labels permutation520 hz
    mixedMoment B raw12090step0 raw12090step0Labels = mixedMoment B raw12090step1 raw12090step1Labels := by
      have hz : ∀ j, raw12090step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12090step1 = (fun i j => raw12090step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12090step1 raw12090step0; decide +kernel
      have hl : raw12090step1Labels = raw12090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12090step0 raw12090step0Labels permutation56 hz
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw12091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12091 raw12091Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw12091 raw12091Labels = mixedMoment B raw12091step0 raw12091step0Labels := by
      have hz : ∀ j, raw12091 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12091step0 = (fun i j => raw12091 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12091step0 raw12091; decide +kernel
      have hl : raw12091step0Labels = raw12091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12091 raw12091Labels permutation265 hz
    mixedMoment B raw12091step0 raw12091step0Labels = mixedMoment B raw12091step1 raw12091step1Labels := by
      have ha : raw12091step1 = (fun i j => raw12091step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12091step1 raw12091step0; decide +kernel
      have hl : raw12091step1Labels = raw12091step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12091step0 raw12091step0Labels permutation50 permutation2
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw12092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12092step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12092step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12092 raw12092Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw12092 raw12092Labels = mixedMoment B raw12092step0 raw12092step0Labels := by
      have hz : ∀ j, raw12092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12092step0 = (fun i j => raw12092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12092step0 raw12092; decide +kernel
      have hl : raw12092step0Labels = raw12092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12092 raw12092Labels permutation346 hz
    mixedMoment B raw12092step0 raw12092step0Labels = mixedMoment B raw12092step1 raw12092step1Labels := by
      have hz : ∀ j, raw12092step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12092step1 = (fun i j => raw12092step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12092step1 raw12092step0; decide +kernel
      have hl : raw12092step1Labels = raw12092step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12092step0 raw12092step0Labels permutation56 hz
    mixedMoment B raw12092step1 raw12092step1Labels = mixedMoment B raw12092step2 raw12092step2Labels := by
      have ha : raw12092step2 = (fun i j => raw12092step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12092step2 raw12092step1; decide +kernel
      have hl : raw12092step2Labels = raw12092step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12092step1 raw12092step1Labels permutation13 permutation3
    mixedMoment B raw12092step2 raw12092step2Labels = mixedMoment B raw12092step3 raw12092step3Labels := by
      have ha : raw12092step3 = raw12092step2 := by apply Matrix.ext; unfold raw12092step3 raw12092step2; decide +kernel
      have hl : raw12092step2Labels = labelEmbedding6 ∘ raw12092step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12092step2 raw12092step2Labels raw12092step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw12093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12093 raw12093Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw12093 raw12093Labels = mixedMoment B raw12093step0 raw12093step0Labels := by
      have hz : ∀ j, raw12093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12093step0 = (fun i j => raw12093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12093step0 raw12093; decide +kernel
      have hl : raw12093step0Labels = raw12093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12093 raw12093Labels permutation346 hz
    mixedMoment B raw12093step0 raw12093step0Labels = mixedMoment B raw12093step1 raw12093step1Labels := by
      have ha : raw12093step1 = (fun i j => raw12093step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12093step1 raw12093step0; decide +kernel
      have hl : raw12093step1Labels = raw12093step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12093step0 raw12093step0Labels permutation35 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw12094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12094 raw12094Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw12094 raw12094Labels = mixedMoment B raw12094step0 raw12094step0Labels := by
      have hz : ∀ j, raw12094 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12094step0 = (fun i j => raw12094 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12094step0 raw12094; decide +kernel
      have hl : raw12094step0Labels = raw12094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12094 raw12094Labels permutation265 hz
    mixedMoment B raw12094step0 raw12094step0Labels = mixedMoment B raw12094step1 raw12094step1Labels := by
      have ha : raw12094step1 = (fun i j => raw12094step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12094step1 raw12094step0; decide +kernel
      have hl : raw12094step1Labels = raw12094step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12094step0 raw12094step0Labels permutation35 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw12095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12095step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw12095step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12095step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw12095step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12095 raw12095Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw12095 raw12095Labels = mixedMoment B raw12095step0 raw12095step0Labels := by
      have hz : ∀ j, raw12095 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12095step0 = (fun i j => raw12095 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12095step0 raw12095; decide +kernel
      have hl : raw12095step0Labels = raw12095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12095 raw12095Labels permutation520 hz
    mixedMoment B raw12095step0 raw12095step0Labels = mixedMoment B raw12095step1 raw12095step1Labels := by
      have hz : ∀ j, raw12095step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw12095step1 = (fun i j => raw12095step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw12095step1 raw12095step0; decide +kernel
      have hl : raw12095step1Labels = raw12095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12095step0 raw12095step0Labels permutation80 hz
    mixedMoment B raw12095step1 raw12095step1Labels = mixedMoment B raw12095step2 raw12095step2Labels := by
      have hz : ∀ j, raw12095step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw12095step2 = (fun i j => raw12095step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw12095step2 raw12095step1; decide +kernel
      have hl : raw12095step2Labels = raw12095step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12095step1 raw12095step1Labels permutation14 hz
    mixedMoment B raw12095step2 raw12095step2Labels = mixedMoment B raw12095step3 raw12095step3Labels := by
      have ha : raw12095step3 = (fun i j => raw12095step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12095step3 raw12095step2; decide +kernel
      have hl : raw12095step3Labels = raw12095step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12095step2 raw12095step2Labels permutation3 permutation2
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw12096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12096step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12096step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12096step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12096 raw12096Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw12096 raw12096Labels = mixedMoment B raw12096step0 raw12096step0Labels := by
      have hz : ∀ j, raw12096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12096step0 = (fun i j => raw12096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12096step0 raw12096; decide +kernel
      have hl : raw12096step0Labels = raw12096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12096 raw12096Labels permutation346 hz
    mixedMoment B raw12096step0 raw12096step0Labels = mixedMoment B raw12096step1 raw12096step1Labels := by
      have hz : ∀ j, raw12096step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12096step1 = (fun i j => raw12096step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12096step1 raw12096step0; decide +kernel
      have hl : raw12096step1Labels = raw12096step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12096step0 raw12096step0Labels permutation56 hz
    mixedMoment B raw12096step1 raw12096step1Labels = mixedMoment B raw12096step2 raw12096step2Labels := by
      have ha : raw12096step2 = (fun i j => raw12096step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12096step2 raw12096step1; decide +kernel
      have hl : raw12096step2Labels = raw12096step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12096step1 raw12096step1Labels permutation13 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw12097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12097step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12097step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12097step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12097 raw12097Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw12097 raw12097Labels = mixedMoment B raw12097step0 raw12097step0Labels := by
      have hz : ∀ j, raw12097 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12097step0 = (fun i j => raw12097 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12097step0 raw12097; decide +kernel
      have hl : raw12097step0Labels = raw12097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12097 raw12097Labels permutation346 hz
    mixedMoment B raw12097step0 raw12097step0Labels = mixedMoment B raw12097step1 raw12097step1Labels := by
      have hz : ∀ j, raw12097step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12097step1 = (fun i j => raw12097step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12097step1 raw12097step0; decide +kernel
      have hl : raw12097step1Labels = raw12097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12097step0 raw12097step0Labels permutation56 hz
    mixedMoment B raw12097step1 raw12097step1Labels = mixedMoment B raw12097step2 raw12097step2Labels := by
      have ha : raw12097step2 = (fun i j => raw12097step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12097step2 raw12097step1; decide +kernel
      have hl : raw12097step2Labels = raw12097step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12097step1 raw12097step1Labels permutation12 permutation3
    mixedMoment B raw12097step2 raw12097step2Labels = mixedMoment B raw12097step3 raw12097step3Labels := by
      have ha : raw12097step3 = raw12097step2 := by apply Matrix.ext; unfold raw12097step3 raw12097step2; decide +kernel
      have hl : raw12097step2Labels = labelEmbedding6 ∘ raw12097step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12097step2 raw12097step2Labels raw12097step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw12098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12098 raw12098Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw12098 raw12098Labels = mixedMoment B raw12098step0 raw12098step0Labels := by
      have hz : ∀ j, raw12098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12098step0 = (fun i j => raw12098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12098step0 raw12098; decide +kernel
      have hl : raw12098step0Labels = raw12098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12098 raw12098Labels permutation346 hz
    mixedMoment B raw12098step0 raw12098step0Labels = mixedMoment B raw12098step1 raw12098step1Labels := by
      have ha : raw12098step1 = (fun i j => raw12098step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12098step1 raw12098step0; decide +kernel
      have hl : raw12098step1Labels = raw12098step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12098step0 raw12098step0Labels permutation33 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw12099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12099step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12099 raw12099Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw12099 raw12099Labels = mixedMoment B raw12099step0 raw12099step0Labels := by
      have hz : ∀ j, raw12099 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12099step0 = (fun i j => raw12099 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12099step0 raw12099; decide +kernel
      have hl : raw12099step0Labels = raw12099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12099 raw12099Labels permutation265 hz
    mixedMoment B raw12099step0 raw12099step0Labels = mixedMoment B raw12099step1 raw12099step1Labels := by
      have ha : raw12099step1 = (fun i j => raw12099step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12099step1 raw12099step0; decide +kernel
      have hl : raw12099step1Labels = raw12099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12099step0 raw12099step0Labels permutation33 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw12100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw12100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw12100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw12100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12100step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12100 raw12100Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw12100 raw12100Labels = mixedMoment B raw12100step0 raw12100step0Labels := by
      have hz : ∀ j, raw12100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12100step0 = (fun i j => raw12100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12100step0 raw12100; decide +kernel
      have hl : raw12100step0Labels = raw12100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12100 raw12100Labels permutation346 hz
    mixedMoment B raw12100step0 raw12100step0Labels = mixedMoment B raw12100step1 raw12100step1Labels := by
      have hz : ∀ j, raw12100step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12100step1 = (fun i j => raw12100step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12100step1 raw12100step0; decide +kernel
      have hl : raw12100step1Labels = raw12100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12100step0 raw12100step0Labels permutation56 hz
    mixedMoment B raw12100step1 raw12100step1Labels = mixedMoment B raw12100step2 raw12100step2Labels := by
      have ha : raw12100step2 = (fun i j => raw12100step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12100step2 raw12100step1; decide +kernel
      have hl : raw12100step2Labels = raw12100step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12100step1 raw12100step1Labels permutation12 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw12101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12101step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12101 raw12101Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw12101 raw12101Labels = mixedMoment B raw12101step0 raw12101step0Labels := by
      have hz : ∀ j, raw12101 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12101step0 = (fun i j => raw12101 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12101step0 raw12101; decide +kernel
      have hl : raw12101step0Labels = raw12101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12101 raw12101Labels permutation346 hz
    mixedMoment B raw12101step0 raw12101step0Labels = mixedMoment B raw12101step1 raw12101step1Labels := by
      have ha : raw12101step1 = (fun i j => raw12101step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12101step1 raw12101step0; decide +kernel
      have hl : raw12101step1Labels = raw12101step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12101step0 raw12101step0Labels permutation137 permutation6
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw12102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12102 raw12102Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw12102 raw12102Labels = mixedMoment B raw12102step0 raw12102step0Labels := by
      have hz : ∀ j, raw12102 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12102step0 = (fun i j => raw12102 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12102step0 raw12102; decide +kernel
      have hl : raw12102step0Labels = raw12102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12102 raw12102Labels permutation265 hz
    mixedMoment B raw12102step0 raw12102step0Labels = mixedMoment B raw12102step1 raw12102step1Labels := by
      have ha : raw12102step1 = (fun i j => raw12102step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12102step1 raw12102step0; decide +kernel
      have hl : raw12102step1Labels = raw12102step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12102step0 raw12102step0Labels permutation137 permutation6
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw12103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12103step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12103step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, 1, -2]]
def raw12103step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12103step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw12103step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12103 raw12103Labels = mixedMoment B node4019 node4019Labels := by
  calc
    mixedMoment B raw12103 raw12103Labels = mixedMoment B raw12103step0 raw12103step0Labels := by
      have hz : ∀ j, raw12103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12103step0 = (fun i j => raw12103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12103step0 raw12103; decide +kernel
      have hl : raw12103step0Labels = raw12103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12103 raw12103Labels permutation434 hz
    mixedMoment B raw12103step0 raw12103step0Labels = mixedMoment B raw12103step1 raw12103step1Labels := by
      have hz : ∀ j, raw12103step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw12103step1 = (fun i j => raw12103step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw12103step1 raw12103step0; decide +kernel
      have hl : raw12103step1Labels = raw12103step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12103step0 raw12103step0Labels permutation80 hz
    mixedMoment B raw12103step1 raw12103step1Labels = mixedMoment B raw12103step2 raw12103step2Labels := by
      have hz : ∀ j, raw12103step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw12103step2 = (fun i j => raw12103step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw12103step2 raw12103step1; decide +kernel
      have hl : raw12103step2Labels = raw12103step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12103step1 raw12103step1Labels permutation14 hz
    mixedMoment B raw12103step2 raw12103step2Labels = mixedMoment B raw12103step3 raw12103step3Labels := by
      have ha : raw12103step3 = (fun i j => raw12103step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12103step3 raw12103step2; decide +kernel
      have hl : raw12103step3Labels = raw12103step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12103step2 raw12103step2Labels permutation7 permutation6
    _ = mixedMoment B node4019 node4019Labels := by rfl

def raw12104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12104step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12104step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, 1, -2]]
def raw12104step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12104step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw12104step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12104 raw12104Labels = mixedMoment B node4019 node4019Labels := by
  calc
    mixedMoment B raw12104 raw12104Labels = mixedMoment B raw12104step0 raw12104step0Labels := by
      have hz : ∀ j, raw12104 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12104step0 = (fun i j => raw12104 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12104step0 raw12104; decide +kernel
      have hl : raw12104step0Labels = raw12104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12104 raw12104Labels permutation520 hz
    mixedMoment B raw12104step0 raw12104step0Labels = mixedMoment B raw12104step1 raw12104step1Labels := by
      have hz : ∀ j, raw12104step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw12104step1 = (fun i j => raw12104step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw12104step1 raw12104step0; decide +kernel
      have hl : raw12104step1Labels = raw12104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12104step0 raw12104step0Labels permutation80 hz
    mixedMoment B raw12104step1 raw12104step1Labels = mixedMoment B raw12104step2 raw12104step2Labels := by
      have hz : ∀ j, raw12104step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw12104step2 = (fun i j => raw12104step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw12104step2 raw12104step1; decide +kernel
      have hl : raw12104step2Labels = raw12104step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12104step1 raw12104step1Labels permutation14 hz
    mixedMoment B raw12104step2 raw12104step2Labels = mixedMoment B raw12104step3 raw12104step3Labels := by
      have ha : raw12104step3 = (fun i j => raw12104step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12104step3 raw12104step2; decide +kernel
      have hl : raw12104step3Labels = raw12104step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12104step2 raw12104step2Labels permutation7 permutation6
    _ = mixedMoment B node4019 node4019Labels := by rfl

def raw12105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12105step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12105 raw12105Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw12105 raw12105Labels = mixedMoment B raw12105step0 raw12105step0Labels := by
      have hz : ∀ j, raw12105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12105step0 = (fun i j => raw12105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12105step0 raw12105; decide +kernel
      have hl : raw12105step0Labels = raw12105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12105 raw12105Labels permutation346 hz
    mixedMoment B raw12105step0 raw12105step0Labels = mixedMoment B raw12105step1 raw12105step1Labels := by
      have hz : ∀ j, raw12105step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12105step1 = (fun i j => raw12105step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12105step1 raw12105step0; decide +kernel
      have hl : raw12105step1Labels = raw12105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12105step0 raw12105step0Labels permutation56 hz
    mixedMoment B raw12105step1 raw12105step1Labels = mixedMoment B raw12105step2 raw12105step2Labels := by
      have ha : raw12105step2 = (fun i j => raw12105step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12105step2 raw12105step1; decide +kernel
      have hl : raw12105step2Labels = raw12105step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12105step1 raw12105step1Labels permutation29 permutation6
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw12106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12106 raw12106Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw12106 raw12106Labels = mixedMoment B raw12106step0 raw12106step0Labels := by
      have hz : ∀ j, raw12106 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12106step0 = (fun i j => raw12106 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12106step0 raw12106; decide +kernel
      have hl : raw12106step0Labels = raw12106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12106 raw12106Labels permutation346 hz
    mixedMoment B raw12106step0 raw12106step0Labels = mixedMoment B raw12106step1 raw12106step1Labels := by
      have ha : raw12106step1 = (fun i j => raw12106step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12106step1 raw12106step0; decide +kernel
      have hl : raw12106step1Labels = raw12106step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12106step0 raw12106step0Labels permutation50 permutation3
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw12107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12107 raw12107Labels = mixedMoment B node2953 node2953Labels := by
  calc
    mixedMoment B raw12107 raw12107Labels = mixedMoment B raw12107step0 raw12107step0Labels := by
      have ha : raw12107step0 = (fun i j => raw12107 (permutation194 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12107step0 raw12107; decide +kernel
      have hl : raw12107step0Labels = raw12107Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12107 raw12107Labels permutation194 permutation3
    _ = mixedMoment B node2953 node2953Labels := by rfl

def raw12108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12108step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12108step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12108step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12108 raw12108Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw12108 raw12108Labels = mixedMoment B raw12108step0 raw12108step0Labels := by
      have hz : ∀ j, raw12108 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12108step0 = (fun i j => raw12108 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12108step0 raw12108; decide +kernel
      have hl : raw12108step0Labels = raw12108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12108 raw12108Labels permutation434 hz
    mixedMoment B raw12108step0 raw12108step0Labels = mixedMoment B raw12108step1 raw12108step1Labels := by
      have hz : ∀ j, raw12108step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw12108step1 = (fun i j => raw12108step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw12108step1 raw12108step0; decide +kernel
      have hl : raw12108step1Labels = raw12108step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12108step0 raw12108step0Labels permutation80 hz
    mixedMoment B raw12108step1 raw12108step1Labels = mixedMoment B raw12108step2 raw12108step2Labels := by
      have ha : raw12108step2 = (fun i j => raw12108step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12108step2 raw12108step1; decide +kernel
      have hl : raw12108step2Labels = raw12108step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12108step1 raw12108step1Labels permutation12 permutation3
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw12109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12109step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12109 raw12109Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw12109 raw12109Labels = mixedMoment B raw12109step0 raw12109step0Labels := by
      have hz : ∀ j, raw12109 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12109step0 = (fun i j => raw12109 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12109step0 raw12109; decide +kernel
      have hl : raw12109step0Labels = raw12109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12109 raw12109Labels permutation520 hz
    mixedMoment B raw12109step0 raw12109step0Labels = mixedMoment B raw12109step1 raw12109step1Labels := by
      have hz : ∀ j, raw12109step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw12109step1 = (fun i j => raw12109step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw12109step1 raw12109step0; decide +kernel
      have hl : raw12109step1Labels = raw12109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12109step0 raw12109step0Labels permutation80 hz
    mixedMoment B raw12109step1 raw12109step1Labels = mixedMoment B raw12109step2 raw12109step2Labels := by
      have ha : raw12109step2 = (fun i j => raw12109step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12109step2 raw12109step1; decide +kernel
      have hl : raw12109step2Labels = raw12109step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12109step1 raw12109step1Labels permutation12 permutation3
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw12110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12110 raw12110Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw12110 raw12110Labels = mixedMoment B raw12110step0 raw12110step0Labels := by
      have hz : ∀ j, raw12110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12110step0 = (fun i j => raw12110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12110step0 raw12110; decide +kernel
      have hl : raw12110step0Labels = raw12110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12110 raw12110Labels permutation346 hz
    mixedMoment B raw12110step0 raw12110step0Labels = mixedMoment B raw12110step1 raw12110step1Labels := by
      have ha : raw12110step1 = (fun i j => raw12110step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12110step1 raw12110step0; decide +kernel
      have hl : raw12110step1Labels = raw12110step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12110step0 raw12110step0Labels permutation50 permutation3
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw12111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12111 raw12111Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw12111 raw12111Labels = mixedMoment B raw12111step0 raw12111step0Labels := by
      have hz : ∀ j, raw12111 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12111step0 = (fun i j => raw12111 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12111step0 raw12111; decide +kernel
      have hl : raw12111step0Labels = raw12111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12111 raw12111Labels permutation265 hz
    mixedMoment B raw12111step0 raw12111step0Labels = mixedMoment B raw12111step1 raw12111step1Labels := by
      have ha : raw12111step1 = (fun i j => raw12111step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12111step1 raw12111step0; decide +kernel
      have hl : raw12111step1Labels = raw12111step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12111step0 raw12111step0Labels permutation50 permutation3
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw12112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12112 raw12112Labels = mixedMoment B node2953 node2953Labels := by
  calc
    mixedMoment B raw12112 raw12112Labels = mixedMoment B raw12112step0 raw12112step0Labels := by
      have ha : raw12112step0 = (fun i j => raw12112 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12112step0 raw12112; decide +kernel
      have hl : raw12112step0Labels = raw12112Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12112 raw12112Labels permutation170 permutation3
    _ = mixedMoment B node2953 node2953Labels := by rfl

def raw12113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12113step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12113step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12113 raw12113Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw12113 raw12113Labels = mixedMoment B raw12113step0 raw12113step0Labels := by
      have hz : ∀ j, raw12113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12113step0 = (fun i j => raw12113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12113step0 raw12113; decide +kernel
      have hl : raw12113step0Labels = raw12113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12113 raw12113Labels permutation434 hz
    mixedMoment B raw12113step0 raw12113step0Labels = mixedMoment B raw12113step1 raw12113step1Labels := by
      have hz : ∀ j, raw12113step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12113step1 = (fun i j => raw12113step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12113step1 raw12113step0; decide +kernel
      have hl : raw12113step1Labels = raw12113step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12113step0 raw12113step0Labels permutation56 hz
    mixedMoment B raw12113step1 raw12113step1Labels = mixedMoment B raw12113step2 raw12113step2Labels := by
      have ha : raw12113step2 = (fun i j => raw12113step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12113step2 raw12113step1; decide +kernel
      have hl : raw12113step2Labels = raw12113step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12113step1 raw12113step1Labels permutation12 permutation3
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw12114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12114step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12114 raw12114Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw12114 raw12114Labels = mixedMoment B raw12114step0 raw12114step0Labels := by
      have hz : ∀ j, raw12114 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12114step0 = (fun i j => raw12114 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12114step0 raw12114; decide +kernel
      have hl : raw12114step0Labels = raw12114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12114 raw12114Labels permutation520 hz
    mixedMoment B raw12114step0 raw12114step0Labels = mixedMoment B raw12114step1 raw12114step1Labels := by
      have hz : ∀ j, raw12114step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12114step1 = (fun i j => raw12114step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12114step1 raw12114step0; decide +kernel
      have hl : raw12114step1Labels = raw12114step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12114step0 raw12114step0Labels permutation56 hz
    mixedMoment B raw12114step1 raw12114step1Labels = mixedMoment B raw12114step2 raw12114step2Labels := by
      have ha : raw12114step2 = (fun i j => raw12114step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12114step2 raw12114step1; decide +kernel
      have hl : raw12114step2Labels = raw12114step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12114step1 raw12114step1Labels permutation12 permutation3
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw12115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12115 raw12115Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw12115 raw12115Labels = mixedMoment B raw12115step0 raw12115step0Labels := by
      have hz : ∀ j, raw12115 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12115step0 = (fun i j => raw12115 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12115step0 raw12115; decide +kernel
      have hl : raw12115step0Labels = raw12115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12115 raw12115Labels permutation265 hz
    mixedMoment B raw12115step0 raw12115step0Labels = mixedMoment B raw12115step1 raw12115step1Labels := by
      have ha : raw12115step1 = (fun i j => raw12115step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12115step1 raw12115step0; decide +kernel
      have hl : raw12115step1Labels = raw12115step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12115step0 raw12115step0Labels permutation50 permutation3
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw12116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12116step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12116 raw12116Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw12116 raw12116Labels = mixedMoment B raw12116step0 raw12116step0Labels := by
      have hz : ∀ j, raw12116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12116step0 = (fun i j => raw12116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12116step0 raw12116; decide +kernel
      have hl : raw12116step0Labels = raw12116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12116 raw12116Labels permutation346 hz
    mixedMoment B raw12116step0 raw12116step0Labels = mixedMoment B raw12116step1 raw12116step1Labels := by
      have hz : ∀ j, raw12116step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12116step1 = (fun i j => raw12116step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12116step1 raw12116step0; decide +kernel
      have hl : raw12116step1Labels = raw12116step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12116step0 raw12116step0Labels permutation56 hz
    mixedMoment B raw12116step1 raw12116step1Labels = mixedMoment B raw12116step2 raw12116step2Labels := by
      have ha : raw12116step2 = (fun i j => raw12116step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12116step2 raw12116step1; decide +kernel
      have hl : raw12116step2Labels = raw12116step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12116step1 raw12116step1Labels permutation13 permutation3
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw12117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12117 raw12117Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw12117 raw12117Labels = mixedMoment B raw12117step0 raw12117step0Labels := by
      have hz : ∀ j, raw12117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12117step0 = (fun i j => raw12117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12117step0 raw12117; decide +kernel
      have hl : raw12117step0Labels = raw12117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12117 raw12117Labels permutation346 hz
    mixedMoment B raw12117step0 raw12117step0Labels = mixedMoment B raw12117step1 raw12117step1Labels := by
      have ha : raw12117step1 = (fun i j => raw12117step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12117step1 raw12117step0; decide +kernel
      have hl : raw12117step1Labels = raw12117step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12117step0 raw12117step0Labels permutation37 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw12118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12118 raw12118Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw12118 raw12118Labels = mixedMoment B raw12118step0 raw12118step0Labels := by
      have hz : ∀ j, raw12118 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12118step0 = (fun i j => raw12118 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12118step0 raw12118; decide +kernel
      have hl : raw12118step0Labels = raw12118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12118 raw12118Labels permutation265 hz
    mixedMoment B raw12118step0 raw12118step0Labels = mixedMoment B raw12118step1 raw12118step1Labels := by
      have ha : raw12118step1 = (fun i j => raw12118step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12118step1 raw12118step0; decide +kernel
      have hl : raw12118step1Labels = raw12118step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12118step0 raw12118step0Labels permutation37 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw12119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw12119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12119step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12119step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw12119step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12119step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw12119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12119 raw12119Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw12119 raw12119Labels = mixedMoment B raw12119step0 raw12119step0Labels := by
      have hz : ∀ j, raw12119 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12119step0 = (fun i j => raw12119 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12119step0 raw12119; decide +kernel
      have hl : raw12119step0Labels = raw12119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12119 raw12119Labels permutation520 hz
    mixedMoment B raw12119step0 raw12119step0Labels = mixedMoment B raw12119step1 raw12119step1Labels := by
      have hz : ∀ j, raw12119step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw12119step1 = (fun i j => raw12119step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw12119step1 raw12119step0; decide +kernel
      have hl : raw12119step1Labels = raw12119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12119step0 raw12119step0Labels permutation80 hz
    mixedMoment B raw12119step1 raw12119step1Labels = mixedMoment B raw12119step2 raw12119step2Labels := by
      have hz : ∀ j, raw12119step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw12119step2 = (fun i j => raw12119step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw12119step2 raw12119step1; decide +kernel
      have hl : raw12119step2Labels = raw12119step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12119step1 raw12119step1Labels permutation14 hz
    mixedMoment B raw12119step2 raw12119step2Labels = mixedMoment B raw12119step3 raw12119step3Labels := by
      have ha : raw12119step3 = (fun i j => raw12119step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12119step3 raw12119step2; decide +kernel
      have hl : raw12119step3Labels = raw12119step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12119step2 raw12119step2Labels permutation3 permutation3
    _ = mixedMoment B node3121 node3121Labels := by rfl

def raw12120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12120step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw12120step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12120 raw12120Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw12120 raw12120Labels = mixedMoment B raw12120step0 raw12120step0Labels := by
      have hz : ∀ j, raw12120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12120step0 = (fun i j => raw12120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12120step0 raw12120; decide +kernel
      have hl : raw12120step0Labels = raw12120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12120 raw12120Labels permutation346 hz
    mixedMoment B raw12120step0 raw12120step0Labels = mixedMoment B raw12120step1 raw12120step1Labels := by
      have hz : ∀ j, raw12120step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12120step1 = (fun i j => raw12120step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12120step1 raw12120step0; decide +kernel
      have hl : raw12120step1Labels = raw12120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12120step0 raw12120step0Labels permutation56 hz
    mixedMoment B raw12120step1 raw12120step1Labels = mixedMoment B raw12120step2 raw12120step2Labels := by
      have ha : raw12120step2 = (fun i j => raw12120step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12120step2 raw12120step1; decide +kernel
      have hl : raw12120step2Labels = raw12120step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12120step1 raw12120step1Labels permutation13 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw12121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12121step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12121step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12121 raw12121Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw12121 raw12121Labels = mixedMoment B raw12121step0 raw12121step0Labels := by
      have hz : ∀ j, raw12121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12121step0 = (fun i j => raw12121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12121step0 raw12121; decide +kernel
      have hl : raw12121step0Labels = raw12121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12121 raw12121Labels permutation346 hz
    mixedMoment B raw12121step0 raw12121step0Labels = mixedMoment B raw12121step1 raw12121step1Labels := by
      have hz : ∀ j, raw12121step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12121step1 = (fun i j => raw12121step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12121step1 raw12121step0; decide +kernel
      have hl : raw12121step1Labels = raw12121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12121step0 raw12121step0Labels permutation56 hz
    mixedMoment B raw12121step1 raw12121step1Labels = mixedMoment B raw12121step2 raw12121step2Labels := by
      have ha : raw12121step2 = (fun i j => raw12121step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12121step2 raw12121step1; decide +kernel
      have hl : raw12121step2Labels = raw12121step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12121step1 raw12121step1Labels permutation12 permutation3
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw12122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12122 raw12122Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw12122 raw12122Labels = mixedMoment B raw12122step0 raw12122step0Labels := by
      have hz : ∀ j, raw12122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12122step0 = (fun i j => raw12122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12122step0 raw12122; decide +kernel
      have hl : raw12122step0Labels = raw12122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12122 raw12122Labels permutation346 hz
    mixedMoment B raw12122step0 raw12122step0Labels = mixedMoment B raw12122step1 raw12122step1Labels := by
      have ha : raw12122step1 = (fun i j => raw12122step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12122step1 raw12122step0; decide +kernel
      have hl : raw12122step1Labels = raw12122step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12122step0 raw12122step0Labels permutation36 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw12123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12123 raw12123Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw12123 raw12123Labels = mixedMoment B raw12123step0 raw12123step0Labels := by
      have hz : ∀ j, raw12123 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12123step0 = (fun i j => raw12123 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12123step0 raw12123; decide +kernel
      have hl : raw12123step0Labels = raw12123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12123 raw12123Labels permutation265 hz
    mixedMoment B raw12123step0 raw12123step0Labels = mixedMoment B raw12123step1 raw12123step1Labels := by
      have ha : raw12123step1 = (fun i j => raw12123step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12123step1 raw12123step0; decide +kernel
      have hl : raw12123step1Labels = raw12123step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12123step0 raw12123step0Labels permutation36 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw12124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12124step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw12124step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12124step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw12124step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12124step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw12124step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12124 raw12124Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw12124 raw12124Labels = mixedMoment B raw12124step0 raw12124step0Labels := by
      have hz : ∀ j, raw12124 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12124step0 = (fun i j => raw12124 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12124step0 raw12124; decide +kernel
      have hl : raw12124step0Labels = raw12124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12124 raw12124Labels permutation434 hz
    mixedMoment B raw12124step0 raw12124step0Labels = mixedMoment B raw12124step1 raw12124step1Labels := by
      have hz : ∀ j, raw12124step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw12124step1 = (fun i j => raw12124step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw12124step1 raw12124step0; decide +kernel
      have hl : raw12124step1Labels = raw12124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12124step0 raw12124step0Labels permutation80 hz
    mixedMoment B raw12124step1 raw12124step1Labels = mixedMoment B raw12124step2 raw12124step2Labels := by
      have hz : ∀ j, raw12124step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw12124step2 = (fun i j => raw12124step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw12124step2 raw12124step1; decide +kernel
      have hl : raw12124step2Labels = raw12124step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12124step1 raw12124step1Labels permutation14 hz
    mixedMoment B raw12124step2 raw12124step2Labels = mixedMoment B raw12124step3 raw12124step3Labels := by
      have ha : raw12124step3 = (fun i j => raw12124step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12124step3 raw12124step2; decide +kernel
      have hl : raw12124step3Labels = raw12124step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12124step2 raw12124step2Labels permutation3 permutation3
    _ = mixedMoment B node3121 node3121Labels := by rfl

def raw12125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw12125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw12125step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw12125step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12125 raw12125Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw12125 raw12125Labels = mixedMoment B raw12125step0 raw12125step0Labels := by
      have hz : ∀ j, raw12125 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12125step0 = (fun i j => raw12125 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12125step0 raw12125; decide +kernel
      have hl : raw12125step0Labels = raw12125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12125 raw12125Labels permutation346 hz
    mixedMoment B raw12125step0 raw12125step0Labels = mixedMoment B raw12125step1 raw12125step1Labels := by
      have hz : ∀ j, raw12125step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12125step1 = (fun i j => raw12125step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12125step1 raw12125step0; decide +kernel
      have hl : raw12125step1Labels = raw12125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12125step0 raw12125step0Labels permutation56 hz
    mixedMoment B raw12125step1 raw12125step1Labels = mixedMoment B raw12125step2 raw12125step2Labels := by
      have ha : raw12125step2 = (fun i j => raw12125step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12125step2 raw12125step1; decide +kernel
      have hl : raw12125step2Labels = raw12125step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12125step1 raw12125step1Labels permutation12 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw12126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12126step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12126step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12126step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12126 raw12126Labels = mixedMoment B node1305 node1305Labels := by
  calc
    mixedMoment B raw12126 raw12126Labels = mixedMoment B raw12126step0 raw12126step0Labels := by
      have hz : ∀ j, raw12126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12126step0 = (fun i j => raw12126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12126step0 raw12126; decide +kernel
      have hl : raw12126step0Labels = raw12126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12126 raw12126Labels permutation346 hz
    mixedMoment B raw12126step0 raw12126step0Labels = mixedMoment B raw12126step1 raw12126step1Labels := by
      have hz : ∀ j, raw12126step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12126step1 = (fun i j => raw12126step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12126step1 raw12126step0; decide +kernel
      have hl : raw12126step1Labels = raw12126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12126step0 raw12126step0Labels permutation56 hz
    mixedMoment B raw12126step1 raw12126step1Labels = mixedMoment B raw12126step2 raw12126step2Labels := by
      have ha : raw12126step2 = (fun i j => raw12126step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12126step2 raw12126step1; decide +kernel
      have hl : raw12126step2Labels = raw12126step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12126step1 raw12126step1Labels permutation8 permutation3
    _ = mixedMoment B node1305 node1305Labels := by rfl

def raw12127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12127step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12127 raw12127Labels = mixedMoment B node2963 node2963Labels := by
  calc
    mixedMoment B raw12127 raw12127Labels = mixedMoment B raw12127step0 raw12127step0Labels := by
      have hz : ∀ j, raw12127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12127step0 = (fun i j => raw12127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12127step0 raw12127; decide +kernel
      have hl : raw12127step0Labels = raw12127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12127 raw12127Labels permutation346 hz
    mixedMoment B raw12127step0 raw12127step0Labels = mixedMoment B raw12127step1 raw12127step1Labels := by
      have ha : raw12127step1 = (fun i j => raw12127step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12127step1 raw12127step0; decide +kernel
      have hl : raw12127step1Labels = raw12127step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12127step0 raw12127step0Labels permutation32 permutation3
    _ = mixedMoment B node2963 node2963Labels := by rfl

def raw12128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12128Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12128step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12128step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12128 raw12128Labels = mixedMoment B node2963 node2963Labels := by
  calc
    mixedMoment B raw12128 raw12128Labels = mixedMoment B raw12128step0 raw12128step0Labels := by
      have hz : ∀ j, raw12128 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12128step0 = (fun i j => raw12128 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12128step0 raw12128; decide +kernel
      have hl : raw12128step0Labels = raw12128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12128 raw12128Labels permutation265 hz
    mixedMoment B raw12128step0 raw12128step0Labels = mixedMoment B raw12128step1 raw12128step1Labels := by
      have ha : raw12128step1 = (fun i j => raw12128step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12128step1 raw12128step0; decide +kernel
      have hl : raw12128step1Labels = raw12128step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12128step0 raw12128step0Labels permutation32 permutation3
    _ = mixedMoment B node2963 node2963Labels := by rfl

def raw12129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12129Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12129step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12129step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12129step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw12129step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12129step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw12129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12129 raw12129Labels = mixedMoment B node3124 node3124Labels := by
  calc
    mixedMoment B raw12129 raw12129Labels = mixedMoment B raw12129step0 raw12129step0Labels := by
      have hz : ∀ j, raw12129 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12129step0 = (fun i j => raw12129 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12129step0 raw12129; decide +kernel
      have hl : raw12129step0Labels = raw12129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12129 raw12129Labels permutation434 hz
    mixedMoment B raw12129step0 raw12129step0Labels = mixedMoment B raw12129step1 raw12129step1Labels := by
      have hz : ∀ j, raw12129step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw12129step1 = (fun i j => raw12129step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw12129step1 raw12129step0; decide +kernel
      have hl : raw12129step1Labels = raw12129step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12129step0 raw12129step0Labels permutation80 hz
    mixedMoment B raw12129step1 raw12129step1Labels = mixedMoment B raw12129step2 raw12129step2Labels := by
      have hz : ∀ j, raw12129step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw12129step2 = (fun i j => raw12129step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw12129step2 raw12129step1; decide +kernel
      have hl : raw12129step2Labels = raw12129step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12129step1 raw12129step1Labels permutation14 hz
    mixedMoment B raw12129step2 raw12129step2Labels = mixedMoment B raw12129step3 raw12129step3Labels := by
      have ha : raw12129step3 = (fun i j => raw12129step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12129step3 raw12129step2; decide +kernel
      have hl : raw12129step3Labels = raw12129step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12129step2 raw12129step2Labels permutation2 permutation3
    _ = mixedMoment B node3124 node3124Labels := by rfl

def raw12130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw12130Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12130step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12130step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12130step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw12130step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12130step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw12130step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12130 raw12130Labels = mixedMoment B node3124 node3124Labels := by
  calc
    mixedMoment B raw12130 raw12130Labels = mixedMoment B raw12130step0 raw12130step0Labels := by
      have hz : ∀ j, raw12130 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12130step0 = (fun i j => raw12130 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12130step0 raw12130; decide +kernel
      have hl : raw12130step0Labels = raw12130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12130 raw12130Labels permutation520 hz
    mixedMoment B raw12130step0 raw12130step0Labels = mixedMoment B raw12130step1 raw12130step1Labels := by
      have hz : ∀ j, raw12130step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw12130step1 = (fun i j => raw12130step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw12130step1 raw12130step0; decide +kernel
      have hl : raw12130step1Labels = raw12130step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12130step0 raw12130step0Labels permutation80 hz
    mixedMoment B raw12130step1 raw12130step1Labels = mixedMoment B raw12130step2 raw12130step2Labels := by
      have hz : ∀ j, raw12130step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw12130step2 = (fun i j => raw12130step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw12130step2 raw12130step1; decide +kernel
      have hl : raw12130step2Labels = raw12130step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12130step1 raw12130step1Labels permutation14 hz
    mixedMoment B raw12130step2 raw12130step2Labels = mixedMoment B raw12130step3 raw12130step3Labels := by
      have ha : raw12130step3 = (fun i j => raw12130step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12130step3 raw12130step2; decide +kernel
      have hl : raw12130step3Labels = raw12130step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12130step2 raw12130step2Labels permutation2 permutation3
    _ = mixedMoment B node3124 node3124Labels := by rfl

def raw12131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12131step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12131step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12131 raw12131Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw12131 raw12131Labels = mixedMoment B raw12131step0 raw12131step0Labels := by
      have hz : ∀ j, raw12131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12131step0 = (fun i j => raw12131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12131step0 raw12131; decide +kernel
      have hl : raw12131step0Labels = raw12131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12131 raw12131Labels permutation346 hz
    mixedMoment B raw12131step0 raw12131step0Labels = mixedMoment B raw12131step1 raw12131step1Labels := by
      have ha : raw12131step1 = (fun i j => raw12131step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12131step1 raw12131step0; decide +kernel
      have hl : raw12131step1Labels = raw12131step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12131step0 raw12131step0Labels permutation32 permutation3
    mixedMoment B raw12131step1 raw12131step1Labels = mixedMoment B raw12131step2 raw12131step2Labels := by
      have ha : raw12131step2 = raw12131step1 := by apply Matrix.ext; unfold raw12131step2 raw12131step1; decide +kernel
      have hl : raw12131step1Labels = labelEmbedding6 ∘ raw12131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12131step1 raw12131step1Labels raw12131step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw12132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12132step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12132 raw12132Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw12132 raw12132Labels = mixedMoment B raw12132step0 raw12132step0Labels := by
      have hz : ∀ j, raw12132 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12132step0 = (fun i j => raw12132 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12132step0 raw12132; decide +kernel
      have hl : raw12132step0Labels = raw12132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12132 raw12132Labels permutation265 hz
    mixedMoment B raw12132step0 raw12132step0Labels = mixedMoment B raw12132step1 raw12132step1Labels := by
      have ha : raw12132step1 = (fun i j => raw12132step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12132step1 raw12132step0; decide +kernel
      have hl : raw12132step1Labels = raw12132step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12132step0 raw12132step0Labels permutation32 permutation3
    mixedMoment B raw12132step1 raw12132step1Labels = mixedMoment B raw12132step2 raw12132step2Labels := by
      have ha : raw12132step2 = raw12132step1 := by apply Matrix.ext; unfold raw12132step2 raw12132step1; decide +kernel
      have hl : raw12132step1Labels = labelEmbedding6 ∘ raw12132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12132step1 raw12132step1Labels raw12132step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw12133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12133step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12133 raw12133Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw12133 raw12133Labels = mixedMoment B raw12133step0 raw12133step0Labels := by
      have hz : ∀ j, raw12133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12133step0 = (fun i j => raw12133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12133step0 raw12133; decide +kernel
      have hl : raw12133step0Labels = raw12133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12133 raw12133Labels permutation346 hz
    mixedMoment B raw12133step0 raw12133step0Labels = mixedMoment B raw12133step1 raw12133step1Labels := by
      have hz : ∀ j, raw12133step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12133step1 = (fun i j => raw12133step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12133step1 raw12133step0; decide +kernel
      have hl : raw12133step1Labels = raw12133step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12133step0 raw12133step0Labels permutation56 hz
    mixedMoment B raw12133step1 raw12133step1Labels = mixedMoment B raw12133step2 raw12133step2Labels := by
      have ha : raw12133step2 = (fun i j => raw12133step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12133step2 raw12133step1; decide +kernel
      have hl : raw12133step2Labels = raw12133step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12133step1 raw12133step1Labels permutation10 permutation3
    mixedMoment B raw12133step2 raw12133step2Labels = mixedMoment B raw12133step3 raw12133step3Labels := by
      have ha : raw12133step3 = raw12133step2 := by apply Matrix.ext; unfold raw12133step3 raw12133step2; decide +kernel
      have hl : raw12133step2Labels = labelEmbedding6 ∘ raw12133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12133step2 raw12133step2Labels raw12133step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw12134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12134 raw12134Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw12134 raw12134Labels = mixedMoment B raw12134step0 raw12134step0Labels := by
      have hz : ∀ j, raw12134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12134step0 = (fun i j => raw12134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12134step0 raw12134; decide +kernel
      have hl : raw12134step0Labels = raw12134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12134 raw12134Labels permutation346 hz
    mixedMoment B raw12134step0 raw12134step0Labels = mixedMoment B raw12134step1 raw12134step1Labels := by
      have hz : ∀ j, raw12134step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12134step1 = (fun i j => raw12134step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12134step1 raw12134step0; decide +kernel
      have hl : raw12134step1Labels = raw12134step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12134step0 raw12134step0Labels permutation56 hz
    mixedMoment B raw12134step1 raw12134step1Labels = mixedMoment B raw12134step2 raw12134step2Labels := by
      have ha : raw12134step2 = (fun i j => raw12134step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12134step2 raw12134step1; decide +kernel
      have hl : raw12134step2Labels = raw12134step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12134step1 raw12134step1Labels permutation12 permutation2
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw12135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12135step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12135step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12135 raw12135Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw12135 raw12135Labels = mixedMoment B raw12135step0 raw12135step0Labels := by
      have hz : ∀ j, raw12135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12135step0 = (fun i j => raw12135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12135step0 raw12135; decide +kernel
      have hl : raw12135step0Labels = raw12135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12135 raw12135Labels permutation346 hz
    mixedMoment B raw12135step0 raw12135step0Labels = mixedMoment B raw12135step1 raw12135step1Labels := by
      have ha : raw12135step1 = (fun i j => raw12135step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12135step1 raw12135step0; decide +kernel
      have hl : raw12135step1Labels = raw12135step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12135step0 raw12135step0Labels permutation40 permutation3
    mixedMoment B raw12135step1 raw12135step1Labels = mixedMoment B raw12135step2 raw12135step2Labels := by
      have ha : raw12135step2 = raw12135step1 := by apply Matrix.ext; unfold raw12135step2 raw12135step1; decide +kernel
      have hl : raw12135step1Labels = labelEmbedding6 ∘ raw12135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12135step1 raw12135step1Labels raw12135step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw12136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12136 raw12136Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw12136 raw12136Labels = mixedMoment B raw12136step0 raw12136step0Labels := by
      have ha : raw12136step0 = (fun i j => raw12136 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12136step0 raw12136; decide +kernel
      have hl : raw12136step0Labels = raw12136Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12136 raw12136Labels permutation184 permutation3
    mixedMoment B raw12136step0 raw12136step0Labels = mixedMoment B raw12136step1 raw12136step1Labels := by
      have ha : raw12136step1 = raw12136step0 := by apply Matrix.ext; unfold raw12136step1 raw12136step0; decide +kernel
      have hl : raw12136step0Labels = labelEmbedding6 ∘ raw12136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12136step0 raw12136step0Labels raw12136step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw12137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12137step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12137step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12137 raw12137Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12137 raw12137Labels = mixedMoment B raw12137step0 raw12137step0Labels := by
      have hz : ∀ j, raw12137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12137step0 = (fun i j => raw12137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12137step0 raw12137; decide +kernel
      have hl : raw12137step0Labels = raw12137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12137 raw12137Labels permutation346 hz
    mixedMoment B raw12137step0 raw12137step0Labels = mixedMoment B raw12137step1 raw12137step1Labels := by
      have ha : raw12137step1 = (fun i j => raw12137step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12137step1 raw12137step0; decide +kernel
      have hl : raw12137step1Labels = raw12137step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12137step0 raw12137step0Labels permutation46 permutation3
    mixedMoment B raw12137step1 raw12137step1Labels = mixedMoment B raw12137step2 raw12137step2Labels := by
      have ha : raw12137step2 = raw12137step1 := by apply Matrix.ext; unfold raw12137step2 raw12137step1; decide +kernel
      have hl : raw12137step1Labels = labelEmbedding6 ∘ raw12137step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12137step1 raw12137step1Labels raw12137step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw12138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12138step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12138step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12138 raw12138Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12138 raw12138Labels = mixedMoment B raw12138step0 raw12138step0Labels := by
      have hz : ∀ j, raw12138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12138step0 = (fun i j => raw12138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12138step0 raw12138; decide +kernel
      have hl : raw12138step0Labels = raw12138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12138 raw12138Labels permutation346 hz
    mixedMoment B raw12138step0 raw12138step0Labels = mixedMoment B raw12138step1 raw12138step1Labels := by
      have ha : raw12138step1 = (fun i j => raw12138step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12138step1 raw12138step0; decide +kernel
      have hl : raw12138step1Labels = raw12138step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12138step0 raw12138step0Labels permutation53 permutation3
    mixedMoment B raw12138step1 raw12138step1Labels = mixedMoment B raw12138step2 raw12138step2Labels := by
      have ha : raw12138step2 = raw12138step1 := by apply Matrix.ext; unfold raw12138step2 raw12138step1; decide +kernel
      have hl : raw12138step1Labels = labelEmbedding6 ∘ raw12138step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12138step1 raw12138step1Labels raw12138step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw12139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12139step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12139 raw12139Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw12139 raw12139Labels = mixedMoment B raw12139step0 raw12139step0Labels := by
      have hz : ∀ j, raw12139 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12139step0 = (fun i j => raw12139 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12139step0 raw12139; decide +kernel
      have hl : raw12139step0Labels = raw12139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12139 raw12139Labels permutation265 hz
    mixedMoment B raw12139step0 raw12139step0Labels = mixedMoment B raw12139step1 raw12139step1Labels := by
      have ha : raw12139step1 = (fun i j => raw12139step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12139step1 raw12139step0; decide +kernel
      have hl : raw12139step1Labels = raw12139step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12139step0 raw12139step0Labels permutation40 permutation3
    mixedMoment B raw12139step1 raw12139step1Labels = mixedMoment B raw12139step2 raw12139step2Labels := by
      have ha : raw12139step2 = raw12139step1 := by apply Matrix.ext; unfold raw12139step2 raw12139step1; decide +kernel
      have hl : raw12139step1Labels = labelEmbedding6 ∘ raw12139step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12139step1 raw12139step1Labels raw12139step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw12140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12140step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12140 raw12140Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw12140 raw12140Labels = mixedMoment B raw12140step0 raw12140step0Labels := by
      have ha : raw12140step0 = (fun i j => raw12140 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12140step0 raw12140; decide +kernel
      have hl : raw12140step0Labels = raw12140Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12140 raw12140Labels permutation160 permutation3
    mixedMoment B raw12140step0 raw12140step0Labels = mixedMoment B raw12140step1 raw12140step1Labels := by
      have ha : raw12140step1 = raw12140step0 := by apply Matrix.ext; unfold raw12140step1 raw12140step0; decide +kernel
      have hl : raw12140step0Labels = labelEmbedding6 ∘ raw12140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12140step0 raw12140step0Labels raw12140step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw12141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12141step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12141step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12141 raw12141Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12141 raw12141Labels = mixedMoment B raw12141step0 raw12141step0Labels := by
      have hz : ∀ j, raw12141 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12141step0 = (fun i j => raw12141 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12141step0 raw12141; decide +kernel
      have hl : raw12141step0Labels = raw12141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12141 raw12141Labels permutation265 hz
    mixedMoment B raw12141step0 raw12141step0Labels = mixedMoment B raw12141step1 raw12141step1Labels := by
      have ha : raw12141step1 = (fun i j => raw12141step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12141step1 raw12141step0; decide +kernel
      have hl : raw12141step1Labels = raw12141step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12141step0 raw12141step0Labels permutation46 permutation3
    mixedMoment B raw12141step1 raw12141step1Labels = mixedMoment B raw12141step2 raw12141step2Labels := by
      have ha : raw12141step2 = raw12141step1 := by apply Matrix.ext; unfold raw12141step2 raw12141step1; decide +kernel
      have hl : raw12141step1Labels = labelEmbedding6 ∘ raw12141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12141step1 raw12141step1Labels raw12141step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw12142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12142step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12142 raw12142Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12142 raw12142Labels = mixedMoment B raw12142step0 raw12142step0Labels := by
      have hz : ∀ j, raw12142 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12142step0 = (fun i j => raw12142 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12142step0 raw12142; decide +kernel
      have hl : raw12142step0Labels = raw12142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12142 raw12142Labels permutation265 hz
    mixedMoment B raw12142step0 raw12142step0Labels = mixedMoment B raw12142step1 raw12142step1Labels := by
      have ha : raw12142step1 = (fun i j => raw12142step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12142step1 raw12142step0; decide +kernel
      have hl : raw12142step1Labels = raw12142step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12142step0 raw12142step0Labels permutation53 permutation3
    mixedMoment B raw12142step1 raw12142step1Labels = mixedMoment B raw12142step2 raw12142step2Labels := by
      have ha : raw12142step2 = raw12142step1 := by apply Matrix.ext; unfold raw12142step2 raw12142step1; decide +kernel
      have hl : raw12142step1Labels = labelEmbedding6 ∘ raw12142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12142step1 raw12142step1Labels raw12142step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw12143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12143step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12143step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12143step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12143step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12143step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12143 raw12143Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw12143 raw12143Labels = mixedMoment B raw12143step0 raw12143step0Labels := by
      have hz : ∀ j, raw12143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12143step0 = (fun i j => raw12143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12143step0 raw12143; decide +kernel
      have hl : raw12143step0Labels = raw12143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12143 raw12143Labels permutation346 hz
    mixedMoment B raw12143step0 raw12143step0Labels = mixedMoment B raw12143step1 raw12143step1Labels := by
      have hz : ∀ j, raw12143step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12143step1 = (fun i j => raw12143step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12143step1 raw12143step0; decide +kernel
      have hl : raw12143step1Labels = raw12143step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12143step0 raw12143step0Labels permutation56 hz
    mixedMoment B raw12143step1 raw12143step1Labels = mixedMoment B raw12143step2 raw12143step2Labels := by
      have ha : raw12143step2 = (fun i j => raw12143step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12143step2 raw12143step1; decide +kernel
      have hl : raw12143step2Labels = raw12143step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12143step1 raw12143step1Labels permutation11 permutation3
    mixedMoment B raw12143step2 raw12143step2Labels = mixedMoment B raw12143step3 raw12143step3Labels := by
      have ha : raw12143step3 = raw12143step2 := by apply Matrix.ext; unfold raw12143step3 raw12143step2; decide +kernel
      have hl : raw12143step2Labels = labelEmbedding6 ∘ raw12143step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12143step2 raw12143step2Labels raw12143step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw12144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12144step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12144 raw12144Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw12144 raw12144Labels = mixedMoment B raw12144step0 raw12144step0Labels := by
      have hz : ∀ j, raw12144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12144step0 = (fun i j => raw12144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12144step0 raw12144; decide +kernel
      have hl : raw12144step0Labels = raw12144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12144 raw12144Labels permutation346 hz
    mixedMoment B raw12144step0 raw12144step0Labels = mixedMoment B raw12144step1 raw12144step1Labels := by
      have ha : raw12144step1 = (fun i j => raw12144step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12144step1 raw12144step0; decide +kernel
      have hl : raw12144step1Labels = raw12144step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12144step0 raw12144step0Labels permutation35 permutation3
    mixedMoment B raw12144step1 raw12144step1Labels = mixedMoment B raw12144step2 raw12144step2Labels := by
      have ha : raw12144step2 = raw12144step1 := by apply Matrix.ext; unfold raw12144step2 raw12144step1; decide +kernel
      have hl : raw12144step1Labels = labelEmbedding6 ∘ raw12144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12144step1 raw12144step1Labels raw12144step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw12145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12145step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12145step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12145 raw12145Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw12145 raw12145Labels = mixedMoment B raw12145step0 raw12145step0Labels := by
      have hz : ∀ j, raw12145 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12145step0 = (fun i j => raw12145 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12145step0 raw12145; decide +kernel
      have hl : raw12145step0Labels = raw12145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12145 raw12145Labels permutation265 hz
    mixedMoment B raw12145step0 raw12145step0Labels = mixedMoment B raw12145step1 raw12145step1Labels := by
      have ha : raw12145step1 = (fun i j => raw12145step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12145step1 raw12145step0; decide +kernel
      have hl : raw12145step1Labels = raw12145step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12145step0 raw12145step0Labels permutation35 permutation3
    mixedMoment B raw12145step1 raw12145step1Labels = mixedMoment B raw12145step2 raw12145step2Labels := by
      have ha : raw12145step2 = raw12145step1 := by apply Matrix.ext; unfold raw12145step2 raw12145step1; decide +kernel
      have hl : raw12145step1Labels = labelEmbedding6 ∘ raw12145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12145step1 raw12145step1Labels raw12145step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw12146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12146step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12146step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12146step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12146 raw12146Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw12146 raw12146Labels = mixedMoment B raw12146step0 raw12146step0Labels := by
      have hz : ∀ j, raw12146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12146step0 = (fun i j => raw12146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12146step0 raw12146; decide +kernel
      have hl : raw12146step0Labels = raw12146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12146 raw12146Labels permutation346 hz
    mixedMoment B raw12146step0 raw12146step0Labels = mixedMoment B raw12146step1 raw12146step1Labels := by
      have hz : ∀ j, raw12146step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12146step1 = (fun i j => raw12146step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12146step1 raw12146step0; decide +kernel
      have hl : raw12146step1Labels = raw12146step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12146step0 raw12146step0Labels permutation56 hz
    mixedMoment B raw12146step1 raw12146step1Labels = mixedMoment B raw12146step2 raw12146step2Labels := by
      have ha : raw12146step2 = (fun i j => raw12146step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12146step2 raw12146step1; decide +kernel
      have hl : raw12146step2Labels = raw12146step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12146step1 raw12146step1Labels permutation11 permutation3
    mixedMoment B raw12146step2 raw12146step2Labels = mixedMoment B raw12146step3 raw12146step3Labels := by
      have ha : raw12146step3 = raw12146step2 := by apply Matrix.ext; unfold raw12146step3 raw12146step2; decide +kernel
      have hl : raw12146step2Labels = labelEmbedding6 ∘ raw12146step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12146step2 raw12146step2Labels raw12146step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw12147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12147step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12147step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12147step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12147step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12147 raw12147Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw12147 raw12147Labels = mixedMoment B raw12147step0 raw12147step0Labels := by
      have hz : ∀ j, raw12147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12147step0 = (fun i j => raw12147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12147step0 raw12147; decide +kernel
      have hl : raw12147step0Labels = raw12147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12147 raw12147Labels permutation346 hz
    mixedMoment B raw12147step0 raw12147step0Labels = mixedMoment B raw12147step1 raw12147step1Labels := by
      have hz : ∀ j, raw12147step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12147step1 = (fun i j => raw12147step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12147step1 raw12147step0; decide +kernel
      have hl : raw12147step1Labels = raw12147step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12147step0 raw12147step0Labels permutation56 hz
    mixedMoment B raw12147step1 raw12147step1Labels = mixedMoment B raw12147step2 raw12147step2Labels := by
      have ha : raw12147step2 = (fun i j => raw12147step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12147step2 raw12147step1; decide +kernel
      have hl : raw12147step2Labels = raw12147step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12147step1 raw12147step1Labels permutation13 permutation3
    mixedMoment B raw12147step2 raw12147step2Labels = mixedMoment B raw12147step3 raw12147step3Labels := by
      have ha : raw12147step3 = raw12147step2 := by apply Matrix.ext; unfold raw12147step3 raw12147step2; decide +kernel
      have hl : raw12147step2Labels = labelEmbedding6 ∘ raw12147step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12147step2 raw12147step2Labels raw12147step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw12148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12148step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12148step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12148step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12148step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12148 raw12148Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw12148 raw12148Labels = mixedMoment B raw12148step0 raw12148step0Labels := by
      have hz : ∀ j, raw12148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12148step0 = (fun i j => raw12148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12148step0 raw12148; decide +kernel
      have hl : raw12148step0Labels = raw12148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12148 raw12148Labels permutation346 hz
    mixedMoment B raw12148step0 raw12148step0Labels = mixedMoment B raw12148step1 raw12148step1Labels := by
      have hz : ∀ j, raw12148step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12148step1 = (fun i j => raw12148step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12148step1 raw12148step0; decide +kernel
      have hl : raw12148step1Labels = raw12148step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12148step0 raw12148step0Labels permutation56 hz
    mixedMoment B raw12148step1 raw12148step1Labels = mixedMoment B raw12148step2 raw12148step2Labels := by
      have ha : raw12148step2 = (fun i j => raw12148step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12148step2 raw12148step1; decide +kernel
      have hl : raw12148step2Labels = raw12148step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12148step1 raw12148step1Labels permutation9 permutation3
    mixedMoment B raw12148step2 raw12148step2Labels = mixedMoment B raw12148step3 raw12148step3Labels := by
      have ha : raw12148step3 = raw12148step2 := by apply Matrix.ext; unfold raw12148step3 raw12148step2; decide +kernel
      have hl : raw12148step2Labels = labelEmbedding6 ∘ raw12148step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12148step2 raw12148step2Labels raw12148step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw12149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12149step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12149 raw12149Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw12149 raw12149Labels = mixedMoment B raw12149step0 raw12149step0Labels := by
      have hz : ∀ j, raw12149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12149step0 = (fun i j => raw12149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12149step0 raw12149; decide +kernel
      have hl : raw12149step0Labels = raw12149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12149 raw12149Labels permutation346 hz
    mixedMoment B raw12149step0 raw12149step0Labels = mixedMoment B raw12149step1 raw12149step1Labels := by
      have ha : raw12149step1 = (fun i j => raw12149step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12149step1 raw12149step0; decide +kernel
      have hl : raw12149step1Labels = raw12149step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12149step0 raw12149step0Labels permutation33 permutation3
    mixedMoment B raw12149step1 raw12149step1Labels = mixedMoment B raw12149step2 raw12149step2Labels := by
      have ha : raw12149step2 = raw12149step1 := by apply Matrix.ext; unfold raw12149step2 raw12149step1; decide +kernel
      have hl : raw12149step1Labels = labelEmbedding6 ∘ raw12149step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12149step1 raw12149step1Labels raw12149step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw12150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12150step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12150 raw12150Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw12150 raw12150Labels = mixedMoment B raw12150step0 raw12150step0Labels := by
      have hz : ∀ j, raw12150 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12150step0 = (fun i j => raw12150 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12150step0 raw12150; decide +kernel
      have hl : raw12150step0Labels = raw12150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12150 raw12150Labels permutation265 hz
    mixedMoment B raw12150step0 raw12150step0Labels = mixedMoment B raw12150step1 raw12150step1Labels := by
      have ha : raw12150step1 = (fun i j => raw12150step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12150step1 raw12150step0; decide +kernel
      have hl : raw12150step1Labels = raw12150step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12150step0 raw12150step0Labels permutation33 permutation3
    mixedMoment B raw12150step1 raw12150step1Labels = mixedMoment B raw12150step2 raw12150step2Labels := by
      have ha : raw12150step2 = raw12150step1 := by apply Matrix.ext; unfold raw12150step2 raw12150step1; decide +kernel
      have hl : raw12150step1Labels = labelEmbedding6 ∘ raw12150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12150step1 raw12150step1Labels raw12150step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw12151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw12151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw12151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw12151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12151step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12151step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12151step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12151step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12151 raw12151Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw12151 raw12151Labels = mixedMoment B raw12151step0 raw12151step0Labels := by
      have hz : ∀ j, raw12151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12151step0 = (fun i j => raw12151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12151step0 raw12151; decide +kernel
      have hl : raw12151step0Labels = raw12151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12151 raw12151Labels permutation346 hz
    mixedMoment B raw12151step0 raw12151step0Labels = mixedMoment B raw12151step1 raw12151step1Labels := by
      have hz : ∀ j, raw12151step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12151step1 = (fun i j => raw12151step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12151step1 raw12151step0; decide +kernel
      have hl : raw12151step1Labels = raw12151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12151step0 raw12151step0Labels permutation56 hz
    mixedMoment B raw12151step1 raw12151step1Labels = mixedMoment B raw12151step2 raw12151step2Labels := by
      have ha : raw12151step2 = (fun i j => raw12151step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12151step2 raw12151step1; decide +kernel
      have hl : raw12151step2Labels = raw12151step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12151step1 raw12151step1Labels permutation12 permutation3
    mixedMoment B raw12151step2 raw12151step2Labels = mixedMoment B raw12151step3 raw12151step3Labels := by
      have ha : raw12151step3 = raw12151step2 := by apply Matrix.ext; unfold raw12151step3 raw12151step2; decide +kernel
      have hl : raw12151step2Labels = labelEmbedding6 ∘ raw12151step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12151step2 raw12151step2Labels raw12151step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw12152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12152step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12152step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12152step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12152 raw12152Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw12152 raw12152Labels = mixedMoment B raw12152step0 raw12152step0Labels := by
      have hz : ∀ j, raw12152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12152step0 = (fun i j => raw12152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12152step0 raw12152; decide +kernel
      have hl : raw12152step0Labels = raw12152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12152 raw12152Labels permutation346 hz
    mixedMoment B raw12152step0 raw12152step0Labels = mixedMoment B raw12152step1 raw12152step1Labels := by
      have hz : ∀ j, raw12152step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12152step1 = (fun i j => raw12152step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12152step1 raw12152step0; decide +kernel
      have hl : raw12152step1Labels = raw12152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12152step0 raw12152step0Labels permutation56 hz
    mixedMoment B raw12152step1 raw12152step1Labels = mixedMoment B raw12152step2 raw12152step2Labels := by
      have ha : raw12152step2 = (fun i j => raw12152step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12152step2 raw12152step1; decide +kernel
      have hl : raw12152step2Labels = raw12152step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12152step1 raw12152step1Labels permutation8 permutation3
    mixedMoment B raw12152step2 raw12152step2Labels = mixedMoment B raw12152step3 raw12152step3Labels := by
      have ha : raw12152step3 = raw12152step2 := by apply Matrix.ext; unfold raw12152step3 raw12152step2; decide +kernel
      have hl : raw12152step2Labels = labelEmbedding6 ∘ raw12152step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12152step2 raw12152step2Labels raw12152step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw12153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12153step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12153 raw12153Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw12153 raw12153Labels = mixedMoment B raw12153step0 raw12153step0Labels := by
      have hz : ∀ j, raw12153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12153step0 = (fun i j => raw12153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12153step0 raw12153; decide +kernel
      have hl : raw12153step0Labels = raw12153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12153 raw12153Labels permutation346 hz
    mixedMoment B raw12153step0 raw12153step0Labels = mixedMoment B raw12153step1 raw12153step1Labels := by
      have ha : raw12153step1 = (fun i j => raw12153step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12153step1 raw12153step0; decide +kernel
      have hl : raw12153step1Labels = raw12153step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12153step0 raw12153step0Labels permutation32 permutation3
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw12154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12154step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12154 raw12154Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw12154 raw12154Labels = mixedMoment B raw12154step0 raw12154step0Labels := by
      have hz : ∀ j, raw12154 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12154step0 = (fun i j => raw12154 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12154step0 raw12154; decide +kernel
      have hl : raw12154step0Labels = raw12154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12154 raw12154Labels permutation265 hz
    mixedMoment B raw12154step0 raw12154step0Labels = mixedMoment B raw12154step1 raw12154step1Labels := by
      have ha : raw12154step1 = (fun i j => raw12154step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12154step1 raw12154step0; decide +kernel
      have hl : raw12154step1Labels = raw12154step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12154step0 raw12154step0Labels permutation32 permutation3
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw12155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12155step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12155step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12155step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12155step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12155 raw12155Labels = mixedMoment B node4015 node4015Labels := by
  calc
    mixedMoment B raw12155 raw12155Labels = mixedMoment B raw12155step0 raw12155step0Labels := by
      have hz : ∀ j, raw12155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12155step0 = (fun i j => raw12155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12155step0 raw12155; decide +kernel
      have hl : raw12155step0Labels = raw12155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12155 raw12155Labels permutation346 hz
    mixedMoment B raw12155step0 raw12155step0Labels = mixedMoment B raw12155step1 raw12155step1Labels := by
      have hz : ∀ j, raw12155step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12155step1 = (fun i j => raw12155step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12155step1 raw12155step0; decide +kernel
      have hl : raw12155step1Labels = raw12155step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12155step0 raw12155step0Labels permutation56 hz
    mixedMoment B raw12155step1 raw12155step1Labels = mixedMoment B raw12155step2 raw12155step2Labels := by
      have ha : raw12155step2 = (fun i j => raw12155step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12155step2 raw12155step1; decide +kernel
      have hl : raw12155step2Labels = raw12155step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12155step1 raw12155step1Labels permutation8 permutation3
    _ = mixedMoment B node4015 node4015Labels := by rfl

def raw12156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12156step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12156step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12156 raw12156Labels = mixedMoment B node4015 node4015Labels := by
  calc
    mixedMoment B raw12156 raw12156Labels = mixedMoment B raw12156step0 raw12156step0Labels := by
      have hz : ∀ j, raw12156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12156step0 = (fun i j => raw12156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12156step0 raw12156; decide +kernel
      have hl : raw12156step0Labels = raw12156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12156 raw12156Labels permutation346 hz
    mixedMoment B raw12156step0 raw12156step0Labels = mixedMoment B raw12156step1 raw12156step1Labels := by
      have hz : ∀ j, raw12156step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12156step1 = (fun i j => raw12156step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12156step1 raw12156step0; decide +kernel
      have hl : raw12156step1Labels = raw12156step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12156step0 raw12156step0Labels permutation56 hz
    mixedMoment B raw12156step1 raw12156step1Labels = mixedMoment B raw12156step2 raw12156step2Labels := by
      have ha : raw12156step2 = (fun i j => raw12156step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12156step2 raw12156step1; decide +kernel
      have hl : raw12156step2Labels = raw12156step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12156step1 raw12156step1Labels permutation10 permutation3
    _ = mixedMoment B node4015 node4015Labels := by rfl

def raw12157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12157step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12157step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw12157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12157 raw12157Labels = mixedMoment B node4018 node4018Labels := by
  calc
    mixedMoment B raw12157 raw12157Labels = mixedMoment B raw12157step0 raw12157step0Labels := by
      have hz : ∀ j, raw12157 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12157step0 = (fun i j => raw12157 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12157step0 raw12157; decide +kernel
      have hl : raw12157step0Labels = raw12157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12157 raw12157Labels permutation346 hz
    mixedMoment B raw12157step0 raw12157step0Labels = mixedMoment B raw12157step1 raw12157step1Labels := by
      have hz : ∀ j, raw12157step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12157step1 = (fun i j => raw12157step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12157step1 raw12157step0; decide +kernel
      have hl : raw12157step1Labels = raw12157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12157step0 raw12157step0Labels permutation56 hz
    mixedMoment B raw12157step1 raw12157step1Labels = mixedMoment B raw12157step2 raw12157step2Labels := by
      have ha : raw12157step2 = (fun i j => raw12157step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12157step2 raw12157step1; decide +kernel
      have hl : raw12157step2Labels = raw12157step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12157step1 raw12157step1Labels permutation12 permutation3
    _ = mixedMoment B node4018 node4018Labels := by rfl

def raw12158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12158 raw12158Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw12158 raw12158Labels = mixedMoment B raw12158step0 raw12158step0Labels := by
      have hz : ∀ j, raw12158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12158step0 = (fun i j => raw12158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12158step0 raw12158; decide +kernel
      have hl : raw12158step0Labels = raw12158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12158 raw12158Labels permutation346 hz
    mixedMoment B raw12158step0 raw12158step0Labels = mixedMoment B raw12158step1 raw12158step1Labels := by
      have ha : raw12158step1 = (fun i j => raw12158step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12158step1 raw12158step0; decide +kernel
      have hl : raw12158step1Labels = raw12158step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12158step0 raw12158step0Labels permutation40 permutation3
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw12159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12159step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12159 raw12159Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw12159 raw12159Labels = mixedMoment B raw12159step0 raw12159step0Labels := by
      have ha : raw12159step0 = (fun i j => raw12159 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12159step0 raw12159; decide +kernel
      have hl : raw12159step0Labels = raw12159Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12159 raw12159Labels permutation184 permutation3
    _ = mixedMoment B node2508 node2508Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
