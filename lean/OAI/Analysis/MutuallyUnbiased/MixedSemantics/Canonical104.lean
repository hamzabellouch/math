import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13312 raw13312Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw13312 raw13312Labels = mixedMoment B raw13312step0 raw13312step0Labels := by
      have ha : raw13312step0 = (fun i j => raw13312 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13312step0 raw13312; decide +kernel
      have hl : raw13312step0Labels = raw13312Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13312 raw13312Labels permutation157 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw13313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13313 raw13313Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw13313 raw13313Labels = mixedMoment B raw13313step0 raw13313step0Labels := by
      have ha : raw13313step0 = (fun i j => raw13313 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13313step0 raw13313; decide +kernel
      have hl : raw13313step0Labels = raw13313Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13313 raw13313Labels permutation156 permutation2
    _ = mixedMoment B node2925 node2925Labels := by rfl

def raw13314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13314 raw13314Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw13314 raw13314Labels = mixedMoment B raw13314step0 raw13314step0Labels := by
      have ha : raw13314step0 = (fun i j => raw13314 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13314step0 raw13314; decide +kernel
      have hl : raw13314step0Labels = raw13314Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13314 raw13314Labels permutation154 permutation2
    _ = mixedMoment B node2928 node2928Labels := by rfl

def raw13315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13315 raw13315Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw13315 raw13315Labels = mixedMoment B raw13315step0 raw13315step0Labels := by
      have ha : raw13315step0 = (fun i j => raw13315 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13315step0 raw13315; decide +kernel
      have hl : raw13315step0Labels = raw13315Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13315 raw13315Labels permutation183 permutation2
    _ = mixedMoment B node3091 node3091Labels := by rfl

def raw13316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13316 raw13316Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw13316 raw13316Labels = mixedMoment B raw13316step0 raw13316step0Labels := by
      have ha : raw13316step0 = (fun i j => raw13316 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13316step0 raw13316; decide +kernel
      have hl : raw13316step0Labels = raw13316Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13316 raw13316Labels permutation159 permutation2
    _ = mixedMoment B node3091 node3091Labels := by rfl

def raw13317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13317 raw13317Labels = mixedMoment B node3068 node3068Labels := by
  calc
    mixedMoment B raw13317 raw13317Labels = mixedMoment B raw13317step0 raw13317step0Labels := by
      have ha : raw13317step0 = (fun i j => raw13317 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13317step0 raw13317; decide +kernel
      have hl : raw13317step0Labels = raw13317Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13317 raw13317Labels permutation153 permutation2
    _ = mixedMoment B node3068 node3068Labels := by rfl

def raw13318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13318 raw13318Labels = mixedMoment B node3069 node3069Labels := by
  calc
    _ = mixedMoment B node3069 node3069Labels := by rfl

def raw13319 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13319step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13319step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13319 raw13319Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw13319 raw13319Labels = mixedMoment B raw13319step0 raw13319step0Labels := by
      have hz : ∀ j, raw13319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13319step0 = (fun i j => raw13319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13319step0 raw13319; decide +kernel
      have hl : raw13319step0Labels = raw13319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13319 raw13319Labels permutation346 hz
    mixedMoment B raw13319step0 raw13319step0Labels = mixedMoment B raw13319step1 raw13319step1Labels := by
      have ha : raw13319step1 = (fun i j => raw13319step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13319step1 raw13319step0; decide +kernel
      have hl : raw13319step1Labels = raw13319step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13319step0 raw13319step0Labels permutation37 permutation7
    mixedMoment B raw13319step1 raw13319step1Labels = mixedMoment B raw13319step2 raw13319step2Labels := by
      have ha : raw13319step2 = raw13319step1 := by apply Matrix.ext; unfold raw13319step2 raw13319step1; decide +kernel
      have hl : raw13319step1Labels = labelEmbedding10 ∘ raw13319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13319step1 raw13319step1Labels raw13319step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw13320 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13320step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13320 raw13320Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw13320 raw13320Labels = mixedMoment B raw13320step0 raw13320step0Labels := by
      have ha : raw13320step0 = (fun i j => raw13320 (permutation502 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13320step0 raw13320; decide +kernel
      have hl : raw13320step0Labels = raw13320Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13320 raw13320Labels permutation502 permutation3
    mixedMoment B raw13320step0 raw13320step0Labels = mixedMoment B raw13320step1 raw13320step1Labels := by
      have ha : raw13320step1 = raw13320step0 := by apply Matrix.ext; unfold raw13320step1 raw13320step0; decide +kernel
      have hl : raw13320step0Labels = labelEmbedding6 ∘ raw13320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13320step0 raw13320step0Labels raw13320step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw13321 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw13321step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw13321step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13321 raw13321Labels = mixedMoment B node5246 node5246Labels := by
  calc
    mixedMoment B raw13321 raw13321Labels = mixedMoment B raw13321step0 raw13321step0Labels := by
      have ha : raw13321step0 = (fun i j => raw13321 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13321step0 raw13321; decide +kernel
      have hl : raw13321step0Labels = raw13321Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13321 raw13321Labels permutation156 permutation7
    mixedMoment B raw13321step0 raw13321step0Labels = mixedMoment B raw13321step1 raw13321step1Labels := by
      have ha : raw13321step1 = raw13321step0 := by apply Matrix.ext; unfold raw13321step1 raw13321step0; decide +kernel
      have hl : raw13321step0Labels = labelEmbedding10 ∘ raw13321step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13321step0 raw13321step0Labels raw13321step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5246 node5246Labels := by rfl

def raw13322 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13322step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13322 raw13322Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw13322 raw13322Labels = mixedMoment B raw13322step0 raw13322step0Labels := by
      have ha : raw13322step0 = (fun i j => raw13322 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13322step0 raw13322; decide +kernel
      have hl : raw13322step0Labels = raw13322Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13322 raw13322Labels permutation155 permutation7
    mixedMoment B raw13322step0 raw13322step0Labels = mixedMoment B raw13322step1 raw13322step1Labels := by
      have ha : raw13322step1 = raw13322step0 := by apply Matrix.ext; unfold raw13322step1 raw13322step0; decide +kernel
      have hl : raw13322step0Labels = labelEmbedding10 ∘ raw13322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13322step0 raw13322step0Labels raw13322step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

def raw13323 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw13323step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13323step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13323step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13323 raw13323Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw13323 raw13323Labels = mixedMoment B raw13323step0 raw13323step0Labels := by
      have ha : raw13323step0 = (fun i j => raw13323 (permutation215 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13323step0 raw13323; decide +kernel
      have hl : raw13323step0Labels = raw13323Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13323 raw13323Labels permutation215 permutation4
    mixedMoment B raw13323step0 raw13323step0Labels = mixedMoment B raw13323step1 raw13323step1Labels := by
      have ha : raw13323step1 = -raw13323step0 := by apply Matrix.ext; change ∀ i j, raw13323step1 i j = -(raw13323step0 i j); unfold raw13323step1 raw13323step0; decide +kernel
      have hl : raw13323step1Labels = raw13323step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13323step1 raw13323step1Labels = mixedMoment B raw13323step2 raw13323step2Labels := by
      have ha : raw13323step2 = raw13323step1 := by apply Matrix.ext; unfold raw13323step2 raw13323step1; decide +kernel
      have hl : raw13323step1Labels = labelEmbedding7 ∘ raw13323step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13323step1 raw13323step1Labels raw13323step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw13324 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13324step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13324step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13324 raw13324Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw13324 raw13324Labels = mixedMoment B raw13324step0 raw13324step0Labels := by
      have hz : ∀ j, raw13324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13324step0 = (fun i j => raw13324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13324step0 raw13324; decide +kernel
      have hl : raw13324step0Labels = raw13324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13324 raw13324Labels permutation346 hz
    mixedMoment B raw13324step0 raw13324step0Labels = mixedMoment B raw13324step1 raw13324step1Labels := by
      have ha : raw13324step1 = (fun i j => raw13324step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13324step1 raw13324step0; decide +kernel
      have hl : raw13324step1Labels = raw13324step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13324step0 raw13324step0Labels permutation32 permutation6
    mixedMoment B raw13324step1 raw13324step1Labels = mixedMoment B raw13324step2 raw13324step2Labels := by
      have ha : raw13324step2 = raw13324step1 := by apply Matrix.ext; unfold raw13324step2 raw13324step1; decide +kernel
      have hl : raw13324step1Labels = labelEmbedding9 ∘ raw13324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13324step1 raw13324step1Labels raw13324step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw13325 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw13325step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw13325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13325 raw13325Labels = mixedMoment B node5143 node5143Labels := by
  calc
    mixedMoment B raw13325 raw13325Labels = mixedMoment B raw13325step0 raw13325step0Labels := by
      have ha : raw13325step0 = (fun i j => raw13325 (permutation500 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13325step0 raw13325; decide +kernel
      have hl : raw13325step0Labels = raw13325Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13325 raw13325Labels permutation500 permutation3
    mixedMoment B raw13325step0 raw13325step0Labels = mixedMoment B raw13325step1 raw13325step1Labels := by
      have ha : raw13325step1 = raw13325step0 := by apply Matrix.ext; unfold raw13325step1 raw13325step0; decide +kernel
      have hl : raw13325step0Labels = labelEmbedding6 ∘ raw13325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13325step0 raw13325step0Labels raw13325step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5143 node5143Labels := by rfl

def raw13326 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw13326step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13326step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw13326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13326 raw13326Labels = mixedMoment B node5285 node5285Labels := by
  calc
    mixedMoment B raw13326 raw13326Labels = mixedMoment B raw13326step0 raw13326step0Labels := by
      have ha : raw13326step0 = (fun i j => raw13326 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13326step0 raw13326; decide +kernel
      have hl : raw13326step0Labels = raw13326Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13326 raw13326Labels permutation176 permutation6
    mixedMoment B raw13326step0 raw13326step0Labels = mixedMoment B raw13326step1 raw13326step1Labels := by
      have ha : raw13326step1 = raw13326step0 := by apply Matrix.ext; unfold raw13326step1 raw13326step0; decide +kernel
      have hl : raw13326step0Labels = labelEmbedding9 ∘ raw13326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13326step0 raw13326step0Labels raw13326step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5285 node5285Labels := by rfl

def raw13327 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13327step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13327 raw13327Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw13327 raw13327Labels = mixedMoment B raw13327step0 raw13327step0Labels := by
      have ha : raw13327step0 = (fun i j => raw13327 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13327step0 raw13327; decide +kernel
      have hl : raw13327step0Labels = raw13327Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13327 raw13327Labels permutation176 permutation6
    mixedMoment B raw13327step0 raw13327step0Labels = mixedMoment B raw13327step1 raw13327step1Labels := by
      have ha : raw13327step1 = raw13327step0 := by apply Matrix.ext; unfold raw13327step1 raw13327step0; decide +kernel
      have hl : raw13327step0Labels = labelEmbedding9 ∘ raw13327step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13327step0 raw13327step0Labels raw13327step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw13328 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13328step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13328step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13328step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13328step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13328 raw13328Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw13328 raw13328Labels = mixedMoment B raw13328step0 raw13328step0Labels := by
      have ha : raw13328step0 = (fun i j => raw13328 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13328step0 raw13328; decide +kernel
      have hl : raw13328step0Labels = raw13328Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13328 raw13328Labels permutation200 permutation4
    mixedMoment B raw13328step0 raw13328step0Labels = mixedMoment B raw13328step1 raw13328step1Labels := by
      have ha : raw13328step1 = -raw13328step0 := by apply Matrix.ext; change ∀ i j, raw13328step1 i j = -(raw13328step0 i j); unfold raw13328step1 raw13328step0; decide +kernel
      have hl : raw13328step1Labels = raw13328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13328step1 raw13328step1Labels = mixedMoment B raw13328step2 raw13328step2Labels := by
      have ha : raw13328step2 = raw13328step1 := by apply Matrix.ext; unfold raw13328step2 raw13328step1; decide +kernel
      have hl : raw13328step1Labels = labelEmbedding7 ∘ raw13328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13328step1 raw13328step1Labels raw13328step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw13329 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13329step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13329step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13329 raw13329Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw13329 raw13329Labels = mixedMoment B raw13329step0 raw13329step0Labels := by
      have hz : ∀ j, raw13329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13329step0 = (fun i j => raw13329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13329step0 raw13329; decide +kernel
      have hl : raw13329step0Labels = raw13329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13329 raw13329Labels permutation346 hz
    mixedMoment B raw13329step0 raw13329step0Labels = mixedMoment B raw13329step1 raw13329step1Labels := by
      have ha : raw13329step1 = (fun i j => raw13329step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13329step1 raw13329step0; decide +kernel
      have hl : raw13329step1Labels = raw13329step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13329step0 raw13329step0Labels permutation32 permutation6
    mixedMoment B raw13329step1 raw13329step1Labels = mixedMoment B raw13329step2 raw13329step2Labels := by
      have ha : raw13329step2 = raw13329step1 := by apply Matrix.ext; unfold raw13329step2 raw13329step1; decide +kernel
      have hl : raw13329step1Labels = labelEmbedding9 ∘ raw13329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13329step1 raw13329step1Labels raw13329step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw13330 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw13330step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw13330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13330 raw13330Labels = mixedMoment B node5278 node5278Labels := by
  calc
    mixedMoment B raw13330 raw13330Labels = mixedMoment B raw13330step0 raw13330step0Labels := by
      have ha : raw13330step0 = (fun i j => raw13330 (permutation499 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13330step0 raw13330; decide +kernel
      have hl : raw13330step0Labels = raw13330Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13330 raw13330Labels permutation499 permutation3
    mixedMoment B raw13330step0 raw13330step0Labels = mixedMoment B raw13330step1 raw13330step1Labels := by
      have ha : raw13330step1 = raw13330step0 := by apply Matrix.ext; unfold raw13330step1 raw13330step0; decide +kernel
      have hl : raw13330step0Labels = labelEmbedding6 ∘ raw13330step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13330step0 raw13330step0Labels raw13330step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5278 node5278Labels := by rfl

def raw13331 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13331step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13331 raw13331Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13331 raw13331Labels = mixedMoment B raw13331step0 raw13331step0Labels := by
      have ha : raw13331step0 = (fun i j => raw13331 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13331step0 raw13331; decide +kernel
      have hl : raw13331step0Labels = raw13331Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13331 raw13331Labels permutation153 permutation6
    mixedMoment B raw13331step0 raw13331step0Labels = mixedMoment B raw13331step1 raw13331step1Labels := by
      have ha : raw13331step1 = raw13331step0 := by apply Matrix.ext; unfold raw13331step1 raw13331step0; decide +kernel
      have hl : raw13331step0Labels = labelEmbedding9 ∘ raw13331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13331step0 raw13331step0Labels raw13331step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw13332 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13332 raw13332Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw13332 raw13332Labels = mixedMoment B raw13332step0 raw13332step0Labels := by
      have hz : ∀ j, raw13332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13332step0 = (fun i j => raw13332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13332step0 raw13332; decide +kernel
      have hl : raw13332step0Labels = raw13332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13332 raw13332Labels permutation346 hz
    mixedMoment B raw13332step0 raw13332step0Labels = mixedMoment B raw13332step1 raw13332step1Labels := by
      have ha : raw13332step1 = (fun i j => raw13332step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13332step1 raw13332step0; decide +kernel
      have hl : raw13332step1Labels = raw13332step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13332step0 raw13332step0Labels permutation32 permutation6
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw13333 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13333 raw13333Labels = mixedMoment B node2573 node2573Labels := by
  calc
    mixedMoment B raw13333 raw13333Labels = mixedMoment B raw13333step0 raw13333step0Labels := by
      have ha : raw13333step0 = (fun i j => raw13333 (permutation502 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13333step0 raw13333; decide +kernel
      have hl : raw13333step0Labels = raw13333Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13333 raw13333Labels permutation502 permutation3
    _ = mixedMoment B node2573 node2573Labels := by rfl

def raw13334 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw13334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13334 raw13334Labels = mixedMoment B node3104 node3104Labels := by
  calc
    mixedMoment B raw13334 raw13334Labels = mixedMoment B raw13334step0 raw13334step0Labels := by
      have ha : raw13334step0 = (fun i j => raw13334 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13334step0 raw13334; decide +kernel
      have hl : raw13334step0Labels = raw13334Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13334 raw13334Labels permutation152 permutation6
    _ = mixedMoment B node3104 node3104Labels := by rfl

def raw13335 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13335 raw13335Labels = mixedMoment B node3105 node3105Labels := by
  calc
    mixedMoment B raw13335 raw13335Labels = mixedMoment B raw13335step0 raw13335step0Labels := by
      have ha : raw13335step0 = (fun i j => raw13335 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13335step0 raw13335; decide +kernel
      have hl : raw13335step0Labels = raw13335Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13335 raw13335Labels permutation152 permutation6
    _ = mixedMoment B node3105 node3105Labels := by rfl

def raw13336 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13336 raw13336Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw13336 raw13336Labels = mixedMoment B raw13336step0 raw13336step0Labels := by
      have ha : raw13336step0 = (fun i j => raw13336 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13336step0 raw13336; decide +kernel
      have hl : raw13336step0Labels = raw13336Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13336 raw13336Labels permutation176 permutation6
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw13337 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13337 raw13337Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw13337 raw13337Labels = mixedMoment B raw13337step0 raw13337step0Labels := by
      have hz : ∀ j, raw13337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13337step0 = (fun i j => raw13337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13337step0 raw13337; decide +kernel
      have hl : raw13337step0Labels = raw13337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13337 raw13337Labels permutation346 hz
    mixedMoment B raw13337step0 raw13337step0Labels = mixedMoment B raw13337step1 raw13337step1Labels := by
      have ha : raw13337step1 = (fun i j => raw13337step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13337step1 raw13337step0; decide +kernel
      have hl : raw13337step1Labels = raw13337step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13337step0 raw13337step0Labels permutation32 permutation6
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw13338 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw13338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13338 raw13338Labels = mixedMoment B node2565 node2565Labels := by
  calc
    mixedMoment B raw13338 raw13338Labels = mixedMoment B raw13338step0 raw13338step0Labels := by
      have ha : raw13338step0 = (fun i j => raw13338 (permutation500 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13338step0 raw13338; decide +kernel
      have hl : raw13338step0Labels = raw13338Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13338 raw13338Labels permutation500 permutation3
    _ = mixedMoment B node2565 node2565Labels := by rfl

def raw13339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw13339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13339 raw13339Labels = mixedMoment B node2756 node2756Labels := by
  calc
    mixedMoment B raw13339 raw13339Labels = mixedMoment B raw13339step0 raw13339step0Labels := by
      have ha : raw13339step0 = (fun i j => raw13339 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13339step0 raw13339; decide +kernel
      have hl : raw13339step0Labels = raw13339Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13339 raw13339Labels permutation176 permutation6
    _ = mixedMoment B node2756 node2756Labels := by rfl

def raw13340 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13340 raw13340Labels = mixedMoment B node2757 node2757Labels := by
  calc
    mixedMoment B raw13340 raw13340Labels = mixedMoment B raw13340step0 raw13340step0Labels := by
      have ha : raw13340step0 = (fun i j => raw13340 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13340step0 raw13340; decide +kernel
      have hl : raw13340step0Labels = raw13340Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13340 raw13340Labels permutation176 permutation6
    _ = mixedMoment B node2757 node2757Labels := by rfl

def raw13341 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13341 raw13341Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw13341 raw13341Labels = mixedMoment B raw13341step0 raw13341step0Labels := by
      have ha : raw13341step0 = (fun i j => raw13341 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13341step0 raw13341; decide +kernel
      have hl : raw13341step0Labels = raw13341Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13341 raw13341Labels permutation152 permutation6
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw13342 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13342step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13342 raw13342Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw13342 raw13342Labels = mixedMoment B raw13342step0 raw13342step0Labels := by
      have hz : ∀ j, raw13342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13342step0 = (fun i j => raw13342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13342step0 raw13342; decide +kernel
      have hl : raw13342step0Labels = raw13342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13342 raw13342Labels permutation346 hz
    mixedMoment B raw13342step0 raw13342step0Labels = mixedMoment B raw13342step1 raw13342step1Labels := by
      have ha : raw13342step1 = (fun i j => raw13342step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13342step1 raw13342step0; decide +kernel
      have hl : raw13342step1Labels = raw13342step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13342step0 raw13342step0Labels permutation32 permutation6
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw13343 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13343 raw13343Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw13343 raw13343Labels = mixedMoment B raw13343step0 raw13343step0Labels := by
      have ha : raw13343step0 = (fun i j => raw13343 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13343step0 raw13343; decide +kernel
      have hl : raw13343step0Labels = raw13343Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13343 raw13343Labels permutation154 permutation6
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw13344 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13344 raw13344Labels = mixedMoment B node2752 node2752Labels := by
  calc
    mixedMoment B raw13344 raw13344Labels = mixedMoment B raw13344step0 raw13344step0Labels := by
      have ha : raw13344step0 = (fun i j => raw13344 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13344step0 raw13344; decide +kernel
      have hl : raw13344step0Labels = raw13344Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13344 raw13344Labels permutation152 permutation6
    _ = mixedMoment B node2752 node2752Labels := by rfl

def raw13345 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13345 raw13345Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw13345 raw13345Labels = mixedMoment B raw13345step0 raw13345step0Labels := by
      have ha : raw13345step0 = (fun i j => raw13345 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13345step0 raw13345; decide +kernel
      have hl : raw13345step0Labels = raw13345Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13345 raw13345Labels permutation152 permutation6
    _ = mixedMoment B node2241 node2241Labels := by rfl

def raw13346 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13346step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13346 raw13346Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw13346 raw13346Labels = mixedMoment B raw13346step0 raw13346step0Labels := by
      have hz : ∀ j, raw13346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13346step0 = (fun i j => raw13346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13346step0 raw13346; decide +kernel
      have hl : raw13346step0Labels = raw13346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13346 raw13346Labels permutation346 hz
    mixedMoment B raw13346step0 raw13346step0Labels = mixedMoment B raw13346step1 raw13346step1Labels := by
      have ha : raw13346step1 = (fun i j => raw13346step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13346step1 raw13346step0; decide +kernel
      have hl : raw13346step1Labels = raw13346step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13346step0 raw13346step0Labels permutation32 permutation6
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw13347 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw13347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13347 raw13347Labels = mixedMoment B node2747 node2747Labels := by
  calc
    mixedMoment B raw13347 raw13347Labels = mixedMoment B raw13347step0 raw13347step0Labels := by
      have ha : raw13347step0 = (fun i j => raw13347 (permutation499 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13347step0 raw13347; decide +kernel
      have hl : raw13347step0Labels = raw13347Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13347 raw13347Labels permutation499 permutation3
    _ = mixedMoment B node2747 node2747Labels := by rfl

def raw13348 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13348 raw13348Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw13348 raw13348Labels = mixedMoment B raw13348step0 raw13348step0Labels := by
      have ha : raw13348step0 = (fun i j => raw13348 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13348step0 raw13348; decide +kernel
      have hl : raw13348step0Labels = raw13348Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13348 raw13348Labels permutation153 permutation6
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw13349 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13349Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13349step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13349step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13349 raw13349Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw13349 raw13349Labels = mixedMoment B raw13349step0 raw13349step0Labels := by
      have hz : ∀ j, raw13349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13349step0 = (fun i j => raw13349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13349step0 raw13349; decide +kernel
      have hl : raw13349step0Labels = raw13349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13349 raw13349Labels permutation346 hz
    mixedMoment B raw13349step0 raw13349step0Labels = mixedMoment B raw13349step1 raw13349step1Labels := by
      have ha : raw13349step1 = (fun i j => raw13349step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13349step1 raw13349step0; decide +kernel
      have hl : raw13349step1Labels = raw13349step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13349step0 raw13349step0Labels permutation37 permutation7
    mixedMoment B raw13349step1 raw13349step1Labels = mixedMoment B raw13349step2 raw13349step2Labels := by
      have ha : raw13349step2 = raw13349step1 := by apply Matrix.ext; unfold raw13349step2 raw13349step1; decide +kernel
      have hl : raw13349step1Labels = labelEmbedding1 ∘ raw13349step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13349step1 raw13349step1Labels raw13349step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw13350 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13350Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw13350step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13350step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw13350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13350 raw13350Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw13350 raw13350Labels = mixedMoment B raw13350step0 raw13350step0Labels := by
      have ha : raw13350step0 = (fun i j => raw13350 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13350step0 raw13350; decide +kernel
      have hl : raw13350step0Labels = raw13350Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13350 raw13350Labels permutation157 permutation7
    mixedMoment B raw13350step0 raw13350step0Labels = mixedMoment B raw13350step1 raw13350step1Labels := by
      have ha : raw13350step1 = raw13350step0 := by apply Matrix.ext; unfold raw13350step1 raw13350step0; decide +kernel
      have hl : raw13350step0Labels = labelEmbedding1 ∘ raw13350step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13350step0 raw13350step0Labels raw13350step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw13351 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13351Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw13351step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw13351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13351 raw13351Labels = mixedMoment B node2701 node2701Labels := by
  calc
    mixedMoment B raw13351 raw13351Labels = mixedMoment B raw13351step0 raw13351step0Labels := by
      have ha : raw13351step0 = (fun i j => raw13351 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13351step0 raw13351; decide +kernel
      have hl : raw13351step0Labels = raw13351Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13351 raw13351Labels permutation156 permutation7
    mixedMoment B raw13351step0 raw13351step0Labels = mixedMoment B raw13351step1 raw13351step1Labels := by
      have ha : raw13351step1 = raw13351step0 := by apply Matrix.ext; unfold raw13351step1 raw13351step0; decide +kernel
      have hl : raw13351step0Labels = labelEmbedding1 ∘ raw13351step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13351step0 raw13351step0Labels raw13351step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2701 node2701Labels := by rfl

def raw13352 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13352step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13352 raw13352Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw13352 raw13352Labels = mixedMoment B raw13352step0 raw13352step0Labels := by
      have ha : raw13352step0 = (fun i j => raw13352 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13352step0 raw13352; decide +kernel
      have hl : raw13352step0Labels = raw13352Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13352 raw13352Labels permutation155 permutation7
    mixedMoment B raw13352step0 raw13352step0Labels = mixedMoment B raw13352step1 raw13352step1Labels := by
      have ha : raw13352step1 = raw13352step0 := by apply Matrix.ext; unfold raw13352step1 raw13352step0; decide +kernel
      have hl : raw13352step0Labels = labelEmbedding1 ∘ raw13352step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13352step0 raw13352step0Labels raw13352step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2703 node2703Labels := by rfl

def raw13353 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13353Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw13353step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13353step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13353step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13353 raw13353Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw13353 raw13353Labels = mixedMoment B raw13353step0 raw13353step0Labels := by
      have ha : raw13353step0 = (fun i j => raw13353 (permutation217 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13353step0 raw13353; decide +kernel
      have hl : raw13353step0Labels = raw13353Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13353 raw13353Labels permutation217 permutation5
    mixedMoment B raw13353step0 raw13353step0Labels = mixedMoment B raw13353step1 raw13353step1Labels := by
      have ha : raw13353step1 = -raw13353step0 := by apply Matrix.ext; change ∀ i j, raw13353step1 i j = -(raw13353step0 i j); unfold raw13353step1 raw13353step0; decide +kernel
      have hl : raw13353step1Labels = raw13353step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13353step1 raw13353step1Labels = mixedMoment B raw13353step2 raw13353step2Labels := by
      have ha : raw13353step2 = raw13353step1 := by apply Matrix.ext; unfold raw13353step2 raw13353step1; decide +kernel
      have hl : raw13353step1Labels = labelEmbedding1 ∘ raw13353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13353step1 raw13353step1Labels raw13353step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw13354 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13354Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13354step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13354step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13354step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13354 raw13354Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw13354 raw13354Labels = mixedMoment B raw13354step0 raw13354step0Labels := by
      have hz : ∀ j, raw13354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13354step0 = (fun i j => raw13354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13354step0 raw13354; decide +kernel
      have hl : raw13354step0Labels = raw13354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13354 raw13354Labels permutation346 hz
    mixedMoment B raw13354step0 raw13354step0Labels = mixedMoment B raw13354step1 raw13354step1Labels := by
      have ha : raw13354step1 = (fun i j => raw13354step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13354step1 raw13354step0; decide +kernel
      have hl : raw13354step1Labels = raw13354step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13354step0 raw13354step0Labels permutation37 permutation7
    mixedMoment B raw13354step1 raw13354step1Labels = mixedMoment B raw13354step2 raw13354step2Labels := by
      have ha : raw13354step2 = raw13354step1 := by apply Matrix.ext; unfold raw13354step2 raw13354step1; decide +kernel
      have hl : raw13354step1Labels = labelEmbedding1 ∘ raw13354step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13354step1 raw13354step1Labels raw13354step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw13355 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13355Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw13355step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw13355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13355 raw13355Labels = mixedMoment B node3020 node3020Labels := by
  calc
    mixedMoment B raw13355 raw13355Labels = mixedMoment B raw13355step0 raw13355step0Labels := by
      have ha : raw13355step0 = (fun i j => raw13355 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13355step0 raw13355; decide +kernel
      have hl : raw13355step0Labels = raw13355Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13355 raw13355Labels permutation157 permutation7
    mixedMoment B raw13355step0 raw13355step0Labels = mixedMoment B raw13355step1 raw13355step1Labels := by
      have ha : raw13355step1 = raw13355step0 := by apply Matrix.ext; unfold raw13355step1 raw13355step0; decide +kernel
      have hl : raw13355step0Labels = labelEmbedding1 ∘ raw13355step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13355step0 raw13355step0Labels raw13355step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3020 node3020Labels := by rfl

def raw13356 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13356Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw13356step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw13356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13356 raw13356Labels = mixedMoment B node3021 node3021Labels := by
  calc
    mixedMoment B raw13356 raw13356Labels = mixedMoment B raw13356step0 raw13356step0Labels := by
      have ha : raw13356step0 = (fun i j => raw13356 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13356step0 raw13356; decide +kernel
      have hl : raw13356step0Labels = raw13356Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13356 raw13356Labels permutation156 permutation7
    mixedMoment B raw13356step0 raw13356step0Labels = mixedMoment B raw13356step1 raw13356step1Labels := by
      have ha : raw13356step1 = raw13356step0 := by apply Matrix.ext; unfold raw13356step1 raw13356step0; decide +kernel
      have hl : raw13356step0Labels = labelEmbedding1 ∘ raw13356step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13356step0 raw13356step0Labels raw13356step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3021 node3021Labels := by rfl

def raw13357 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13357Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13357step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13357 raw13357Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw13357 raw13357Labels = mixedMoment B raw13357step0 raw13357step0Labels := by
      have ha : raw13357step0 = (fun i j => raw13357 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13357step0 raw13357; decide +kernel
      have hl : raw13357step0Labels = raw13357Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13357 raw13357Labels permutation155 permutation7
    mixedMoment B raw13357step0 raw13357step0Labels = mixedMoment B raw13357step1 raw13357step1Labels := by
      have ha : raw13357step1 = raw13357step0 := by apply Matrix.ext; unfold raw13357step1 raw13357step0; decide +kernel
      have hl : raw13357step0Labels = labelEmbedding1 ∘ raw13357step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13357step0 raw13357step0Labels raw13357step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw13358 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13358Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13358step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13358step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13358step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13358 raw13358Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw13358 raw13358Labels = mixedMoment B raw13358step0 raw13358step0Labels := by
      have ha : raw13358step0 = (fun i j => raw13358 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13358step0 raw13358; decide +kernel
      have hl : raw13358step0Labels = raw13358Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13358 raw13358Labels permutation216 permutation5
    mixedMoment B raw13358step0 raw13358step0Labels = mixedMoment B raw13358step1 raw13358step1Labels := by
      have ha : raw13358step1 = -raw13358step0 := by apply Matrix.ext; change ∀ i j, raw13358step1 i j = -(raw13358step0 i j); unfold raw13358step1 raw13358step0; decide +kernel
      have hl : raw13358step1Labels = raw13358step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13358step1 raw13358step1Labels = mixedMoment B raw13358step2 raw13358step2Labels := by
      have ha : raw13358step2 = raw13358step1 := by apply Matrix.ext; unfold raw13358step2 raw13358step1; decide +kernel
      have hl : raw13358step1Labels = labelEmbedding1 ∘ raw13358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13358step1 raw13358step1Labels raw13358step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3226 node3226Labels := by rfl

def raw13359 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13359Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13359step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13359 raw13359Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13359 raw13359Labels = mixedMoment B raw13359step0 raw13359step0Labels := by
      have ha : raw13359step0 = (fun i j => raw13359 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13359step0 raw13359; decide +kernel
      have hl : raw13359step0Labels = raw13359Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13359 raw13359Labels permutation156 permutation7
    mixedMoment B raw13359step0 raw13359step0Labels = mixedMoment B raw13359step1 raw13359step1Labels := by
      have ha : raw13359step1 = raw13359step0 := by apply Matrix.ext; unfold raw13359step1 raw13359step0; decide +kernel
      have hl : raw13359step0Labels = labelEmbedding1 ∘ raw13359step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13359step0 raw13359step0Labels raw13359step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw13360 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13360Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13360step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13360step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13360step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13360step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13360 raw13360Labels = mixedMoment B node3182 node3182Labels := by
  calc
    mixedMoment B raw13360 raw13360Labels = mixedMoment B raw13360step0 raw13360step0Labels := by
      have ha : raw13360step0 = (fun i j => raw13360 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13360step0 raw13360; decide +kernel
      have hl : raw13360step0Labels = raw13360Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13360 raw13360Labels permutation216 permutation5
    mixedMoment B raw13360step0 raw13360step0Labels = mixedMoment B raw13360step1 raw13360step1Labels := by
      have ha : raw13360step1 = -raw13360step0 := by apply Matrix.ext; change ∀ i j, raw13360step1 i j = -(raw13360step0 i j); unfold raw13360step1 raw13360step0; decide +kernel
      have hl : raw13360step1Labels = raw13360step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13360step1 raw13360step1Labels = mixedMoment B raw13360step2 raw13360step2Labels := by
      have ha : raw13360step2 = raw13360step1 := by apply Matrix.ext; unfold raw13360step2 raw13360step1; decide +kernel
      have hl : raw13360step1Labels = labelEmbedding1 ∘ raw13360step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13360step1 raw13360step1Labels raw13360step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3182 node3182Labels := by rfl

def raw13361 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13361Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13361step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13361step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13361step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13361 raw13361Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw13361 raw13361Labels = mixedMoment B raw13361step0 raw13361step0Labels := by
      have hz : ∀ j, raw13361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13361step0 = (fun i j => raw13361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13361step0 raw13361; decide +kernel
      have hl : raw13361step0Labels = raw13361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13361 raw13361Labels permutation346 hz
    mixedMoment B raw13361step0 raw13361step0Labels = mixedMoment B raw13361step1 raw13361step1Labels := by
      have ha : raw13361step1 = (fun i j => raw13361step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13361step1 raw13361step0; decide +kernel
      have hl : raw13361step1Labels = raw13361step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13361step0 raw13361step0Labels permutation35 permutation7
    mixedMoment B raw13361step1 raw13361step1Labels = mixedMoment B raw13361step2 raw13361step2Labels := by
      have ha : raw13361step2 = raw13361step1 := by apply Matrix.ext; unfold raw13361step2 raw13361step1; decide +kernel
      have hl : raw13361step1Labels = labelEmbedding1 ∘ raw13361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13361step1 raw13361step1Labels raw13361step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw13362 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13362Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13362step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13362 raw13362Labels = mixedMoment B node3073 node3073Labels := by
  calc
    mixedMoment B raw13362 raw13362Labels = mixedMoment B raw13362step0 raw13362step0Labels := by
      have ha : raw13362step0 = (fun i j => raw13362 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13362step0 raw13362; decide +kernel
      have hl : raw13362step0Labels = raw13362Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13362 raw13362Labels permutation155 permutation7
    mixedMoment B raw13362step0 raw13362step0Labels = mixedMoment B raw13362step1 raw13362step1Labels := by
      have ha : raw13362step1 = raw13362step0 := by apply Matrix.ext; unfold raw13362step1 raw13362step0; decide +kernel
      have hl : raw13362step0Labels = labelEmbedding1 ∘ raw13362step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13362step0 raw13362step0Labels raw13362step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3073 node3073Labels := by rfl

def raw13363 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13363Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13363step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13363step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13363 raw13363Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13363 raw13363Labels = mixedMoment B raw13363step0 raw13363step0Labels := by
      have ha : raw13363step0 = (fun i j => raw13363 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13363step0 raw13363; decide +kernel
      have hl : raw13363step0Labels = raw13363Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13363 raw13363Labels permutation155 permutation7
    mixedMoment B raw13363step0 raw13363step0Labels = mixedMoment B raw13363step1 raw13363step1Labels := by
      have ha : raw13363step1 = raw13363step0 := by apply Matrix.ext; unfold raw13363step1 raw13363step0; decide +kernel
      have hl : raw13363step0Labels = labelEmbedding1 ∘ raw13363step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13363step0 raw13363step0Labels raw13363step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw13364 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13364 raw13364Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw13364 raw13364Labels = mixedMoment B raw13364step0 raw13364step0Labels := by
      have hz : ∀ j, raw13364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13364step0 = (fun i j => raw13364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13364step0 raw13364; decide +kernel
      have hl : raw13364step0Labels = raw13364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13364 raw13364Labels permutation346 hz
    mixedMoment B raw13364step0 raw13364step0Labels = mixedMoment B raw13364step1 raw13364step1Labels := by
      have ha : raw13364step1 = (fun i j => raw13364step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13364step1 raw13364step0; decide +kernel
      have hl : raw13364step1Labels = raw13364step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13364step0 raw13364step0Labels permutation37 permutation2
    mixedMoment B raw13364step1 raw13364step1Labels = mixedMoment B raw13364step2 raw13364step2Labels := by
      have ha : raw13364step2 = -raw13364step1 := by apply Matrix.ext; change ∀ i j, raw13364step2 i j = -(raw13364step1 i j); unfold raw13364step2 raw13364step1; decide +kernel
      have hl : raw13364step2Labels = raw13364step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw13365 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw13365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13365 raw13365Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw13365 raw13365Labels = mixedMoment B raw13365step0 raw13365step0Labels := by
      have ha : raw13365step0 = (fun i j => raw13365 (permutation502 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13365step0 raw13365; decide +kernel
      have hl : raw13365step0Labels = raw13365Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13365 raw13365Labels permutation502 permutation2
    _ = mixedMoment B node2923 node2923Labels := by rfl

def raw13366 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw13366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw13366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13366 raw13366Labels = mixedMoment B node3489 node3489Labels := by
  calc
    mixedMoment B raw13366 raw13366Labels = mixedMoment B raw13366step0 raw13366step0Labels := by
      have ha : raw13366step0 = (fun i j => raw13366 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13366step0 raw13366; decide +kernel
      have hl : raw13366step0Labels = raw13366Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13366 raw13366Labels permutation156 permutation2
    mixedMoment B raw13366step0 raw13366step0Labels = mixedMoment B raw13366step1 raw13366step1Labels := by
      have ha : raw13366step1 = -raw13366step0 := by apply Matrix.ext; change ∀ i j, raw13366step1 i j = -(raw13366step0 i j); unfold raw13366step1 raw13366step0; decide +kernel
      have hl : raw13366step1Labels = raw13366step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3489 node3489Labels := by rfl

def raw13367 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13367 raw13367Labels = mixedMoment B node3496 node3496Labels := by
  calc
    mixedMoment B raw13367 raw13367Labels = mixedMoment B raw13367step0 raw13367step0Labels := by
      have ha : raw13367step0 = (fun i j => raw13367 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13367step0 raw13367; decide +kernel
      have hl : raw13367step0Labels = raw13367Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13367 raw13367Labels permutation155 permutation2
    mixedMoment B raw13367step0 raw13367step0Labels = mixedMoment B raw13367step1 raw13367step1Labels := by
      have ha : raw13367step1 = -raw13367step0 := by apply Matrix.ext; change ∀ i j, raw13367step1 i j = -(raw13367step0 i j); unfold raw13367step1 raw13367step0; decide +kernel
      have hl : raw13367step1Labels = raw13367step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3496 node3496Labels := by rfl

def raw13368 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw13368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13368 raw13368Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw13368 raw13368Labels = mixedMoment B raw13368step0 raw13368step0Labels := by
      have ha : raw13368step0 = (fun i j => raw13368 (permutation215 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13368step0 raw13368; decide +kernel
      have hl : raw13368step0Labels = raw13368Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13368 raw13368Labels permutation215 permutation4
    mixedMoment B raw13368step0 raw13368step0Labels = mixedMoment B raw13368step1 raw13368step1Labels := by
      have ha : raw13368step1 = -raw13368step0 := by apply Matrix.ext; change ∀ i j, raw13368step1 i j = -(raw13368step0 i j); unfold raw13368step1 raw13368step0; decide +kernel
      have hl : raw13368step1Labels = raw13368step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2089 node2089Labels := by rfl

def raw13369 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13369 raw13369Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw13369 raw13369Labels = mixedMoment B raw13369step0 raw13369step0Labels := by
      have ha : raw13369step0 = (fun i j => raw13369 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13369step0 raw13369; decide +kernel
      have hl : raw13369step0Labels = raw13369Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13369 raw13369Labels permutation200 permutation4
    mixedMoment B raw13369step0 raw13369step0Labels = mixedMoment B raw13369step1 raw13369step1Labels := by
      have ha : raw13369step1 = -raw13369step0 := by apply Matrix.ext; change ∀ i j, raw13369step1 i j = -(raw13369step0 i j); unfold raw13369step1 raw13369step0; decide +kernel
      have hl : raw13369step1Labels = raw13369step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2105 node2105Labels := by rfl

def raw13370 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw13370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw13370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13370 raw13370Labels = mixedMoment B node2926 node2926Labels := by
  calc
    mixedMoment B raw13370 raw13370Labels = mixedMoment B raw13370step0 raw13370step0Labels := by
      have ha : raw13370step0 = (fun i j => raw13370 (permutation503 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13370step0 raw13370; decide +kernel
      have hl : raw13370step0Labels = raw13370Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13370 raw13370Labels permutation503 permutation2
    _ = mixedMoment B node2926 node2926Labels := by rfl

def raw13371 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13371 raw13371Labels = mixedMoment B node3073 node3073Labels := by
  calc
    mixedMoment B raw13371 raw13371Labels = mixedMoment B raw13371step0 raw13371step0Labels := by
      have ha : raw13371step0 = (fun i j => raw13371 (permutation502 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13371step0 raw13371; decide +kernel
      have hl : raw13371step0Labels = raw13371Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13371 raw13371Labels permutation502 permutation2
    _ = mixedMoment B node3073 node3073Labels := by rfl

def raw13372 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw13372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13372 raw13372Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw13372 raw13372Labels = mixedMoment B raw13372step0 raw13372step0Labels := by
      have hz : ∀ j, raw13372 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13372step0 = (fun i j => raw13372 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13372step0 raw13372; decide +kernel
      have hl : raw13372step0Labels = raw13372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13372 raw13372Labels permutation346 hz
    mixedMoment B raw13372step0 raw13372step0Labels = mixedMoment B raw13372step1 raw13372step1Labels := by
      have ha : raw13372step1 = (fun i j => raw13372step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13372step1 raw13372step0; decide +kernel
      have hl : raw13372step1Labels = raw13372step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13372step0 raw13372step0Labels permutation38 permutation4
    mixedMoment B raw13372step1 raw13372step1Labels = mixedMoment B raw13372step2 raw13372step2Labels := by
      have ha : raw13372step2 = -raw13372step1 := by apply Matrix.ext; change ∀ i j, raw13372step2 i j = -(raw13372step1 i j); unfold raw13372step2 raw13372step1; decide +kernel
      have hl : raw13372step2Labels = raw13372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw13373 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13373 raw13373Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw13373 raw13373Labels = mixedMoment B raw13373step0 raw13373step0Labels := by
      have ha : raw13373step0 = (fun i j => raw13373 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13373step0 raw13373; decide +kernel
      have hl : raw13373step0Labels = raw13373Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13373 raw13373Labels permutation218 permutation4
    mixedMoment B raw13373step0 raw13373step0Labels = mixedMoment B raw13373step1 raw13373step1Labels := by
      have ha : raw13373step1 = -raw13373step0 := by apply Matrix.ext; change ∀ i j, raw13373step1 i j = -(raw13373step0 i j); unfold raw13373step1 raw13373step0; decide +kernel
      have hl : raw13373step1Labels = raw13373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw13374 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw13374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw13374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13374 raw13374Labels = mixedMoment B node3551 node3551Labels := by
  calc
    mixedMoment B raw13374 raw13374Labels = mixedMoment B raw13374step0 raw13374step0Labels := by
      have ha : raw13374step0 = (fun i j => raw13374 (permutation215 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13374step0 raw13374; decide +kernel
      have hl : raw13374step0Labels = raw13374Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13374 raw13374Labels permutation215 permutation4
    mixedMoment B raw13374step0 raw13374step0Labels = mixedMoment B raw13374step1 raw13374step1Labels := by
      have ha : raw13374step1 = -raw13374step0 := by apply Matrix.ext; change ∀ i j, raw13374step1 i j = -(raw13374step0 i j); unfold raw13374step1 raw13374step0; decide +kernel
      have hl : raw13374step1Labels = raw13374step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3551 node3551Labels := by rfl

def raw13375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13375 raw13375Labels = mixedMoment B node5447 node5447Labels := by
  calc
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw13376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13376 raw13376Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw13376 raw13376Labels = mixedMoment B raw13376step0 raw13376step0Labels := by
      have ha : raw13376step0 = (fun i j => raw13376 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13376step0 raw13376; decide +kernel
      have hl : raw13376step0Labels = raw13376Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13376 raw13376Labels permutation176 permutation2
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw13377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13377 raw13377Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw13377 raw13377Labels = mixedMoment B raw13377step0 raw13377step0Labels := by
      have hz : ∀ j, raw13377 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13377step0 = (fun i j => raw13377 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13377step0 raw13377; decide +kernel
      have hl : raw13377step0Labels = raw13377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13377 raw13377Labels permutation434 hz
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw13378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13378 raw13378Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw13378 raw13378Labels = mixedMoment B raw13378step0 raw13378step0Labels := by
      have hz : ∀ j, raw13378 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13378step0 = (fun i j => raw13378 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13378step0 raw13378; decide +kernel
      have hl : raw13378step0Labels = raw13378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13378 raw13378Labels permutation520 hz
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw13379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13379 raw13379Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw13379 raw13379Labels = mixedMoment B raw13379step0 raw13379step0Labels := by
      have hz : ∀ j, raw13379 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13379step0 = (fun i j => raw13379 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13379step0 raw13379; decide +kernel
      have hl : raw13379step0Labels = raw13379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13379 raw13379Labels permutation590 hz
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw13380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13380step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13380step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13380 raw13380Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw13380 raw13380Labels = mixedMoment B raw13380step0 raw13380step0Labels := by
      have ha : raw13380step0 = (fun i j => raw13380 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13380step0 raw13380; decide +kernel
      have hl : raw13380step0Labels = raw13380Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13380 raw13380Labels permutation176 permutation3
    mixedMoment B raw13380step0 raw13380step0Labels = mixedMoment B raw13380step1 raw13380step1Labels := by
      have ha : raw13380step1 = raw13380step0 := by apply Matrix.ext; unfold raw13380step1 raw13380step0; decide +kernel
      have hl : raw13380step0Labels = labelEmbedding6 ∘ raw13380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13380step0 raw13380step0Labels raw13380step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw13381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13381 raw13381Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw13381 raw13381Labels = mixedMoment B raw13381step0 raw13381step0Labels := by
      have ha : raw13381step0 = (fun i j => raw13381 (permutation185 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13381step0 raw13381; decide +kernel
      have hl : raw13381step0Labels = raw13381Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13381 raw13381Labels permutation185 permutation2
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw13382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13382step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13382 raw13382Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13382 raw13382Labels = mixedMoment B raw13382step0 raw13382step0Labels := by
      have hz : ∀ j, raw13382 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13382step0 = (fun i j => raw13382 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13382step0 raw13382; decide +kernel
      have hl : raw13382step0Labels = raw13382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13382 raw13382Labels permutation434 hz
    mixedMoment B raw13382step0 raw13382step0Labels = mixedMoment B raw13382step1 raw13382step1Labels := by
      have ha : raw13382step1 = (fun i j => raw13382step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13382step1 raw13382step0; decide +kernel
      have hl : raw13382step1Labels = raw13382step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13382step0 raw13382step0Labels permutation41 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw13383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13383 raw13383Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13383 raw13383Labels = mixedMoment B raw13383step0 raw13383step0Labels := by
      have hz : ∀ j, raw13383 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13383step0 = (fun i j => raw13383 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13383step0 raw13383; decide +kernel
      have hl : raw13383step0Labels = raw13383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13383 raw13383Labels permutation520 hz
    mixedMoment B raw13383step0 raw13383step0Labels = mixedMoment B raw13383step1 raw13383step1Labels := by
      have ha : raw13383step1 = (fun i j => raw13383step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13383step1 raw13383step0; decide +kernel
      have hl : raw13383step1Labels = raw13383step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13383step0 raw13383step0Labels permutation41 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw13384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13384 raw13384Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13384 raw13384Labels = mixedMoment B raw13384step0 raw13384step0Labels := by
      have hz : ∀ j, raw13384 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13384step0 = (fun i j => raw13384 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13384step0 raw13384; decide +kernel
      have hl : raw13384step0Labels = raw13384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13384 raw13384Labels permutation590 hz
    mixedMoment B raw13384step0 raw13384step0Labels = mixedMoment B raw13384step1 raw13384step1Labels := by
      have ha : raw13384step1 = (fun i j => raw13384step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13384step1 raw13384step0; decide +kernel
      have hl : raw13384step1Labels = raw13384step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13384step0 raw13384step0Labels permutation41 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw13385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13385step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13385step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13385 raw13385Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw13385 raw13385Labels = mixedMoment B raw13385step0 raw13385step0Labels := by
      have ha : raw13385step0 = (fun i j => raw13385 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13385step0 raw13385; decide +kernel
      have hl : raw13385step0Labels = raw13385Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13385 raw13385Labels permutation152 permutation3
    mixedMoment B raw13385step0 raw13385step0Labels = mixedMoment B raw13385step1 raw13385step1Labels := by
      have ha : raw13385step1 = raw13385step0 := by apply Matrix.ext; unfold raw13385step1 raw13385step0; decide +kernel
      have hl : raw13385step0Labels = labelEmbedding6 ∘ raw13385step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13385step0 raw13385step0Labels raw13385step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw13386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13386 raw13386Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw13386 raw13386Labels = mixedMoment B raw13386step0 raw13386step0Labels := by
      have ha : raw13386step0 = (fun i j => raw13386 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13386step0 raw13386; decide +kernel
      have hl : raw13386step0Labels = raw13386Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13386 raw13386Labels permutation161 permutation2
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw13387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13387 raw13387Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13387 raw13387Labels = mixedMoment B raw13387step0 raw13387step0Labels := by
      have hz : ∀ j, raw13387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13387step0 = (fun i j => raw13387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13387step0 raw13387; decide +kernel
      have hl : raw13387step0Labels = raw13387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13387 raw13387Labels permutation434 hz
    mixedMoment B raw13387step0 raw13387step0Labels = mixedMoment B raw13387step1 raw13387step1Labels := by
      have ha : raw13387step1 = (fun i j => raw13387step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13387step1 raw13387step0; decide +kernel
      have hl : raw13387step1Labels = raw13387step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13387step0 raw13387step0Labels permutation35 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw13388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13388 raw13388Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13388 raw13388Labels = mixedMoment B raw13388step0 raw13388step0Labels := by
      have hz : ∀ j, raw13388 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13388step0 = (fun i j => raw13388 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13388step0 raw13388; decide +kernel
      have hl : raw13388step0Labels = raw13388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13388 raw13388Labels permutation520 hz
    mixedMoment B raw13388step0 raw13388step0Labels = mixedMoment B raw13388step1 raw13388step1Labels := by
      have ha : raw13388step1 = (fun i j => raw13388step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13388step1 raw13388step0; decide +kernel
      have hl : raw13388step1Labels = raw13388step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13388step0 raw13388step0Labels permutation35 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw13389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13389 raw13389Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13389 raw13389Labels = mixedMoment B raw13389step0 raw13389step0Labels := by
      have hz : ∀ j, raw13389 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13389step0 = (fun i j => raw13389 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13389step0 raw13389; decide +kernel
      have hl : raw13389step0Labels = raw13389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13389 raw13389Labels permutation590 hz
    mixedMoment B raw13389step0 raw13389step0Labels = mixedMoment B raw13389step1 raw13389step1Labels := by
      have ha : raw13389step1 = (fun i j => raw13389step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13389step1 raw13389step0; decide +kernel
      have hl : raw13389step1Labels = raw13389step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13389step0 raw13389step0Labels permutation35 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw13390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13390step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13390 raw13390Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw13390 raw13390Labels = mixedMoment B raw13390step0 raw13390step0Labels := by
      have ha : raw13390step0 = (fun i j => raw13390 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13390step0 raw13390; decide +kernel
      have hl : raw13390step0Labels = raw13390Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13390 raw13390Labels permutation155 permutation3
    mixedMoment B raw13390step0 raw13390step0Labels = mixedMoment B raw13390step1 raw13390step1Labels := by
      have ha : raw13390step1 = raw13390step0 := by apply Matrix.ext; unfold raw13390step1 raw13390step0; decide +kernel
      have hl : raw13390step0Labels = labelEmbedding6 ∘ raw13390step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13390step0 raw13390step0Labels raw13390step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

def raw13391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13391 raw13391Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw13391 raw13391Labels = mixedMoment B raw13391step0 raw13391step0Labels := by
      have ha : raw13391step0 = (fun i j => raw13391 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13391step0 raw13391; decide +kernel
      have hl : raw13391step0Labels = raw13391Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13391 raw13391Labels permutation155 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw13392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13392 raw13392Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw13392 raw13392Labels = mixedMoment B raw13392step0 raw13392step0Labels := by
      have ha : raw13392step0 = (fun i j => raw13392 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13392step0 raw13392; decide +kernel
      have hl : raw13392step0Labels = raw13392Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13392 raw13392Labels permutation179 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw13393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw13393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13393 raw13393Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13393 raw13393Labels = mixedMoment B raw13393step0 raw13393step0Labels := by
      have hz : ∀ j, raw13393 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13393step0 = (fun i j => raw13393 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13393step0 raw13393; decide +kernel
      have hl : raw13393step0Labels = raw13393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13393 raw13393Labels permutation520 hz
    mixedMoment B raw13393step0 raw13393step0Labels = mixedMoment B raw13393step1 raw13393step1Labels := by
      have ha : raw13393step1 = (fun i j => raw13393step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13393step1 raw13393step0; decide +kernel
      have hl : raw13393step1Labels = raw13393step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13393step0 raw13393step0Labels permutation33 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw13394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw13394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13394 raw13394Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13394 raw13394Labels = mixedMoment B raw13394step0 raw13394step0Labels := by
      have hz : ∀ j, raw13394 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13394step0 = (fun i j => raw13394 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13394step0 raw13394; decide +kernel
      have hl : raw13394step0Labels = raw13394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13394 raw13394Labels permutation590 hz
    mixedMoment B raw13394step0 raw13394step0Labels = mixedMoment B raw13394step1 raw13394step1Labels := by
      have ha : raw13394step1 = (fun i j => raw13394step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13394step1 raw13394step0; decide +kernel
      have hl : raw13394step1Labels = raw13394step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13394step0 raw13394step0Labels permutation33 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw13395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13395step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13395 raw13395Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw13395 raw13395Labels = mixedMoment B raw13395step0 raw13395step0Labels := by
      have ha : raw13395step0 = (fun i j => raw13395 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13395step0 raw13395; decide +kernel
      have hl : raw13395step0Labels = raw13395Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13395 raw13395Labels permutation153 permutation3
    mixedMoment B raw13395step0 raw13395step0Labels = mixedMoment B raw13395step1 raw13395step1Labels := by
      have ha : raw13395step1 = raw13395step0 := by apply Matrix.ext; unfold raw13395step1 raw13395step0; decide +kernel
      have hl : raw13395step0Labels = labelEmbedding6 ∘ raw13395step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13395step0 raw13395step0Labels raw13395step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

def raw13396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13396step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13396 raw13396Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw13396 raw13396Labels = mixedMoment B raw13396step0 raw13396step0Labels := by
      have ha : raw13396step0 = (fun i j => raw13396 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13396step0 raw13396; decide +kernel
      have hl : raw13396step0Labels = raw13396Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13396 raw13396Labels permutation153 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw13397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13397 raw13397Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw13397 raw13397Labels = mixedMoment B raw13397step0 raw13397step0Labels := by
      have ha : raw13397step0 = (fun i j => raw13397 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13397step0 raw13397; decide +kernel
      have hl : raw13397step0Labels = raw13397Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13397 raw13397Labels permutation177 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw13398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw13398step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13398 raw13398Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13398 raw13398Labels = mixedMoment B raw13398step0 raw13398step0Labels := by
      have hz : ∀ j, raw13398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13398step0 = (fun i j => raw13398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13398step0 raw13398; decide +kernel
      have hl : raw13398step0Labels = raw13398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13398 raw13398Labels permutation434 hz
    mixedMoment B raw13398step0 raw13398step0Labels = mixedMoment B raw13398step1 raw13398step1Labels := by
      have ha : raw13398step1 = (fun i j => raw13398step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13398step1 raw13398step0; decide +kernel
      have hl : raw13398step1Labels = raw13398step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13398step0 raw13398step0Labels permutation33 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw13399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw13399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13399 raw13399Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13399 raw13399Labels = mixedMoment B raw13399step0 raw13399step0Labels := by
      have hz : ∀ j, raw13399 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13399step0 = (fun i j => raw13399 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13399step0 raw13399; decide +kernel
      have hl : raw13399step0Labels = raw13399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13399 raw13399Labels permutation590 hz
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw13400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13400step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13400 raw13400Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw13400 raw13400Labels = mixedMoment B raw13400step0 raw13400step0Labels := by
      have ha : raw13400step0 = (fun i j => raw13400 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13400step0 raw13400; decide +kernel
      have hl : raw13400step0Labels = raw13400Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13400 raw13400Labels permutation152 permutation3
    mixedMoment B raw13400step0 raw13400step0Labels = mixedMoment B raw13400step1 raw13400step1Labels := by
      have ha : raw13400step1 = raw13400step0 := by apply Matrix.ext; unfold raw13400step1 raw13400step0; decide +kernel
      have hl : raw13400step0Labels = labelEmbedding6 ∘ raw13400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13400step0 raw13400step0Labels raw13400step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

def raw13401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13401 raw13401Labels = mixedMoment B node5192 node5192Labels := by
  calc
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw13402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13402 raw13402Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw13402 raw13402Labels = mixedMoment B raw13402step0 raw13402step0Labels := by
      have ha : raw13402step0 = (fun i j => raw13402 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13402step0 raw13402; decide +kernel
      have hl : raw13402step0Labels = raw13402Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13402 raw13402Labels permutation176 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw13403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13403step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13403 raw13403Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13403 raw13403Labels = mixedMoment B raw13403step0 raw13403step0Labels := by
      have hz : ∀ j, raw13403 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13403step0 = (fun i j => raw13403 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13403step0 raw13403; decide +kernel
      have hl : raw13403step0Labels = raw13403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13403 raw13403Labels permutation434 hz
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw13404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw13404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13404 raw13404Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13404 raw13404Labels = mixedMoment B raw13404step0 raw13404step0Labels := by
      have hz : ∀ j, raw13404 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13404step0 = (fun i j => raw13404 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13404step0 raw13404; decide +kernel
      have hl : raw13404step0Labels = raw13404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13404 raw13404Labels permutation520 hz
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw13405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13405 raw13405Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw13405 raw13405Labels = mixedMoment B raw13405step0 raw13405step0Labels := by
      have ha : raw13405step0 = (fun i j => raw13405 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13405step0 raw13405; decide +kernel
      have hl : raw13405step0Labels = raw13405Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13405 raw13405Labels permutation152 permutation3
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw13406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13406 raw13406Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw13406 raw13406Labels = mixedMoment B raw13406step0 raw13406step0Labels := by
      have ha : raw13406step0 = (fun i j => raw13406 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13406step0 raw13406; decide +kernel
      have hl : raw13406step0Labels = raw13406Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13406 raw13406Labels permutation176 permutation3
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw13407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13407 raw13407Labels = mixedMoment B node4039 node4039Labels := by
  calc
    mixedMoment B raw13407 raw13407Labels = mixedMoment B raw13407step0 raw13407step0Labels := by
      have hz : ∀ j, raw13407 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13407step0 = (fun i j => raw13407 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13407step0 raw13407; decide +kernel
      have hl : raw13407step0Labels = raw13407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13407 raw13407Labels permutation434 hz
    mixedMoment B raw13407step0 raw13407step0Labels = mixedMoment B raw13407step1 raw13407step1Labels := by
      have ha : raw13407step1 = (fun i j => raw13407step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13407step1 raw13407step0; decide +kernel
      have hl : raw13407step1Labels = raw13407step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13407step0 raw13407step0Labels permutation32 permutation3
    _ = mixedMoment B node4039 node4039Labels := by rfl

def raw13408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13408 raw13408Labels = mixedMoment B node4039 node4039Labels := by
  calc
    mixedMoment B raw13408 raw13408Labels = mixedMoment B raw13408step0 raw13408step0Labels := by
      have hz : ∀ j, raw13408 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13408step0 = (fun i j => raw13408 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13408step0 raw13408; decide +kernel
      have hl : raw13408step0Labels = raw13408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13408 raw13408Labels permutation520 hz
    mixedMoment B raw13408step0 raw13408step0Labels = mixedMoment B raw13408step1 raw13408step1Labels := by
      have ha : raw13408step1 = (fun i j => raw13408step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13408step1 raw13408step0; decide +kernel
      have hl : raw13408step1Labels = raw13408step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13408step0 raw13408step0Labels permutation32 permutation3
    _ = mixedMoment B node4039 node4039Labels := by rfl

def raw13409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13409 raw13409Labels = mixedMoment B node4039 node4039Labels := by
  calc
    mixedMoment B raw13409 raw13409Labels = mixedMoment B raw13409step0 raw13409step0Labels := by
      have hz : ∀ j, raw13409 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13409step0 = (fun i j => raw13409 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13409step0 raw13409; decide +kernel
      have hl : raw13409step0Labels = raw13409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13409 raw13409Labels permutation590 hz
    mixedMoment B raw13409step0 raw13409step0Labels = mixedMoment B raw13409step1 raw13409step1Labels := by
      have ha : raw13409step1 = (fun i j => raw13409step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13409step1 raw13409step0; decide +kernel
      have hl : raw13409step1Labels = raw13409step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13409step0 raw13409step0Labels permutation32 permutation3
    _ = mixedMoment B node4039 node4039Labels := by rfl

def raw13410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13410 raw13410Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw13410 raw13410Labels = mixedMoment B raw13410step0 raw13410step0Labels := by
      have ha : raw13410step0 = (fun i j => raw13410 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13410step0 raw13410; decide +kernel
      have hl : raw13410step0Labels = raw13410Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13410 raw13410Labels permutation176 permutation3
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw13411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13411 raw13411Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw13411 raw13411Labels = mixedMoment B raw13411step0 raw13411step0Labels := by
      have ha : raw13411step0 = (fun i j => raw13411 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13411step0 raw13411; decide +kernel
      have hl : raw13411step0Labels = raw13411Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13411 raw13411Labels permutation176 permutation3
    _ = mixedMoment B node2880 node2880Labels := by rfl

def raw13412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13412step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13412 raw13412Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13412 raw13412Labels = mixedMoment B raw13412step0 raw13412step0Labels := by
      have hz : ∀ j, raw13412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13412step0 = (fun i j => raw13412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13412step0 raw13412; decide +kernel
      have hl : raw13412step0Labels = raw13412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13412 raw13412Labels permutation434 hz
    mixedMoment B raw13412step0 raw13412step0Labels = mixedMoment B raw13412step1 raw13412step1Labels := by
      have ha : raw13412step1 = (fun i j => raw13412step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13412step1 raw13412step0; decide +kernel
      have hl : raw13412step1Labels = raw13412step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13412step0 raw13412step0Labels permutation38 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw13413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13413 raw13413Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13413 raw13413Labels = mixedMoment B raw13413step0 raw13413step0Labels := by
      have hz : ∀ j, raw13413 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13413step0 = (fun i j => raw13413 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13413step0 raw13413; decide +kernel
      have hl : raw13413step0Labels = raw13413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13413 raw13413Labels permutation520 hz
    mixedMoment B raw13413step0 raw13413step0Labels = mixedMoment B raw13413step1 raw13413step1Labels := by
      have ha : raw13413step1 = (fun i j => raw13413step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13413step1 raw13413step0; decide +kernel
      have hl : raw13413step1Labels = raw13413step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13413step0 raw13413step0Labels permutation38 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw13414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13414step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13414 raw13414Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13414 raw13414Labels = mixedMoment B raw13414step0 raw13414step0Labels := by
      have hz : ∀ j, raw13414 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13414step0 = (fun i j => raw13414 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13414step0 raw13414; decide +kernel
      have hl : raw13414step0Labels = raw13414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13414 raw13414Labels permutation590 hz
    mixedMoment B raw13414step0 raw13414step0Labels = mixedMoment B raw13414step1 raw13414step1Labels := by
      have ha : raw13414step1 = (fun i j => raw13414step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13414step1 raw13414step0; decide +kernel
      have hl : raw13414step1Labels = raw13414step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13414step0 raw13414step0Labels permutation38 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw13415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13415 raw13415Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw13415 raw13415Labels = mixedMoment B raw13415step0 raw13415step0Labels := by
      have ha : raw13415step0 = (fun i j => raw13415 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13415step0 raw13415; decide +kernel
      have hl : raw13415step0Labels = raw13415Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13415 raw13415Labels permutation152 permutation3
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw13416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13416 raw13416Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw13416 raw13416Labels = mixedMoment B raw13416step0 raw13416step0Labels := by
      have ha : raw13416step0 = (fun i j => raw13416 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13416step0 raw13416; decide +kernel
      have hl : raw13416step0Labels = raw13416Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13416 raw13416Labels permutation152 permutation3
    _ = mixedMoment B node2880 node2880Labels := by rfl

def raw13417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13417step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13417 raw13417Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13417 raw13417Labels = mixedMoment B raw13417step0 raw13417step0Labels := by
      have hz : ∀ j, raw13417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13417step0 = (fun i j => raw13417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13417step0 raw13417; decide +kernel
      have hl : raw13417step0Labels = raw13417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13417 raw13417Labels permutation434 hz
    mixedMoment B raw13417step0 raw13417step0Labels = mixedMoment B raw13417step1 raw13417step1Labels := by
      have ha : raw13417step1 = (fun i j => raw13417step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13417step1 raw13417step0; decide +kernel
      have hl : raw13417step1Labels = raw13417step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13417step0 raw13417step0Labels permutation32 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw13418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13418step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13418 raw13418Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13418 raw13418Labels = mixedMoment B raw13418step0 raw13418step0Labels := by
      have hz : ∀ j, raw13418 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13418step0 = (fun i j => raw13418 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13418step0 raw13418; decide +kernel
      have hl : raw13418step0Labels = raw13418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13418 raw13418Labels permutation520 hz
    mixedMoment B raw13418step0 raw13418step0Labels = mixedMoment B raw13418step1 raw13418step1Labels := by
      have ha : raw13418step1 = (fun i j => raw13418step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13418step1 raw13418step0; decide +kernel
      have hl : raw13418step1Labels = raw13418step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13418step0 raw13418step0Labels permutation32 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw13419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw13419step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13419 raw13419Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13419 raw13419Labels = mixedMoment B raw13419step0 raw13419step0Labels := by
      have hz : ∀ j, raw13419 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13419step0 = (fun i j => raw13419 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13419step0 raw13419; decide +kernel
      have hl : raw13419step0Labels = raw13419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13419 raw13419Labels permutation590 hz
    mixedMoment B raw13419step0 raw13419step0Labels = mixedMoment B raw13419step1 raw13419step1Labels := by
      have ha : raw13419step1 = (fun i j => raw13419step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13419step1 raw13419step0; decide +kernel
      have hl : raw13419step1Labels = raw13419step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13419step0 raw13419step0Labels permutation32 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw13420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13420 raw13420Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw13420 raw13420Labels = mixedMoment B raw13420step0 raw13420step0Labels := by
      have ha : raw13420step0 = (fun i j => raw13420 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13420step0 raw13420; decide +kernel
      have hl : raw13420step0Labels = raw13420Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13420 raw13420Labels permutation155 permutation3
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw13421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13421 raw13421Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw13421 raw13421Labels = mixedMoment B raw13421step0 raw13421step0Labels := by
      have ha : raw13421step0 = (fun i j => raw13421 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13421step0 raw13421; decide +kernel
      have hl : raw13421step0Labels = raw13421Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13421 raw13421Labels permutation155 permutation3
    _ = mixedMoment B node2853 node2853Labels := by rfl

def raw13422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13422 raw13422Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw13422 raw13422Labels = mixedMoment B raw13422step0 raw13422step0Labels := by
      have ha : raw13422step0 = (fun i j => raw13422 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13422step0 raw13422; decide +kernel
      have hl : raw13422step0Labels = raw13422Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13422 raw13422Labels permutation179 permutation3
    _ = mixedMoment B node2853 node2853Labels := by rfl

def raw13423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw13423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw13423step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13423 raw13423Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw13423 raw13423Labels = mixedMoment B raw13423step0 raw13423step0Labels := by
      have hz : ∀ j, raw13423 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13423step0 = (fun i j => raw13423 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13423step0 raw13423; decide +kernel
      have hl : raw13423step0Labels = raw13423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13423 raw13423Labels permutation520 hz
    mixedMoment B raw13423step0 raw13423step0Labels = mixedMoment B raw13423step1 raw13423step1Labels := by
      have ha : raw13423step1 = (fun i j => raw13423step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13423step1 raw13423step0; decide +kernel
      have hl : raw13423step1Labels = raw13423step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13423step0 raw13423step0Labels permutation33 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw13424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw13424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw13424step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13424 raw13424Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw13424 raw13424Labels = mixedMoment B raw13424step0 raw13424step0Labels := by
      have hz : ∀ j, raw13424 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13424step0 = (fun i j => raw13424 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13424step0 raw13424; decide +kernel
      have hl : raw13424step0Labels = raw13424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13424 raw13424Labels permutation590 hz
    mixedMoment B raw13424step0 raw13424step0Labels = mixedMoment B raw13424step1 raw13424step1Labels := by
      have ha : raw13424step1 = (fun i j => raw13424step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13424step1 raw13424step0; decide +kernel
      have hl : raw13424step1Labels = raw13424step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13424step0 raw13424step0Labels permutation33 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw13425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13425Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13425 raw13425Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw13425 raw13425Labels = mixedMoment B raw13425step0 raw13425step0Labels := by
      have ha : raw13425step0 = (fun i j => raw13425 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13425step0 raw13425; decide +kernel
      have hl : raw13425step0Labels = raw13425Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13425 raw13425Labels permutation153 permutation3
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw13426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13426Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13426 raw13426Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw13426 raw13426Labels = mixedMoment B raw13426step0 raw13426step0Labels := by
      have ha : raw13426step0 = (fun i j => raw13426 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13426step0 raw13426; decide +kernel
      have hl : raw13426step0Labels = raw13426Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13426 raw13426Labels permutation153 permutation3
    _ = mixedMoment B node2853 node2853Labels := by rfl

def raw13427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13427Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13427 raw13427Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw13427 raw13427Labels = mixedMoment B raw13427step0 raw13427step0Labels := by
      have ha : raw13427step0 = (fun i j => raw13427 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13427step0 raw13427; decide +kernel
      have hl : raw13427step0Labels = raw13427Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13427 raw13427Labels permutation177 permutation3
    _ = mixedMoment B node2853 node2853Labels := by rfl

def raw13428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw13428Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw13428step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13428 raw13428Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw13428 raw13428Labels = mixedMoment B raw13428step0 raw13428step0Labels := by
      have hz : ∀ j, raw13428 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13428step0 = (fun i j => raw13428 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13428step0 raw13428; decide +kernel
      have hl : raw13428step0Labels = raw13428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13428 raw13428Labels permutation434 hz
    mixedMoment B raw13428step0 raw13428step0Labels = mixedMoment B raw13428step1 raw13428step1Labels := by
      have ha : raw13428step1 = (fun i j => raw13428step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13428step1 raw13428step0; decide +kernel
      have hl : raw13428step1Labels = raw13428step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13428step0 raw13428step0Labels permutation33 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw13429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw13429Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13429step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13429 raw13429Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw13429 raw13429Labels = mixedMoment B raw13429step0 raw13429step0Labels := by
      have hz : ∀ j, raw13429 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13429step0 = (fun i j => raw13429 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13429step0 raw13429; decide +kernel
      have hl : raw13429step0Labels = raw13429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13429 raw13429Labels permutation590 hz
    mixedMoment B raw13429step0 raw13429step0Labels = mixedMoment B raw13429step1 raw13429step1Labels := by
      have ha : raw13429step1 = (fun i j => raw13429step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13429step1 raw13429step0; decide +kernel
      have hl : raw13429step1Labels = raw13429step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13429step0 raw13429step0Labels permutation32 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw13430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13430Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13430 raw13430Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw13430 raw13430Labels = mixedMoment B raw13430step0 raw13430step0Labels := by
      have ha : raw13430step0 = (fun i j => raw13430 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13430step0 raw13430; decide +kernel
      have hl : raw13430step0Labels = raw13430Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13430 raw13430Labels permutation152 permutation3
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw13431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13431Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13431 raw13431Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw13431 raw13431Labels = mixedMoment B raw13431step0 raw13431step0Labels := by
      have ha : raw13431step0 = (fun i j => raw13431 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13431step0 raw13431; decide +kernel
      have hl : raw13431step0Labels = raw13431Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13431 raw13431Labels permutation152 permutation3
    _ = mixedMoment B node2853 node2853Labels := by rfl

def raw13432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13432Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13432 raw13432Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw13432 raw13432Labels = mixedMoment B raw13432step0 raw13432step0Labels := by
      have ha : raw13432step0 = (fun i j => raw13432 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13432step0 raw13432; decide +kernel
      have hl : raw13432step0Labels = raw13432Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13432 raw13432Labels permutation176 permutation3
    _ = mixedMoment B node2853 node2853Labels := by rfl

def raw13433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw13433Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13433step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13433 raw13433Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw13433 raw13433Labels = mixedMoment B raw13433step0 raw13433step0Labels := by
      have hz : ∀ j, raw13433 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13433step0 = (fun i j => raw13433 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13433step0 raw13433; decide +kernel
      have hl : raw13433step0Labels = raw13433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13433 raw13433Labels permutation434 hz
    mixedMoment B raw13433step0 raw13433step0Labels = mixedMoment B raw13433step1 raw13433step1Labels := by
      have ha : raw13433step1 = (fun i j => raw13433step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13433step1 raw13433step0; decide +kernel
      have hl : raw13433step1Labels = raw13433step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13433step0 raw13433step0Labels permutation32 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw13434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw13434Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13434step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13434 raw13434Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw13434 raw13434Labels = mixedMoment B raw13434step0 raw13434step0Labels := by
      have hz : ∀ j, raw13434 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13434step0 = (fun i j => raw13434 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13434step0 raw13434; decide +kernel
      have hl : raw13434step0Labels = raw13434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13434 raw13434Labels permutation520 hz
    mixedMoment B raw13434step0 raw13434step0Labels = mixedMoment B raw13434step1 raw13434step1Labels := by
      have ha : raw13434step1 = (fun i j => raw13434step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13434step1 raw13434step0; decide +kernel
      have hl : raw13434step1Labels = raw13434step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13434step0 raw13434step0Labels permutation32 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw13435 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13435step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13435step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13435 raw13435Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw13435 raw13435Labels = mixedMoment B raw13435step0 raw13435step0Labels := by
      have hz : ∀ j, raw13435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13435step0 = (fun i j => raw13435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13435step0 raw13435; decide +kernel
      have hl : raw13435step0Labels = raw13435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13435 raw13435Labels permutation346 hz
    mixedMoment B raw13435step0 raw13435step0Labels = mixedMoment B raw13435step1 raw13435step1Labels := by
      have ha : raw13435step1 = (fun i j => raw13435step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13435step1 raw13435step0; decide +kernel
      have hl : raw13435step1Labels = raw13435step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13435step0 raw13435step0Labels permutation32 permutation7
    mixedMoment B raw13435step1 raw13435step1Labels = mixedMoment B raw13435step2 raw13435step2Labels := by
      have ha : raw13435step2 = raw13435step1 := by apply Matrix.ext; unfold raw13435step2 raw13435step1; decide +kernel
      have hl : raw13435step1Labels = labelEmbedding10 ∘ raw13435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13435step1 raw13435step1Labels raw13435step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw13436 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13436step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13436step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13436 raw13436Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw13436 raw13436Labels = mixedMoment B raw13436step0 raw13436step0Labels := by
      have ha : raw13436step0 = (fun i j => raw13436 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13436step0 raw13436; decide +kernel
      have hl : raw13436step0Labels = raw13436Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13436 raw13436Labels permutation153 permutation7
    mixedMoment B raw13436step0 raw13436step0Labels = mixedMoment B raw13436step1 raw13436step1Labels := by
      have ha : raw13436step1 = raw13436step0 := by apply Matrix.ext; unfold raw13436step1 raw13436step0; decide +kernel
      have hl : raw13436step0Labels = labelEmbedding10 ∘ raw13436step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13436step0 raw13436step0Labels raw13436step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

def raw13437 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13437step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13437step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13437 raw13437Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw13437 raw13437Labels = mixedMoment B raw13437step0 raw13437step0Labels := by
      have ha : raw13437step0 = (fun i j => raw13437 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13437step0 raw13437; decide +kernel
      have hl : raw13437step0Labels = raw13437Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13437 raw13437Labels permutation152 permutation7
    mixedMoment B raw13437step0 raw13437step0Labels = mixedMoment B raw13437step1 raw13437step1Labels := by
      have ha : raw13437step1 = raw13437step0 := by apply Matrix.ext; unfold raw13437step1 raw13437step0; decide +kernel
      have hl : raw13437step0Labels = labelEmbedding10 ∘ raw13437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13437step0 raw13437step0Labels raw13437step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

def raw13438 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw13438step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13438step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13438step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13438step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13438 raw13438Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw13438 raw13438Labels = mixedMoment B raw13438step0 raw13438step0Labels := by
      have ha : raw13438step0 = (fun i j => raw13438 (permutation217 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13438step0 raw13438; decide +kernel
      have hl : raw13438step0Labels = raw13438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13438 raw13438Labels permutation217 permutation4
    mixedMoment B raw13438step0 raw13438step0Labels = mixedMoment B raw13438step1 raw13438step1Labels := by
      have ha : raw13438step1 = -raw13438step0 := by apply Matrix.ext; change ∀ i j, raw13438step1 i j = -(raw13438step0 i j); unfold raw13438step1 raw13438step0; decide +kernel
      have hl : raw13438step1Labels = raw13438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13438step1 raw13438step1Labels = mixedMoment B raw13438step2 raw13438step2Labels := by
      have ha : raw13438step2 = raw13438step1 := by apply Matrix.ext; unfold raw13438step2 raw13438step1; decide +kernel
      have hl : raw13438step1Labels = labelEmbedding7 ∘ raw13438step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13438step1 raw13438step1Labels raw13438step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw13439 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13439step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13439step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13439 raw13439Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw13439 raw13439Labels = mixedMoment B raw13439step0 raw13439step0Labels := by
      have hz : ∀ j, raw13439 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13439step0 = (fun i j => raw13439 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13439step0 raw13439; decide +kernel
      have hl : raw13439step0Labels = raw13439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13439 raw13439Labels permutation346 hz
    mixedMoment B raw13439step0 raw13439step0Labels = mixedMoment B raw13439step1 raw13439step1Labels := by
      have ha : raw13439step1 = (fun i j => raw13439step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13439step1 raw13439step0; decide +kernel
      have hl : raw13439step1Labels = raw13439step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13439step0 raw13439step0Labels permutation32 permutation6
    mixedMoment B raw13439step1 raw13439step1Labels = mixedMoment B raw13439step2 raw13439step2Labels := by
      have ha : raw13439step2 = raw13439step1 := by apply Matrix.ext; unfold raw13439step2 raw13439step1; decide +kernel
      have hl : raw13439step1Labels = labelEmbedding9 ∘ raw13439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13439step1 raw13439step1Labels raw13439step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
