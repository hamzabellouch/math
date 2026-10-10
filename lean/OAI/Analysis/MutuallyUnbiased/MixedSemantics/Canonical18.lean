import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2304 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2304step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2304step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2304 raw2304Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw2304 raw2304Labels = mixedMoment B raw2304step0 raw2304step0Labels := by
      have ha : raw2304step0 = (fun i j => raw2304 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2304step0 raw2304; decide +kernel
      have hl : raw2304step0Labels = raw2304Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2304 raw2304Labels permutation8 permutation4
    mixedMoment B raw2304step0 raw2304step0Labels = mixedMoment B raw2304step1 raw2304step1Labels := by
      have ha : raw2304step1 = raw2304step0 := by apply Matrix.ext; unfold raw2304step1 raw2304step0; decide +kernel
      have hl : raw2304step0Labels = labelEmbedding7 ∘ raw2304step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2304step0 raw2304step0Labels raw2304step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw2305 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2305step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2305 raw2305Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw2305 raw2305Labels = mixedMoment B raw2305step0 raw2305step0Labels := by
      have ha : raw2305step0 = (fun i j => raw2305 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2305step0 raw2305; decide +kernel
      have hl : raw2305step0Labels = raw2305Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2305 raw2305Labels permutation8 permutation4
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw2306 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2306Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2306step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw2306step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2306step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2306 raw2306Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw2306 raw2306Labels = mixedMoment B raw2306step0 raw2306step0Labels := by
      have ha : raw2306step0 = (fun i j => raw2306 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2306step0 raw2306; decide +kernel
      have hl : raw2306step0Labels = raw2306Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2306 raw2306Labels permutation12 permutation6
    mixedMoment B raw2306step0 raw2306step0Labels = mixedMoment B raw2306step1 raw2306step1Labels := by
      have ha : raw2306step1 = -raw2306step0 := by apply Matrix.ext; change ∀ i j, raw2306step1 i j = -(raw2306step0 i j); unfold raw2306step1 raw2306step0; decide +kernel
      have hl : raw2306step1Labels = raw2306step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2306step1 raw2306step1Labels = mixedMoment B raw2306step2 raw2306step2Labels := by
      have ha : raw2306step2 = raw2306step1 := by apply Matrix.ext; unfold raw2306step2 raw2306step1; decide +kernel
      have hl : raw2306step1Labels = labelEmbedding1 ∘ raw2306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2306step1 raw2306step1Labels raw2306step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3632 node3632Labels := by rfl

def raw2307 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 3, -1]]
def raw2307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2307step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw2307step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2307step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw2307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2307 raw2307Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw2307 raw2307Labels = mixedMoment B raw2307step0 raw2307step0Labels := by
      have ha : raw2307step0 = (fun i j => raw2307 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2307step0 raw2307; decide +kernel
      have hl : raw2307step0Labels = raw2307Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2307 raw2307Labels permutation2 permutation4
    mixedMoment B raw2307step0 raw2307step0Labels = mixedMoment B raw2307step1 raw2307step1Labels := by
      have ha : raw2307step1 = raw2307step0 := by apply Matrix.ext; unfold raw2307step1 raw2307step0; decide +kernel
      have hl : raw2307step0Labels = labelEmbedding7 ∘ raw2307step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2307step0 raw2307step0Labels raw2307step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw2308 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 3, -1]]
def raw2308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2308step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw2308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2308 raw2308Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw2308 raw2308Labels = mixedMoment B raw2308step0 raw2308step0Labels := by
      have ha : raw2308step0 = (fun i j => raw2308 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2308step0 raw2308; decide +kernel
      have hl : raw2308step0Labels = raw2308Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2308 raw2308Labels permutation2 permutation4
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw2309 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 3, -1]]
def raw2309Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2309step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]
def raw2309step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2309step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]
def raw2309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2309 raw2309Labels = mixedMoment B node3634 node3634Labels := by
  calc
    mixedMoment B raw2309 raw2309Labels = mixedMoment B raw2309step0 raw2309step0Labels := by
      have ha : raw2309step0 = (fun i j => raw2309 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2309step0 raw2309; decide +kernel
      have hl : raw2309step0Labels = raw2309Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2309 raw2309Labels permutation7 permutation3
    mixedMoment B raw2309step0 raw2309step0Labels = mixedMoment B raw2309step1 raw2309step1Labels := by
      have ha : raw2309step1 = raw2309step0 := by apply Matrix.ext; unfold raw2309step1 raw2309step0; decide +kernel
      have hl : raw2309step0Labels = labelEmbedding1 ∘ raw2309step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2309step0 raw2309step0Labels raw2309step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3634 node3634Labels := by rfl

def raw2310 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2310step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2310 raw2310Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw2310 raw2310Labels = mixedMoment B raw2310step0 raw2310step0Labels := by
      have ha : raw2310step0 = (fun i j => raw2310 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2310step0 raw2310; decide +kernel
      have hl : raw2310step0Labels = raw2310Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2310 raw2310Labels permutation32 permutation5
    mixedMoment B raw2310step0 raw2310step0Labels = mixedMoment B raw2310step1 raw2310step1Labels := by
      have ha : raw2310step1 = raw2310step0 := by apply Matrix.ext; unfold raw2310step1 raw2310step0; decide +kernel
      have hl : raw2310step0Labels = labelEmbedding8 ∘ raw2310step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2310step0 raw2310step0Labels raw2310step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw2311 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2311 raw2311Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw2311 raw2311Labels = mixedMoment B raw2311step0 raw2311step0Labels := by
      have ha : raw2311step0 = (fun i j => raw2311 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2311step0 raw2311; decide +kernel
      have hl : raw2311step0Labels = raw2311Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2311 raw2311Labels permutation32 permutation4
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw2312 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2312Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2312step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2312 raw2312Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw2312 raw2312Labels = mixedMoment B raw2312step0 raw2312step0Labels := by
      have ha : raw2312step0 = (fun i j => raw2312 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2312step0 raw2312; decide +kernel
      have hl : raw2312step0Labels = raw2312Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2312 raw2312Labels permutation41 permutation3
    mixedMoment B raw2312step0 raw2312step0Labels = mixedMoment B raw2312step1 raw2312step1Labels := by
      have ha : raw2312step1 = -raw2312step0 := by apply Matrix.ext; change ∀ i j, raw2312step1 i j = -(raw2312step0 i j); unfold raw2312step1 raw2312step0; decide +kernel
      have hl : raw2312step1Labels = raw2312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2312step1 raw2312step1Labels = mixedMoment B raw2312step2 raw2312step2Labels := by
      have ha : raw2312step2 = raw2312step1 := by apply Matrix.ext; unfold raw2312step2 raw2312step1; decide +kernel
      have hl : raw2312step1Labels = labelEmbedding1 ∘ raw2312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2312step1 raw2312step1Labels raw2312step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw2313 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw2313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2313step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2313step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2313 raw2313Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2313 raw2313Labels = mixedMoment B raw2313step0 raw2313step0Labels := by
      have ha : raw2313step0 = (fun i j => raw2313 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2313step0 raw2313; decide +kernel
      have hl : raw2313step0Labels = raw2313Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2313 raw2313Labels permutation8 permutation5
    mixedMoment B raw2313step0 raw2313step0Labels = mixedMoment B raw2313step1 raw2313step1Labels := by
      have ha : raw2313step1 = raw2313step0 := by apply Matrix.ext; unfold raw2313step1 raw2313step0; decide +kernel
      have hl : raw2313step0Labels = labelEmbedding8 ∘ raw2313step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2313step0 raw2313step0Labels raw2313step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw2314 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw2314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2314step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw2314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2314 raw2314Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw2314 raw2314Labels = mixedMoment B raw2314step0 raw2314step0Labels := by
      have ha : raw2314step0 = (fun i j => raw2314 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2314step0 raw2314; decide +kernel
      have hl : raw2314step0Labels = raw2314Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2314 raw2314Labels permutation8 permutation4
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw2315 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw2315Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2315step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw2315step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw2315step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw2315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2315 raw2315Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw2315 raw2315Labels = mixedMoment B raw2315step0 raw2315step0Labels := by
      have ha : raw2315step0 = (fun i j => raw2315 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2315step0 raw2315; decide +kernel
      have hl : raw2315step0Labels = raw2315Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2315 raw2315Labels permutation11 permutation3
    mixedMoment B raw2315step0 raw2315step0Labels = mixedMoment B raw2315step1 raw2315step1Labels := by
      have ha : raw2315step1 = -raw2315step0 := by apply Matrix.ext; change ∀ i j, raw2315step1 i j = -(raw2315step0 i j); unfold raw2315step1 raw2315step0; decide +kernel
      have hl : raw2315step1Labels = raw2315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2315step1 raw2315step1Labels = mixedMoment B raw2315step2 raw2315step2Labels := by
      have ha : raw2315step2 = raw2315step1 := by apply Matrix.ext; unfold raw2315step2 raw2315step1; decide +kernel
      have hl : raw2315step1Labels = labelEmbedding1 ∘ raw2315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2315step1 raw2315step1Labels raw2315step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw2316 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2316step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2316step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2316 raw2316Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw2316 raw2316Labels = mixedMoment B raw2316step0 raw2316step0Labels := by
      have ha : raw2316step0 = (fun i j => raw2316 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2316step0 raw2316; decide +kernel
      have hl : raw2316step0Labels = raw2316Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2316 raw2316Labels permutation8 permutation4
    mixedMoment B raw2316step0 raw2316step0Labels = mixedMoment B raw2316step1 raw2316step1Labels := by
      have ha : raw2316step1 = raw2316step0 := by apply Matrix.ext; unfold raw2316step1 raw2316step0; decide +kernel
      have hl : raw2316step0Labels = labelEmbedding7 ∘ raw2316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2316step0 raw2316step0Labels raw2316step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw2317 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2317step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2317 raw2317Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw2317 raw2317Labels = mixedMoment B raw2317step0 raw2317step0Labels := by
      have ha : raw2317step0 = (fun i j => raw2317 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2317step0 raw2317; decide +kernel
      have hl : raw2317step0Labels = raw2317Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2317 raw2317Labels permutation8 permutation4
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw2318 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2318Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2318step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2318step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2318 raw2318Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw2318 raw2318Labels = mixedMoment B raw2318step0 raw2318step0Labels := by
      have ha : raw2318step0 = (fun i j => raw2318 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2318step0 raw2318; decide +kernel
      have hl : raw2318step0Labels = raw2318Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2318 raw2318Labels permutation8 permutation6
    mixedMoment B raw2318step0 raw2318step0Labels = mixedMoment B raw2318step1 raw2318step1Labels := by
      have ha : raw2318step1 = -raw2318step0 := by apply Matrix.ext; change ∀ i j, raw2318step1 i j = -(raw2318step0 i j); unfold raw2318step1 raw2318step0; decide +kernel
      have hl : raw2318step1Labels = raw2318step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2318step1 raw2318step1Labels = mixedMoment B raw2318step2 raw2318step2Labels := by
      have ha : raw2318step2 = raw2318step1 := by apply Matrix.ext; unfold raw2318step2 raw2318step1; decide +kernel
      have hl : raw2318step1Labels = labelEmbedding1 ∘ raw2318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2318step1 raw2318step1Labels raw2318step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw2319 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]
def raw2319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2319step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2319step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2319step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2319step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2319 raw2319Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw2319 raw2319Labels = mixedMoment B raw2319step0 raw2319step0Labels := by
      have ha : raw2319step0 = (fun i j => raw2319 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2319step0 raw2319; decide +kernel
      have hl : raw2319step0Labels = raw2319Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2319 raw2319Labels permutation2 permutation4
    mixedMoment B raw2319step0 raw2319step0Labels = mixedMoment B raw2319step1 raw2319step1Labels := by
      have ha : raw2319step1 = raw2319step0 := by apply Matrix.ext; unfold raw2319step1 raw2319step0; decide +kernel
      have hl : raw2319step0Labels = labelEmbedding7 ∘ raw2319step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2319step0 raw2319step0Labels raw2319step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5305 node5305Labels := by rfl

def raw2320 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]
def raw2320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2320step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2320 raw2320Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw2320 raw2320Labels = mixedMoment B raw2320step0 raw2320step0Labels := by
      have ha : raw2320step0 = (fun i j => raw2320 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2320step0 raw2320; decide +kernel
      have hl : raw2320step0Labels = raw2320Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2320 raw2320Labels permutation2 permutation4
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw2321 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]
def raw2321Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2321step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2321step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2321 raw2321Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw2321 raw2321Labels = mixedMoment B raw2321step0 raw2321step0Labels := by
      have ha : raw2321step0 = (fun i j => raw2321 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2321step0 raw2321; decide +kernel
      have hl : raw2321step0Labels = raw2321Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2321 raw2321Labels permutation7 permutation6
    mixedMoment B raw2321step0 raw2321step0Labels = mixedMoment B raw2321step1 raw2321step1Labels := by
      have ha : raw2321step1 = raw2321step0 := by apply Matrix.ext; unfold raw2321step1 raw2321step0; decide +kernel
      have hl : raw2321step0Labels = labelEmbedding1 ∘ raw2321step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2321step0 raw2321step0Labels raw2321step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw2322 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2322step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2322step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2322 raw2322Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw2322 raw2322Labels = mixedMoment B raw2322step0 raw2322step0Labels := by
      have ha : raw2322step0 = (fun i j => raw2322 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2322step0 raw2322; decide +kernel
      have hl : raw2322step0Labels = raw2322Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2322 raw2322Labels permutation8 permutation4
    mixedMoment B raw2322step0 raw2322step0Labels = mixedMoment B raw2322step1 raw2322step1Labels := by
      have ha : raw2322step1 = raw2322step0 := by apply Matrix.ext; unfold raw2322step1 raw2322step0; decide +kernel
      have hl : raw2322step0Labels = labelEmbedding7 ∘ raw2322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2322step0 raw2322step0Labels raw2322step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw2323 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2323step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2323 raw2323Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw2323 raw2323Labels = mixedMoment B raw2323step0 raw2323step0Labels := by
      have ha : raw2323step0 = (fun i j => raw2323 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2323step0 raw2323; decide +kernel
      have hl : raw2323step0Labels = raw2323Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2323 raw2323Labels permutation8 permutation4
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw2324 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2324Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2324step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw2324step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2324step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2324 raw2324Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw2324 raw2324Labels = mixedMoment B raw2324step0 raw2324step0Labels := by
      have ha : raw2324step0 = (fun i j => raw2324 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2324step0 raw2324; decide +kernel
      have hl : raw2324step0Labels = raw2324Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2324 raw2324Labels permutation8 permutation6
    mixedMoment B raw2324step0 raw2324step0Labels = mixedMoment B raw2324step1 raw2324step1Labels := by
      have ha : raw2324step1 = -raw2324step0 := by apply Matrix.ext; change ∀ i j, raw2324step1 i j = -(raw2324step0 i j); unfold raw2324step1 raw2324step0; decide +kernel
      have hl : raw2324step1Labels = raw2324step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2324step1 raw2324step1Labels = mixedMoment B raw2324step2 raw2324step2Labels := by
      have ha : raw2324step2 = raw2324step1 := by apply Matrix.ext; unfold raw2324step2 raw2324step1; decide +kernel
      have hl : raw2324step1Labels = labelEmbedding1 ∘ raw2324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2324step1 raw2324step1Labels raw2324step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3623 node3623Labels := by rfl

def raw2325 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 2, 0]]
def raw2325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2325step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2325step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2325step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2325 raw2325Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw2325 raw2325Labels = mixedMoment B raw2325step0 raw2325step0Labels := by
      have ha : raw2325step0 = (fun i j => raw2325 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2325step0 raw2325; decide +kernel
      have hl : raw2325step0Labels = raw2325Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2325 raw2325Labels permutation2 permutation4
    mixedMoment B raw2325step0 raw2325step0Labels = mixedMoment B raw2325step1 raw2325step1Labels := by
      have ha : raw2325step1 = raw2325step0 := by apply Matrix.ext; unfold raw2325step1 raw2325step0; decide +kernel
      have hl : raw2325step0Labels = labelEmbedding7 ∘ raw2325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2325step0 raw2325step0Labels raw2325step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw2326 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 2, 0]]
def raw2326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2326step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2326 raw2326Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw2326 raw2326Labels = mixedMoment B raw2326step0 raw2326step0Labels := by
      have ha : raw2326step0 = (fun i j => raw2326 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2326step0 raw2326; decide +kernel
      have hl : raw2326step0Labels = raw2326Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2326 raw2326Labels permutation2 permutation4
    _ = mixedMoment B node2788 node2788Labels := by rfl

def raw2327 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 2, 0]]
def raw2327Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2327step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-2, 1, 1]]
def raw2327step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2327step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw2327step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2327step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw2327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2327 raw2327Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw2327 raw2327Labels = mixedMoment B raw2327step0 raw2327step0Labels := by
      have ha : raw2327step0 = (fun i j => raw2327 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2327step0 raw2327; decide +kernel
      have hl : raw2327step0Labels = raw2327Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2327 raw2327Labels permutation3 permutation6
    mixedMoment B raw2327step0 raw2327step0Labels = mixedMoment B raw2327step1 raw2327step1Labels := by
      have ha : raw2327step1 = -raw2327step0 := by apply Matrix.ext; change ∀ i j, raw2327step1 i j = -(raw2327step0 i j); unfold raw2327step1 raw2327step0; decide +kernel
      have hl : raw2327step1Labels = raw2327step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2327step1 raw2327step1Labels = mixedMoment B raw2327step2 raw2327step2Labels := by
      have ha : raw2327step2 = raw2327step1 := by apply Matrix.ext; unfold raw2327step2 raw2327step1; decide +kernel
      have hl : raw2327step1Labels = labelEmbedding1 ∘ raw2327step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2327step1 raw2327step1Labels raw2327step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3633 node3633Labels := by rfl

def raw2328 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2328step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2328step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2328 raw2328Labels = mixedMoment B node5315 node5315Labels := by
  calc
    mixedMoment B raw2328 raw2328Labels = mixedMoment B raw2328step0 raw2328step0Labels := by
      have ha : raw2328step0 = (fun i j => raw2328 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2328step0 raw2328; decide +kernel
      have hl : raw2328step0Labels = raw2328Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2328 raw2328Labels permutation152 permutation4
    mixedMoment B raw2328step0 raw2328step0Labels = mixedMoment B raw2328step1 raw2328step1Labels := by
      have ha : raw2328step1 = raw2328step0 := by apply Matrix.ext; unfold raw2328step1 raw2328step0; decide +kernel
      have hl : raw2328step0Labels = labelEmbedding7 ∘ raw2328step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2328step0 raw2328step0Labels raw2328step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5315 node5315Labels := by rfl

def raw2329 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2329 raw2329Labels = mixedMoment B node3638 node3638Labels := by
  calc
    mixedMoment B raw2329 raw2329Labels = mixedMoment B raw2329step0 raw2329step0Labels := by
      have ha : raw2329step0 = (fun i j => raw2329 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2329step0 raw2329; decide +kernel
      have hl : raw2329step0Labels = raw2329Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2329 raw2329Labels permutation152 permutation4
    _ = mixedMoment B node3638 node3638Labels := by rfl

def raw2330 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2330Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw2330step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw2330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2330step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw2330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2330 raw2330Labels = mixedMoment B node3643 node3643Labels := by
  calc
    mixedMoment B raw2330 raw2330Labels = mixedMoment B raw2330step0 raw2330step0Labels := by
      have ha : raw2330step0 = (fun i j => raw2330 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2330step0 raw2330; decide +kernel
      have hl : raw2330step0Labels = raw2330Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2330 raw2330Labels permutation154 permutation6
    mixedMoment B raw2330step0 raw2330step0Labels = mixedMoment B raw2330step1 raw2330step1Labels := by
      have ha : raw2330step1 = -raw2330step0 := by apply Matrix.ext; change ∀ i j, raw2330step1 i j = -(raw2330step0 i j); unfold raw2330step1 raw2330step0; decide +kernel
      have hl : raw2330step1Labels = raw2330step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2330step1 raw2330step1Labels = mixedMoment B raw2330step2 raw2330step2Labels := by
      have ha : raw2330step2 = raw2330step1 := by apply Matrix.ext; unfold raw2330step2 raw2330step1; decide +kernel
      have hl : raw2330step1Labels = labelEmbedding1 ∘ raw2330step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2330step1 raw2330step1Labels raw2330step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3643 node3643Labels := by rfl

def raw2331 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2331step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2331 raw2331Labels = mixedMoment B node5316 node5316Labels := by
  calc
    mixedMoment B raw2331 raw2331Labels = mixedMoment B raw2331step0 raw2331step0Labels := by
      have ha : raw2331step0 = (fun i j => raw2331 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2331step0 raw2331; decide +kernel
      have hl : raw2331step0Labels = raw2331Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2331 raw2331Labels permutation152 permutation4
    mixedMoment B raw2331step0 raw2331step0Labels = mixedMoment B raw2331step1 raw2331step1Labels := by
      have ha : raw2331step1 = raw2331step0 := by apply Matrix.ext; unfold raw2331step1 raw2331step0; decide +kernel
      have hl : raw2331step0Labels = labelEmbedding7 ∘ raw2331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2331step0 raw2331step0Labels raw2331step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5316 node5316Labels := by rfl

def raw2332 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2332 raw2332Labels = mixedMoment B node3639 node3639Labels := by
  calc
    mixedMoment B raw2332 raw2332Labels = mixedMoment B raw2332step0 raw2332step0Labels := by
      have ha : raw2332step0 = (fun i j => raw2332 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2332step0 raw2332; decide +kernel
      have hl : raw2332step0Labels = raw2332Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2332 raw2332Labels permutation152 permutation4
    _ = mixedMoment B node3639 node3639Labels := by rfl

def raw2333 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2333Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw2333step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw2333step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2333step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw2333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2333 raw2333Labels = mixedMoment B node3645 node3645Labels := by
  calc
    mixedMoment B raw2333 raw2333Labels = mixedMoment B raw2333step0 raw2333step0Labels := by
      have ha : raw2333step0 = (fun i j => raw2333 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2333step0 raw2333; decide +kernel
      have hl : raw2333step0Labels = raw2333Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2333 raw2333Labels permutation155 permutation6
    mixedMoment B raw2333step0 raw2333step0Labels = mixedMoment B raw2333step1 raw2333step1Labels := by
      have ha : raw2333step1 = -raw2333step0 := by apply Matrix.ext; change ∀ i j, raw2333step1 i j = -(raw2333step0 i j); unfold raw2333step1 raw2333step0; decide +kernel
      have hl : raw2333step1Labels = raw2333step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2333step1 raw2333step1Labels = mixedMoment B raw2333step2 raw2333step2Labels := by
      have ha : raw2333step2 = raw2333step1 := by apply Matrix.ext; unfold raw2333step2 raw2333step1; decide +kernel
      have hl : raw2333step1Labels = labelEmbedding1 ∘ raw2333step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2333step1 raw2333step1Labels raw2333step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3645 node3645Labels := by rfl

def raw2334 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2334step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2334 raw2334Labels = mixedMoment B node5317 node5317Labels := by
  calc
    mixedMoment B raw2334 raw2334Labels = mixedMoment B raw2334step0 raw2334step0Labels := by
      have ha : raw2334step0 = (fun i j => raw2334 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2334step0 raw2334; decide +kernel
      have hl : raw2334step0Labels = raw2334Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2334 raw2334Labels permutation152 permutation4
    mixedMoment B raw2334step0 raw2334step0Labels = mixedMoment B raw2334step1 raw2334step1Labels := by
      have ha : raw2334step1 = raw2334step0 := by apply Matrix.ext; unfold raw2334step1 raw2334step0; decide +kernel
      have hl : raw2334step0Labels = labelEmbedding7 ∘ raw2334step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2334step0 raw2334step0Labels raw2334step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5317 node5317Labels := by rfl

def raw2335 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2335 raw2335Labels = mixedMoment B node3640 node3640Labels := by
  calc
    mixedMoment B raw2335 raw2335Labels = mixedMoment B raw2335step0 raw2335step0Labels := by
      have ha : raw2335step0 = (fun i j => raw2335 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2335step0 raw2335; decide +kernel
      have hl : raw2335step0Labels = raw2335Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2335 raw2335Labels permutation152 permutation4
    _ = mixedMoment B node3640 node3640Labels := by rfl

def raw2336 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2336Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw2336step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2336step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2336step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2336step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2336 raw2336Labels = mixedMoment B node3649 node3649Labels := by
  calc
    mixedMoment B raw2336 raw2336Labels = mixedMoment B raw2336step0 raw2336step0Labels := by
      have ha : raw2336step0 = (fun i j => raw2336 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2336step0 raw2336; decide +kernel
      have hl : raw2336step0Labels = raw2336Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2336 raw2336Labels permutation158 permutation6
    mixedMoment B raw2336step0 raw2336step0Labels = mixedMoment B raw2336step1 raw2336step1Labels := by
      have ha : raw2336step1 = -raw2336step0 := by apply Matrix.ext; change ∀ i j, raw2336step1 i j = -(raw2336step0 i j); unfold raw2336step1 raw2336step0; decide +kernel
      have hl : raw2336step1Labels = raw2336step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2336step1 raw2336step1Labels = mixedMoment B raw2336step2 raw2336step2Labels := by
      have ha : raw2336step2 = raw2336step1 := by apply Matrix.ext; unfold raw2336step2 raw2336step1; decide +kernel
      have hl : raw2336step1Labels = labelEmbedding1 ∘ raw2336step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2336step1 raw2336step1Labels raw2336step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3649 node3649Labels := by rfl

def raw2337 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2337step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2337 raw2337Labels = mixedMoment B node5318 node5318Labels := by
  calc
    mixedMoment B raw2337 raw2337Labels = mixedMoment B raw2337step0 raw2337step0Labels := by
      have ha : raw2337step0 = (fun i j => raw2337 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2337step0 raw2337; decide +kernel
      have hl : raw2337step0Labels = raw2337Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2337 raw2337Labels permutation152 permutation4
    mixedMoment B raw2337step0 raw2337step0Labels = mixedMoment B raw2337step1 raw2337step1Labels := by
      have ha : raw2337step1 = raw2337step0 := by apply Matrix.ext; unfold raw2337step1 raw2337step0; decide +kernel
      have hl : raw2337step0Labels = labelEmbedding7 ∘ raw2337step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2337step0 raw2337step0Labels raw2337step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5318 node5318Labels := by rfl

def raw2338 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2338 raw2338Labels = mixedMoment B node3641 node3641Labels := by
  calc
    mixedMoment B raw2338 raw2338Labels = mixedMoment B raw2338step0 raw2338step0Labels := by
      have ha : raw2338step0 = (fun i j => raw2338 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2338step0 raw2338; decide +kernel
      have hl : raw2338step0Labels = raw2338Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2338 raw2338Labels permutation152 permutation4
    _ = mixedMoment B node3641 node3641Labels := by rfl

def raw2339 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2339Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw2339step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2339step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2339step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2339step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2339 raw2339Labels = mixedMoment B node3655 node3655Labels := by
  calc
    mixedMoment B raw2339 raw2339Labels = mixedMoment B raw2339step0 raw2339step0Labels := by
      have ha : raw2339step0 = (fun i j => raw2339 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2339step0 raw2339; decide +kernel
      have hl : raw2339step0Labels = raw2339Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2339 raw2339Labels permutation164 permutation6
    mixedMoment B raw2339step0 raw2339step0Labels = mixedMoment B raw2339step1 raw2339step1Labels := by
      have ha : raw2339step1 = -raw2339step0 := by apply Matrix.ext; change ∀ i j, raw2339step1 i j = -(raw2339step0 i j); unfold raw2339step1 raw2339step0; decide +kernel
      have hl : raw2339step1Labels = raw2339step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2339step1 raw2339step1Labels = mixedMoment B raw2339step2 raw2339step2Labels := by
      have ha : raw2339step2 = raw2339step1 := by apply Matrix.ext; unfold raw2339step2 raw2339step1; decide +kernel
      have hl : raw2339step1Labels = labelEmbedding1 ∘ raw2339step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2339step1 raw2339step1Labels raw2339step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3655 node3655Labels := by rfl

def raw2340 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2340step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2340step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2340 raw2340Labels = mixedMoment B node5319 node5319Labels := by
  calc
    mixedMoment B raw2340 raw2340Labels = mixedMoment B raw2340step0 raw2340step0Labels := by
      have ha : raw2340step0 = (fun i j => raw2340 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2340step0 raw2340; decide +kernel
      have hl : raw2340step0Labels = raw2340Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2340 raw2340Labels permutation152 permutation4
    mixedMoment B raw2340step0 raw2340step0Labels = mixedMoment B raw2340step1 raw2340step1Labels := by
      have ha : raw2340step1 = raw2340step0 := by apply Matrix.ext; unfold raw2340step1 raw2340step0; decide +kernel
      have hl : raw2340step0Labels = labelEmbedding7 ∘ raw2340step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2340step0 raw2340step0Labels raw2340step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5319 node5319Labels := by rfl

def raw2341 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2341 raw2341Labels = mixedMoment B node3642 node3642Labels := by
  calc
    mixedMoment B raw2341 raw2341Labels = mixedMoment B raw2341step0 raw2341step0Labels := by
      have ha : raw2341step0 = (fun i j => raw2341 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2341step0 raw2341; decide +kernel
      have hl : raw2341step0Labels = raw2341Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2341 raw2341Labels permutation152 permutation4
    _ = mixedMoment B node3642 node3642Labels := by rfl

def raw2342 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2342Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2342step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2342step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2342step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2342step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2342 raw2342Labels = mixedMoment B node3662 node3662Labels := by
  calc
    mixedMoment B raw2342 raw2342Labels = mixedMoment B raw2342step0 raw2342step0Labels := by
      have ha : raw2342step0 = (fun i j => raw2342 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2342step0 raw2342; decide +kernel
      have hl : raw2342step0Labels = raw2342Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2342 raw2342Labels permutation152 permutation6
    mixedMoment B raw2342step0 raw2342step0Labels = mixedMoment B raw2342step1 raw2342step1Labels := by
      have ha : raw2342step1 = -raw2342step0 := by apply Matrix.ext; change ∀ i j, raw2342step1 i j = -(raw2342step0 i j); unfold raw2342step1 raw2342step0; decide +kernel
      have hl : raw2342step1Labels = raw2342step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2342step1 raw2342step1Labels = mixedMoment B raw2342step2 raw2342step2Labels := by
      have ha : raw2342step2 = raw2342step1 := by apply Matrix.ext; unfold raw2342step2 raw2342step1; decide +kernel
      have hl : raw2342step1Labels = labelEmbedding1 ∘ raw2342step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2342step1 raw2342step1Labels raw2342step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3662 node3662Labels := by rfl

def raw2343 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2343step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2343step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2343step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2343 raw2343Labels = mixedMoment B node5320 node5320Labels := by
  calc
    mixedMoment B raw2343 raw2343Labels = mixedMoment B raw2343step0 raw2343step0Labels := by
      have ha : raw2343step0 = (fun i j => raw2343 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2343step0 raw2343; decide +kernel
      have hl : raw2343step0Labels = raw2343Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2343 raw2343Labels permutation152 permutation4
    mixedMoment B raw2343step0 raw2343step0Labels = mixedMoment B raw2343step1 raw2343step1Labels := by
      have ha : raw2343step1 = raw2343step0 := by apply Matrix.ext; unfold raw2343step1 raw2343step0; decide +kernel
      have hl : raw2343step0Labels = labelEmbedding7 ∘ raw2343step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2343step0 raw2343step0Labels raw2343step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5320 node5320Labels := by rfl

def raw2344 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2344 raw2344Labels = mixedMoment B node3646 node3646Labels := by
  calc
    mixedMoment B raw2344 raw2344Labels = mixedMoment B raw2344step0 raw2344step0Labels := by
      have ha : raw2344step0 = (fun i j => raw2344 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2344step0 raw2344; decide +kernel
      have hl : raw2344step0Labels = raw2344Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2344 raw2344Labels permutation152 permutation4
    _ = mixedMoment B node3646 node3646Labels := by rfl

def raw2345 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2345Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw2345step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2345step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2345step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2345step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2345step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2345 raw2345Labels = mixedMoment B node3656 node3656Labels := by
  calc
    mixedMoment B raw2345 raw2345Labels = mixedMoment B raw2345step0 raw2345step0Labels := by
      have ha : raw2345step0 = (fun i j => raw2345 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2345step0 raw2345; decide +kernel
      have hl : raw2345step0Labels = raw2345Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2345 raw2345Labels permutation164 permutation6
    mixedMoment B raw2345step0 raw2345step0Labels = mixedMoment B raw2345step1 raw2345step1Labels := by
      have ha : raw2345step1 = -raw2345step0 := by apply Matrix.ext; change ∀ i j, raw2345step1 i j = -(raw2345step0 i j); unfold raw2345step1 raw2345step0; decide +kernel
      have hl : raw2345step1Labels = raw2345step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2345step1 raw2345step1Labels = mixedMoment B raw2345step2 raw2345step2Labels := by
      have ha : raw2345step2 = raw2345step1 := by apply Matrix.ext; unfold raw2345step2 raw2345step1; decide +kernel
      have hl : raw2345step1Labels = labelEmbedding1 ∘ raw2345step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2345step1 raw2345step1Labels raw2345step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3656 node3656Labels := by rfl

def raw2346 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2346step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2346 raw2346Labels = mixedMoment B node5321 node5321Labels := by
  calc
    mixedMoment B raw2346 raw2346Labels = mixedMoment B raw2346step0 raw2346step0Labels := by
      have ha : raw2346step0 = (fun i j => raw2346 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2346step0 raw2346; decide +kernel
      have hl : raw2346step0Labels = raw2346Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2346 raw2346Labels permutation152 permutation4
    mixedMoment B raw2346step0 raw2346step0Labels = mixedMoment B raw2346step1 raw2346step1Labels := by
      have ha : raw2346step1 = raw2346step0 := by apply Matrix.ext; unfold raw2346step1 raw2346step0; decide +kernel
      have hl : raw2346step0Labels = labelEmbedding7 ∘ raw2346step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2346step0 raw2346step0Labels raw2346step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5321 node5321Labels := by rfl

def raw2347 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2347 raw2347Labels = mixedMoment B node3647 node3647Labels := by
  calc
    mixedMoment B raw2347 raw2347Labels = mixedMoment B raw2347step0 raw2347step0Labels := by
      have ha : raw2347step0 = (fun i j => raw2347 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2347step0 raw2347; decide +kernel
      have hl : raw2347step0Labels = raw2347Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2347 raw2347Labels permutation152 permutation4
    _ = mixedMoment B node3647 node3647Labels := by rfl

def raw2348 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2348Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw2348step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2348step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2348step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2348step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2348 raw2348Labels = mixedMoment B node3663 node3663Labels := by
  calc
    mixedMoment B raw2348 raw2348Labels = mixedMoment B raw2348step0 raw2348step0Labels := by
      have ha : raw2348step0 = (fun i j => raw2348 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2348step0 raw2348; decide +kernel
      have hl : raw2348step0Labels = raw2348Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2348 raw2348Labels permutation152 permutation6
    mixedMoment B raw2348step0 raw2348step0Labels = mixedMoment B raw2348step1 raw2348step1Labels := by
      have ha : raw2348step1 = -raw2348step0 := by apply Matrix.ext; change ∀ i j, raw2348step1 i j = -(raw2348step0 i j); unfold raw2348step1 raw2348step0; decide +kernel
      have hl : raw2348step1Labels = raw2348step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2348step1 raw2348step1Labels = mixedMoment B raw2348step2 raw2348step2Labels := by
      have ha : raw2348step2 = raw2348step1 := by apply Matrix.ext; unfold raw2348step2 raw2348step1; decide +kernel
      have hl : raw2348step1Labels = labelEmbedding1 ∘ raw2348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2348step1 raw2348step1Labels raw2348step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3663 node3663Labels := by rfl

def raw2349 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2349step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2349step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2349 raw2349Labels = mixedMoment B node5324 node5324Labels := by
  calc
    mixedMoment B raw2349 raw2349Labels = mixedMoment B raw2349step0 raw2349step0Labels := by
      have ha : raw2349step0 = (fun i j => raw2349 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2349step0 raw2349; decide +kernel
      have hl : raw2349step0Labels = raw2349Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2349 raw2349Labels permutation152 permutation4
    mixedMoment B raw2349step0 raw2349step0Labels = mixedMoment B raw2349step1 raw2349step1Labels := by
      have ha : raw2349step1 = raw2349step0 := by apply Matrix.ext; unfold raw2349step1 raw2349step0; decide +kernel
      have hl : raw2349step0Labels = labelEmbedding7 ∘ raw2349step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2349step0 raw2349step0Labels raw2349step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5324 node5324Labels := by rfl

def raw2350 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2350 raw2350Labels = mixedMoment B node3651 node3651Labels := by
  calc
    mixedMoment B raw2350 raw2350Labels = mixedMoment B raw2350step0 raw2350step0Labels := by
      have ha : raw2350step0 = (fun i j => raw2350 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2350step0 raw2350; decide +kernel
      have hl : raw2350step0Labels = raw2350Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2350 raw2350Labels permutation152 permutation4
    _ = mixedMoment B node3651 node3651Labels := by rfl

def raw2351 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2351Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw2351step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2351step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2351step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2351 raw2351Labels = mixedMoment B node3651 node3651Labels := by
  calc
    mixedMoment B raw2351 raw2351Labels = mixedMoment B raw2351step0 raw2351step0Labels := by
      have ha : raw2351step0 = (fun i j => raw2351 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2351step0 raw2351; decide +kernel
      have hl : raw2351step0Labels = raw2351Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2351 raw2351Labels permutation159 permutation6
    mixedMoment B raw2351step0 raw2351step0Labels = mixedMoment B raw2351step1 raw2351step1Labels := by
      have ha : raw2351step1 = -raw2351step0 := by apply Matrix.ext; change ∀ i j, raw2351step1 i j = -(raw2351step0 i j); unfold raw2351step1 raw2351step0; decide +kernel
      have hl : raw2351step1Labels = raw2351step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2351step1 raw2351step1Labels = mixedMoment B raw2351step2 raw2351step2Labels := by
      have ha : raw2351step2 = raw2351step1 := by apply Matrix.ext; unfold raw2351step2 raw2351step1; decide +kernel
      have hl : raw2351step1Labels = labelEmbedding1 ∘ raw2351step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2351step1 raw2351step1Labels raw2351step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3651 node3651Labels := by rfl

def raw2352 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2352step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2352 raw2352Labels = mixedMoment B node5326 node5326Labels := by
  calc
    mixedMoment B raw2352 raw2352Labels = mixedMoment B raw2352step0 raw2352step0Labels := by
      have ha : raw2352step0 = (fun i j => raw2352 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2352step0 raw2352; decide +kernel
      have hl : raw2352step0Labels = raw2352Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2352 raw2352Labels permutation152 permutation4
    mixedMoment B raw2352step0 raw2352step0Labels = mixedMoment B raw2352step1 raw2352step1Labels := by
      have ha : raw2352step1 = raw2352step0 := by apply Matrix.ext; unfold raw2352step1 raw2352step0; decide +kernel
      have hl : raw2352step0Labels = labelEmbedding7 ∘ raw2352step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2352step0 raw2352step0Labels raw2352step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5326 node5326Labels := by rfl

def raw2353 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2353 raw2353Labels = mixedMoment B node3653 node3653Labels := by
  calc
    mixedMoment B raw2353 raw2353Labels = mixedMoment B raw2353step0 raw2353step0Labels := by
      have ha : raw2353step0 = (fun i j => raw2353 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2353step0 raw2353; decide +kernel
      have hl : raw2353step0Labels = raw2353Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2353 raw2353Labels permutation152 permutation4
    _ = mixedMoment B node3653 node3653Labels := by rfl

def raw2354 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2354Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw2354step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2354step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2354step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2354 raw2354Labels = mixedMoment B node3657 node3657Labels := by
  calc
    mixedMoment B raw2354 raw2354Labels = mixedMoment B raw2354step0 raw2354step0Labels := by
      have ha : raw2354step0 = (fun i j => raw2354 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2354step0 raw2354; decide +kernel
      have hl : raw2354step0Labels = raw2354Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2354 raw2354Labels permutation170 permutation6
    mixedMoment B raw2354step0 raw2354step0Labels = mixedMoment B raw2354step1 raw2354step1Labels := by
      have ha : raw2354step1 = -raw2354step0 := by apply Matrix.ext; change ∀ i j, raw2354step1 i j = -(raw2354step0 i j); unfold raw2354step1 raw2354step0; decide +kernel
      have hl : raw2354step1Labels = raw2354step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2354step1 raw2354step1Labels = mixedMoment B raw2354step2 raw2354step2Labels := by
      have ha : raw2354step2 = raw2354step1 := by apply Matrix.ext; unfold raw2354step2 raw2354step1; decide +kernel
      have hl : raw2354step1Labels = labelEmbedding1 ∘ raw2354step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2354step1 raw2354step1Labels raw2354step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3657 node3657Labels := by rfl

def raw2355 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2355step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2355 raw2355Labels = mixedMoment B node5328 node5328Labels := by
  calc
    mixedMoment B raw2355 raw2355Labels = mixedMoment B raw2355step0 raw2355step0Labels := by
      have ha : raw2355step0 = (fun i j => raw2355 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2355step0 raw2355; decide +kernel
      have hl : raw2355step0Labels = raw2355Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2355 raw2355Labels permutation152 permutation4
    mixedMoment B raw2355step0 raw2355step0Labels = mixedMoment B raw2355step1 raw2355step1Labels := by
      have ha : raw2355step1 = raw2355step0 := by apply Matrix.ext; unfold raw2355step1 raw2355step0; decide +kernel
      have hl : raw2355step0Labels = labelEmbedding7 ∘ raw2355step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2355step0 raw2355step0Labels raw2355step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5328 node5328Labels := by rfl

def raw2356 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2356 raw2356Labels = mixedMoment B node3659 node3659Labels := by
  calc
    mixedMoment B raw2356 raw2356Labels = mixedMoment B raw2356step0 raw2356step0Labels := by
      have ha : raw2356step0 = (fun i j => raw2356 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2356step0 raw2356; decide +kernel
      have hl : raw2356step0Labels = raw2356Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2356 raw2356Labels permutation152 permutation4
    _ = mixedMoment B node3659 node3659Labels := by rfl

def raw2357 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2357Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2357step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2357step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2357step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2357 raw2357Labels = mixedMoment B node3659 node3659Labels := by
  calc
    mixedMoment B raw2357 raw2357Labels = mixedMoment B raw2357step0 raw2357step0Labels := by
      have ha : raw2357step0 = (fun i j => raw2357 (permutation173 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2357step0 raw2357; decide +kernel
      have hl : raw2357step0Labels = raw2357Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2357 raw2357Labels permutation173 permutation6
    mixedMoment B raw2357step0 raw2357step0Labels = mixedMoment B raw2357step1 raw2357step1Labels := by
      have ha : raw2357step1 = -raw2357step0 := by apply Matrix.ext; change ∀ i j, raw2357step1 i j = -(raw2357step0 i j); unfold raw2357step1 raw2357step0; decide +kernel
      have hl : raw2357step1Labels = raw2357step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2357step1 raw2357step1Labels = mixedMoment B raw2357step2 raw2357step2Labels := by
      have ha : raw2357step2 = raw2357step1 := by apply Matrix.ext; unfold raw2357step2 raw2357step1; decide +kernel
      have hl : raw2357step1Labels = labelEmbedding1 ∘ raw2357step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2357step1 raw2357step1Labels raw2357step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3659 node3659Labels := by rfl

def raw2358 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2358step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2358step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2358 raw2358Labels = mixedMoment B node5329 node5329Labels := by
  calc
    mixedMoment B raw2358 raw2358Labels = mixedMoment B raw2358step0 raw2358step0Labels := by
      have ha : raw2358step0 = (fun i j => raw2358 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2358step0 raw2358; decide +kernel
      have hl : raw2358step0Labels = raw2358Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2358 raw2358Labels permutation32 permutation4
    mixedMoment B raw2358step0 raw2358step0Labels = mixedMoment B raw2358step1 raw2358step1Labels := by
      have ha : raw2358step1 = raw2358step0 := by apply Matrix.ext; unfold raw2358step1 raw2358step0; decide +kernel
      have hl : raw2358step0Labels = labelEmbedding7 ∘ raw2358step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2358step0 raw2358step0Labels raw2358step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5329 node5329Labels := by rfl

def raw2359 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2359 raw2359Labels = mixedMoment B node3660 node3660Labels := by
  calc
    mixedMoment B raw2359 raw2359Labels = mixedMoment B raw2359step0 raw2359step0Labels := by
      have ha : raw2359step0 = (fun i j => raw2359 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2359step0 raw2359; decide +kernel
      have hl : raw2359step0Labels = raw2359Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2359 raw2359Labels permutation32 permutation4
    _ = mixedMoment B node3660 node3660Labels := by rfl

def raw2360 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2360Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw2360step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2360step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2360 raw2360Labels = mixedMoment B node3660 node3660Labels := by
  calc
    mixedMoment B raw2360 raw2360Labels = mixedMoment B raw2360step0 raw2360step0Labels := by
      have ha : raw2360step0 = (fun i j => raw2360 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2360step0 raw2360; decide +kernel
      have hl : raw2360step0Labels = raw2360Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2360 raw2360Labels permutation34 permutation6
    mixedMoment B raw2360step0 raw2360step0Labels = mixedMoment B raw2360step1 raw2360step1Labels := by
      have ha : raw2360step1 = -raw2360step0 := by apply Matrix.ext; change ∀ i j, raw2360step1 i j = -(raw2360step0 i j); unfold raw2360step1 raw2360step0; decide +kernel
      have hl : raw2360step1Labels = raw2360step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2360step1 raw2360step1Labels = mixedMoment B raw2360step2 raw2360step2Labels := by
      have ha : raw2360step2 = raw2360step1 := by apply Matrix.ext; unfold raw2360step2 raw2360step1; decide +kernel
      have hl : raw2360step1Labels = labelEmbedding1 ∘ raw2360step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2360step1 raw2360step1Labels raw2360step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3660 node3660Labels := by rfl

def raw2361 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2361step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2361step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2361 raw2361Labels = mixedMoment B node5330 node5330Labels := by
  calc
    mixedMoment B raw2361 raw2361Labels = mixedMoment B raw2361step0 raw2361step0Labels := by
      have ha : raw2361step0 = (fun i j => raw2361 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2361step0 raw2361; decide +kernel
      have hl : raw2361step0Labels = raw2361Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2361 raw2361Labels permutation32 permutation4
    mixedMoment B raw2361step0 raw2361step0Labels = mixedMoment B raw2361step1 raw2361step1Labels := by
      have ha : raw2361step1 = raw2361step0 := by apply Matrix.ext; unfold raw2361step1 raw2361step0; decide +kernel
      have hl : raw2361step0Labels = labelEmbedding7 ∘ raw2361step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2361step0 raw2361step0Labels raw2361step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5330 node5330Labels := by rfl

def raw2362 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2362 raw2362Labels = mixedMoment B node3661 node3661Labels := by
  calc
    mixedMoment B raw2362 raw2362Labels = mixedMoment B raw2362step0 raw2362step0Labels := by
      have ha : raw2362step0 = (fun i j => raw2362 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2362step0 raw2362; decide +kernel
      have hl : raw2362step0Labels = raw2362Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2362 raw2362Labels permutation32 permutation4
    _ = mixedMoment B node3661 node3661Labels := by rfl

def raw2363 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2363Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw2363step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw2363step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw2363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2363 raw2363Labels = mixedMoment B node3666 node3666Labels := by
  calc
    mixedMoment B raw2363 raw2363Labels = mixedMoment B raw2363step0 raw2363step0Labels := by
      have ha : raw2363step0 = (fun i j => raw2363 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2363step0 raw2363; decide +kernel
      have hl : raw2363step0Labels = raw2363Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2363 raw2363Labels permutation35 permutation6
    mixedMoment B raw2363step0 raw2363step0Labels = mixedMoment B raw2363step1 raw2363step1Labels := by
      have ha : raw2363step1 = -raw2363step0 := by apply Matrix.ext; change ∀ i j, raw2363step1 i j = -(raw2363step0 i j); unfold raw2363step1 raw2363step0; decide +kernel
      have hl : raw2363step1Labels = raw2363step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2363step1 raw2363step1Labels = mixedMoment B raw2363step2 raw2363step2Labels := by
      have ha : raw2363step2 = raw2363step1 := by apply Matrix.ext; unfold raw2363step2 raw2363step1; decide +kernel
      have hl : raw2363step1Labels = labelEmbedding1 ∘ raw2363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2363step1 raw2363step1Labels raw2363step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3666 node3666Labels := by rfl

def raw2364 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2364step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2364 raw2364Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw2364 raw2364Labels = mixedMoment B raw2364step0 raw2364step0Labels := by
      have ha : raw2364step0 = (fun i j => raw2364 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2364step0 raw2364; decide +kernel
      have hl : raw2364step0Labels = raw2364Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2364 raw2364Labels permutation152 permutation4
    mixedMoment B raw2364step0 raw2364step0Labels = mixedMoment B raw2364step1 raw2364step1Labels := by
      have ha : raw2364step1 = raw2364step0 := by apply Matrix.ext; unfold raw2364step1 raw2364step0; decide +kernel
      have hl : raw2364step0Labels = labelEmbedding7 ∘ raw2364step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2364step0 raw2364step0Labels raw2364step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

def raw2365 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2365 raw2365Labels = mixedMoment B node3668 node3668Labels := by
  calc
    mixedMoment B raw2365 raw2365Labels = mixedMoment B raw2365step0 raw2365step0Labels := by
      have ha : raw2365step0 = (fun i j => raw2365 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2365step0 raw2365; decide +kernel
      have hl : raw2365step0Labels = raw2365Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2365 raw2365Labels permutation152 permutation4
    _ = mixedMoment B node3668 node3668Labels := by rfl

def raw2366 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2366Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2366step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2366 raw2366Labels = mixedMoment B node3677 node3677Labels := by
  calc
    mixedMoment B raw2366 raw2366Labels = mixedMoment B raw2366step0 raw2366step0Labels := by
      have ha : raw2366step0 = (fun i j => raw2366 (permutation664 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2366step0 raw2366; decide +kernel
      have hl : raw2366step0Labels = raw2366Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2366 raw2366Labels permutation664 permutation6
    mixedMoment B raw2366step0 raw2366step0Labels = mixedMoment B raw2366step1 raw2366step1Labels := by
      have ha : raw2366step1 = raw2366step0 := by apply Matrix.ext; unfold raw2366step1 raw2366step0; decide +kernel
      have hl : raw2366step0Labels = labelEmbedding1 ∘ raw2366step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2366step0 raw2366step0Labels raw2366step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3677 node3677Labels := by rfl

def raw2367 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2367step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2367step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2367 raw2367Labels = mixedMoment B node5334 node5334Labels := by
  calc
    mixedMoment B raw2367 raw2367Labels = mixedMoment B raw2367step0 raw2367step0Labels := by
      have ha : raw2367step0 = (fun i j => raw2367 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2367step0 raw2367; decide +kernel
      have hl : raw2367step0Labels = raw2367Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2367 raw2367Labels permutation152 permutation4
    mixedMoment B raw2367step0 raw2367step0Labels = mixedMoment B raw2367step1 raw2367step1Labels := by
      have ha : raw2367step1 = raw2367step0 := by apply Matrix.ext; unfold raw2367step1 raw2367step0; decide +kernel
      have hl : raw2367step0Labels = labelEmbedding7 ∘ raw2367step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2367step0 raw2367step0Labels raw2367step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5334 node5334Labels := by rfl

def raw2368 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2368 raw2368Labels = mixedMoment B node3669 node3669Labels := by
  calc
    mixedMoment B raw2368 raw2368Labels = mixedMoment B raw2368step0 raw2368step0Labels := by
      have ha : raw2368step0 = (fun i j => raw2368 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2368step0 raw2368; decide +kernel
      have hl : raw2368step0Labels = raw2368Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2368 raw2368Labels permutation152 permutation4
    _ = mixedMoment B node3669 node3669Labels := by rfl

def raw2369 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2369Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw2369step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw2369step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2369step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw2369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2369 raw2369Labels = mixedMoment B node3742 node3742Labels := by
  calc
    mixedMoment B raw2369 raw2369Labels = mixedMoment B raw2369step0 raw2369step0Labels := by
      have ha : raw2369step0 = (fun i j => raw2369 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2369step0 raw2369; decide +kernel
      have hl : raw2369step0Labels = raw2369Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2369 raw2369Labels permutation155 permutation6
    mixedMoment B raw2369step0 raw2369step0Labels = mixedMoment B raw2369step1 raw2369step1Labels := by
      have ha : raw2369step1 = -raw2369step0 := by apply Matrix.ext; change ∀ i j, raw2369step1 i j = -(raw2369step0 i j); unfold raw2369step1 raw2369step0; decide +kernel
      have hl : raw2369step1Labels = raw2369step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2369step1 raw2369step1Labels = mixedMoment B raw2369step2 raw2369step2Labels := by
      have ha : raw2369step2 = raw2369step1 := by apply Matrix.ext; unfold raw2369step2 raw2369step1; decide +kernel
      have hl : raw2369step1Labels = labelEmbedding1 ∘ raw2369step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2369step1 raw2369step1Labels raw2369step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3742 node3742Labels := by rfl

def raw2370 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2370step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2370step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2370 raw2370Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw2370 raw2370Labels = mixedMoment B raw2370step0 raw2370step0Labels := by
      have ha : raw2370step0 = (fun i j => raw2370 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2370step0 raw2370; decide +kernel
      have hl : raw2370step0Labels = raw2370Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2370 raw2370Labels permutation152 permutation4
    mixedMoment B raw2370step0 raw2370step0Labels = mixedMoment B raw2370step1 raw2370step1Labels := by
      have ha : raw2370step1 = raw2370step0 := by apply Matrix.ext; unfold raw2370step1 raw2370step0; decide +kernel
      have hl : raw2370step0Labels = labelEmbedding7 ∘ raw2370step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2370step0 raw2370step0Labels raw2370step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

def raw2371 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2371 raw2371Labels = mixedMoment B node3670 node3670Labels := by
  calc
    mixedMoment B raw2371 raw2371Labels = mixedMoment B raw2371step0 raw2371step0Labels := by
      have ha : raw2371step0 = (fun i j => raw2371 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2371step0 raw2371; decide +kernel
      have hl : raw2371step0Labels = raw2371Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2371 raw2371Labels permutation152 permutation4
    _ = mixedMoment B node3670 node3670Labels := by rfl

def raw2372 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2372Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2372step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2372 raw2372Labels = mixedMoment B node3753 node3753Labels := by
  calc
    mixedMoment B raw2372 raw2372Labels = mixedMoment B raw2372step0 raw2372step0Labels := by
      have ha : raw2372step0 = (fun i j => raw2372 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2372step0 raw2372; decide +kernel
      have hl : raw2372step0Labels = raw2372Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2372 raw2372Labels permutation688 permutation6
    mixedMoment B raw2372step0 raw2372step0Labels = mixedMoment B raw2372step1 raw2372step1Labels := by
      have ha : raw2372step1 = raw2372step0 := by apply Matrix.ext; unfold raw2372step1 raw2372step0; decide +kernel
      have hl : raw2372step0Labels = labelEmbedding1 ∘ raw2372step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2372step0 raw2372step0Labels raw2372step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3753 node3753Labels := by rfl

def raw2373 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2373step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2373step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2373 raw2373Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw2373 raw2373Labels = mixedMoment B raw2373step0 raw2373step0Labels := by
      have ha : raw2373step0 = (fun i j => raw2373 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2373step0 raw2373; decide +kernel
      have hl : raw2373step0Labels = raw2373Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2373 raw2373Labels permutation152 permutation4
    mixedMoment B raw2373step0 raw2373step0Labels = mixedMoment B raw2373step1 raw2373step1Labels := by
      have ha : raw2373step1 = raw2373step0 := by apply Matrix.ext; unfold raw2373step1 raw2373step0; decide +kernel
      have hl : raw2373step0Labels = labelEmbedding7 ∘ raw2373step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2373step0 raw2373step0Labels raw2373step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5336 node5336Labels := by rfl

def raw2374 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2374 raw2374Labels = mixedMoment B node3671 node3671Labels := by
  calc
    mixedMoment B raw2374 raw2374Labels = mixedMoment B raw2374step0 raw2374step0Labels := by
      have ha : raw2374step0 = (fun i j => raw2374 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2374step0 raw2374; decide +kernel
      have hl : raw2374step0Labels = raw2374Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2374 raw2374Labels permutation152 permutation4
    _ = mixedMoment B node3671 node3671Labels := by rfl

def raw2375 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2375Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw2375step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2375step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2375step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2375 raw2375Labels = mixedMoment B node3754 node3754Labels := by
  calc
    mixedMoment B raw2375 raw2375Labels = mixedMoment B raw2375step0 raw2375step0Labels := by
      have ha : raw2375step0 = (fun i j => raw2375 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2375step0 raw2375; decide +kernel
      have hl : raw2375step0Labels = raw2375Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2375 raw2375Labels permutation154 permutation6
    mixedMoment B raw2375step0 raw2375step0Labels = mixedMoment B raw2375step1 raw2375step1Labels := by
      have ha : raw2375step1 = -raw2375step0 := by apply Matrix.ext; change ∀ i j, raw2375step1 i j = -(raw2375step0 i j); unfold raw2375step1 raw2375step0; decide +kernel
      have hl : raw2375step1Labels = raw2375step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2375step1 raw2375step1Labels = mixedMoment B raw2375step2 raw2375step2Labels := by
      have ha : raw2375step2 = raw2375step1 := by apply Matrix.ext; unfold raw2375step2 raw2375step1; decide +kernel
      have hl : raw2375step1Labels = labelEmbedding1 ∘ raw2375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2375step1 raw2375step1Labels raw2375step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3754 node3754Labels := by rfl

def raw2376 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2376step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2376step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2376 raw2376Labels = mixedMoment B node5337 node5337Labels := by
  calc
    mixedMoment B raw2376 raw2376Labels = mixedMoment B raw2376step0 raw2376step0Labels := by
      have ha : raw2376step0 = (fun i j => raw2376 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2376step0 raw2376; decide +kernel
      have hl : raw2376step0Labels = raw2376Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2376 raw2376Labels permutation152 permutation4
    mixedMoment B raw2376step0 raw2376step0Labels = mixedMoment B raw2376step1 raw2376step1Labels := by
      have ha : raw2376step1 = raw2376step0 := by apply Matrix.ext; unfold raw2376step1 raw2376step0; decide +kernel
      have hl : raw2376step0Labels = labelEmbedding7 ∘ raw2376step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2376step0 raw2376step0Labels raw2376step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5337 node5337Labels := by rfl

def raw2377 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2377 raw2377Labels = mixedMoment B node3672 node3672Labels := by
  calc
    mixedMoment B raw2377 raw2377Labels = mixedMoment B raw2377step0 raw2377step0Labels := by
      have ha : raw2377step0 = (fun i j => raw2377 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2377step0 raw2377; decide +kernel
      have hl : raw2377step0Labels = raw2377Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2377 raw2377Labels permutation152 permutation4
    _ = mixedMoment B node3672 node3672Labels := by rfl

def raw2378 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2378Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2378step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2378step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2378step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2378 raw2378Labels = mixedMoment B node3756 node3756Labels := by
  calc
    mixedMoment B raw2378 raw2378Labels = mixedMoment B raw2378step0 raw2378step0Labels := by
      have ha : raw2378step0 = (fun i j => raw2378 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2378step0 raw2378; decide +kernel
      have hl : raw2378step0Labels = raw2378Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2378 raw2378Labels permutation152 permutation6
    mixedMoment B raw2378step0 raw2378step0Labels = mixedMoment B raw2378step1 raw2378step1Labels := by
      have ha : raw2378step1 = -raw2378step0 := by apply Matrix.ext; change ∀ i j, raw2378step1 i j = -(raw2378step0 i j); unfold raw2378step1 raw2378step0; decide +kernel
      have hl : raw2378step1Labels = raw2378step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2378step1 raw2378step1Labels = mixedMoment B raw2378step2 raw2378step2Labels := by
      have ha : raw2378step2 = raw2378step1 := by apply Matrix.ext; unfold raw2378step2 raw2378step1; decide +kernel
      have hl : raw2378step1Labels = labelEmbedding1 ∘ raw2378step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2378step1 raw2378step1Labels raw2378step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3756 node3756Labels := by rfl

def raw2379 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2379step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2379 raw2379Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw2379 raw2379Labels = mixedMoment B raw2379step0 raw2379step0Labels := by
      have ha : raw2379step0 = (fun i j => raw2379 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2379step0 raw2379; decide +kernel
      have hl : raw2379step0Labels = raw2379Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2379 raw2379Labels permutation152 permutation4
    mixedMoment B raw2379step0 raw2379step0Labels = mixedMoment B raw2379step1 raw2379step1Labels := by
      have ha : raw2379step1 = raw2379step0 := by apply Matrix.ext; unfold raw2379step1 raw2379step0; decide +kernel
      have hl : raw2379step0Labels = labelEmbedding7 ∘ raw2379step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2379step0 raw2379step0Labels raw2379step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

def raw2380 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2380 raw2380Labels = mixedMoment B node3678 node3678Labels := by
  calc
    mixedMoment B raw2380 raw2380Labels = mixedMoment B raw2380step0 raw2380step0Labels := by
      have ha : raw2380step0 = (fun i j => raw2380 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2380step0 raw2380; decide +kernel
      have hl : raw2380step0Labels = raw2380Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2380 raw2380Labels permutation152 permutation4
    _ = mixedMoment B node3678 node3678Labels := by rfl

def raw2381 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2381Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2381step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2381 raw2381Labels = mixedMoment B node3744 node3744Labels := by
  calc
    mixedMoment B raw2381 raw2381Labels = mixedMoment B raw2381step0 raw2381step0Labels := by
      have ha : raw2381step0 = (fun i j => raw2381 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2381step0 raw2381; decide +kernel
      have hl : raw2381step0Labels = raw2381Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2381 raw2381Labels permutation688 permutation6
    mixedMoment B raw2381step0 raw2381step0Labels = mixedMoment B raw2381step1 raw2381step1Labels := by
      have ha : raw2381step1 = raw2381step0 := by apply Matrix.ext; unfold raw2381step1 raw2381step0; decide +kernel
      have hl : raw2381step0Labels = labelEmbedding1 ∘ raw2381step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2381step0 raw2381step0Labels raw2381step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3744 node3744Labels := by rfl

def raw2382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2382step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2382step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2382 raw2382Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw2382 raw2382Labels = mixedMoment B raw2382step0 raw2382step0Labels := by
      have ha : raw2382step0 = (fun i j => raw2382 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2382step0 raw2382; decide +kernel
      have hl : raw2382step0Labels = raw2382Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2382 raw2382Labels permutation152 permutation4
    mixedMoment B raw2382step0 raw2382step0Labels = mixedMoment B raw2382step1 raw2382step1Labels := by
      have ha : raw2382step1 = raw2382step0 := by apply Matrix.ext; unfold raw2382step1 raw2382step0; decide +kernel
      have hl : raw2382step0Labels = labelEmbedding7 ∘ raw2382step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2382step0 raw2382step0Labels raw2382step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw2383 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2383 raw2383Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw2383 raw2383Labels = mixedMoment B raw2383step0 raw2383step0Labels := by
      have ha : raw2383step0 = (fun i j => raw2383 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2383step0 raw2383; decide +kernel
      have hl : raw2383step0Labels = raw2383Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2383 raw2383Labels permutation152 permutation4
    _ = mixedMoment B node3681 node3681Labels := by rfl

def raw2384 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2384Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2384step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2384 raw2384Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw2384 raw2384Labels = mixedMoment B raw2384step0 raw2384step0Labels := by
      have ha : raw2384step0 = (fun i j => raw2384 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2384step0 raw2384; decide +kernel
      have hl : raw2384step0Labels = raw2384Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2384 raw2384Labels permutation688 permutation6
    mixedMoment B raw2384step0 raw2384step0Labels = mixedMoment B raw2384step1 raw2384step1Labels := by
      have ha : raw2384step1 = raw2384step0 := by apply Matrix.ext; unfold raw2384step1 raw2384step0; decide +kernel
      have hl : raw2384step0Labels = labelEmbedding1 ∘ raw2384step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2384step0 raw2384step0Labels raw2384step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3681 node3681Labels := by rfl

def raw2385 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2385step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2385step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2385 raw2385Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw2385 raw2385Labels = mixedMoment B raw2385step0 raw2385step0Labels := by
      have ha : raw2385step0 = (fun i j => raw2385 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2385step0 raw2385; decide +kernel
      have hl : raw2385step0Labels = raw2385Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2385 raw2385Labels permutation152 permutation4
    mixedMoment B raw2385step0 raw2385step0Labels = mixedMoment B raw2385step1 raw2385step1Labels := by
      have ha : raw2385step1 = raw2385step0 := by apply Matrix.ext; unfold raw2385step1 raw2385step0; decide +kernel
      have hl : raw2385step0Labels = labelEmbedding7 ∘ raw2385step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2385step0 raw2385step0Labels raw2385step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw2386 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2386 raw2386Labels = mixedMoment B node3683 node3683Labels := by
  calc
    mixedMoment B raw2386 raw2386Labels = mixedMoment B raw2386step0 raw2386step0Labels := by
      have ha : raw2386step0 = (fun i j => raw2386 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2386step0 raw2386; decide +kernel
      have hl : raw2386step0Labels = raw2386Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2386 raw2386Labels permutation152 permutation4
    _ = mixedMoment B node3683 node3683Labels := by rfl

def raw2387 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2387Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2387step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2387step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2387step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2387 raw2387Labels = mixedMoment B node3746 node3746Labels := by
  calc
    mixedMoment B raw2387 raw2387Labels = mixedMoment B raw2387step0 raw2387step0Labels := by
      have ha : raw2387step0 = (fun i j => raw2387 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2387step0 raw2387; decide +kernel
      have hl : raw2387step0Labels = raw2387Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2387 raw2387Labels permutation153 permutation6
    mixedMoment B raw2387step0 raw2387step0Labels = mixedMoment B raw2387step1 raw2387step1Labels := by
      have ha : raw2387step1 = -raw2387step0 := by apply Matrix.ext; change ∀ i j, raw2387step1 i j = -(raw2387step0 i j); unfold raw2387step1 raw2387step0; decide +kernel
      have hl : raw2387step1Labels = raw2387step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2387step1 raw2387step1Labels = mixedMoment B raw2387step2 raw2387step2Labels := by
      have ha : raw2387step2 = raw2387step1 := by apply Matrix.ext; unfold raw2387step2 raw2387step1; decide +kernel
      have hl : raw2387step1Labels = labelEmbedding1 ∘ raw2387step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2387step1 raw2387step1Labels raw2387step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3746 node3746Labels := by rfl

def raw2388 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2388step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2388step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2388 raw2388Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw2388 raw2388Labels = mixedMoment B raw2388step0 raw2388step0Labels := by
      have ha : raw2388step0 = (fun i j => raw2388 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2388step0 raw2388; decide +kernel
      have hl : raw2388step0Labels = raw2388Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2388 raw2388Labels permutation152 permutation4
    mixedMoment B raw2388step0 raw2388step0Labels = mixedMoment B raw2388step1 raw2388step1Labels := by
      have ha : raw2388step1 = raw2388step0 := by apply Matrix.ext; unfold raw2388step1 raw2388step0; decide +kernel
      have hl : raw2388step0Labels = labelEmbedding7 ∘ raw2388step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2388step0 raw2388step0Labels raw2388step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw2389 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2389 raw2389Labels = mixedMoment B node3687 node3687Labels := by
  calc
    mixedMoment B raw2389 raw2389Labels = mixedMoment B raw2389step0 raw2389step0Labels := by
      have ha : raw2389step0 = (fun i j => raw2389 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2389step0 raw2389; decide +kernel
      have hl : raw2389step0Labels = raw2389Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2389 raw2389Labels permutation152 permutation4
    _ = mixedMoment B node3687 node3687Labels := by rfl

def raw2390 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2390Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw2390step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2390step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2390step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2390 raw2390Labels = mixedMoment B node3749 node3749Labels := by
  calc
    mixedMoment B raw2390 raw2390Labels = mixedMoment B raw2390step0 raw2390step0Labels := by
      have ha : raw2390step0 = (fun i j => raw2390 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2390step0 raw2390; decide +kernel
      have hl : raw2390step0Labels = raw2390Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2390 raw2390Labels permutation158 permutation6
    mixedMoment B raw2390step0 raw2390step0Labels = mixedMoment B raw2390step1 raw2390step1Labels := by
      have ha : raw2390step1 = -raw2390step0 := by apply Matrix.ext; change ∀ i j, raw2390step1 i j = -(raw2390step0 i j); unfold raw2390step1 raw2390step0; decide +kernel
      have hl : raw2390step1Labels = raw2390step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2390step1 raw2390step1Labels = mixedMoment B raw2390step2 raw2390step2Labels := by
      have ha : raw2390step2 = raw2390step1 := by apply Matrix.ext; unfold raw2390step2 raw2390step1; decide +kernel
      have hl : raw2390step1Labels = labelEmbedding1 ∘ raw2390step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2390step1 raw2390step1Labels raw2390step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3749 node3749Labels := by rfl

def raw2391 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2391step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2391step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2391 raw2391Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw2391 raw2391Labels = mixedMoment B raw2391step0 raw2391step0Labels := by
      have ha : raw2391step0 = (fun i j => raw2391 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2391step0 raw2391; decide +kernel
      have hl : raw2391step0Labels = raw2391Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2391 raw2391Labels permutation152 permutation4
    mixedMoment B raw2391step0 raw2391step0Labels = mixedMoment B raw2391step1 raw2391step1Labels := by
      have ha : raw2391step1 = raw2391step0 := by apply Matrix.ext; unfold raw2391step1 raw2391step0; decide +kernel
      have hl : raw2391step0Labels = labelEmbedding7 ∘ raw2391step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2391step0 raw2391step0Labels raw2391step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw2392 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2392 raw2392Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw2392 raw2392Labels = mixedMoment B raw2392step0 raw2392step0Labels := by
      have ha : raw2392step0 = (fun i j => raw2392 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2392step0 raw2392; decide +kernel
      have hl : raw2392step0Labels = raw2392Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2392 raw2392Labels permutation152 permutation4
    _ = mixedMoment B node3689 node3689Labels := by rfl

def raw2393 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2393Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw2393step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2393step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2393step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2393step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2393 raw2393Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw2393 raw2393Labels = mixedMoment B raw2393step0 raw2393step0Labels := by
      have ha : raw2393step0 = (fun i j => raw2393 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2393step0 raw2393; decide +kernel
      have hl : raw2393step0Labels = raw2393Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2393 raw2393Labels permutation160 permutation6
    mixedMoment B raw2393step0 raw2393step0Labels = mixedMoment B raw2393step1 raw2393step1Labels := by
      have ha : raw2393step1 = -raw2393step0 := by apply Matrix.ext; change ∀ i j, raw2393step1 i j = -(raw2393step0 i j); unfold raw2393step1 raw2393step0; decide +kernel
      have hl : raw2393step1Labels = raw2393step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2393step1 raw2393step1Labels = mixedMoment B raw2393step2 raw2393step2Labels := by
      have ha : raw2393step2 = raw2393step1 := by apply Matrix.ext; unfold raw2393step2 raw2393step1; decide +kernel
      have hl : raw2393step1Labels = labelEmbedding1 ∘ raw2393step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2393step1 raw2393step1Labels raw2393step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

def raw2394 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2394step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2394 raw2394Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw2394 raw2394Labels = mixedMoment B raw2394step0 raw2394step0Labels := by
      have ha : raw2394step0 = (fun i j => raw2394 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2394step0 raw2394; decide +kernel
      have hl : raw2394step0Labels = raw2394Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2394 raw2394Labels permutation152 permutation4
    mixedMoment B raw2394step0 raw2394step0Labels = mixedMoment B raw2394step1 raw2394step1Labels := by
      have ha : raw2394step1 = raw2394step0 := by apply Matrix.ext; unfold raw2394step1 raw2394step0; decide +kernel
      have hl : raw2394step0Labels = labelEmbedding7 ∘ raw2394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2394step0 raw2394step0Labels raw2394step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw2395 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2395 raw2395Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw2395 raw2395Labels = mixedMoment B raw2395step0 raw2395step0Labels := by
      have ha : raw2395step0 = (fun i j => raw2395 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2395step0 raw2395; decide +kernel
      have hl : raw2395step0Labels = raw2395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2395 raw2395Labels permutation152 permutation4
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw2396 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2396Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2396step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2396step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2396 raw2396Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw2396 raw2396Labels = mixedMoment B raw2396step0 raw2396step0Labels := by
      have ha : raw2396step0 = (fun i j => raw2396 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2396step0 raw2396; decide +kernel
      have hl : raw2396step0Labels = raw2396Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2396 raw2396Labels permutation158 permutation6
    mixedMoment B raw2396step0 raw2396step0Labels = mixedMoment B raw2396step1 raw2396step1Labels := by
      have ha : raw2396step1 = -raw2396step0 := by apply Matrix.ext; change ∀ i j, raw2396step1 i j = -(raw2396step0 i j); unfold raw2396step1 raw2396step0; decide +kernel
      have hl : raw2396step1Labels = raw2396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2396step1 raw2396step1Labels = mixedMoment B raw2396step2 raw2396step2Labels := by
      have ha : raw2396step2 = raw2396step1 := by apply Matrix.ext; unfold raw2396step2 raw2396step1; decide +kernel
      have hl : raw2396step1Labels = labelEmbedding1 ∘ raw2396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2396step1 raw2396step1Labels raw2396step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

def raw2397 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2397step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2397step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2397 raw2397Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw2397 raw2397Labels = mixedMoment B raw2397step0 raw2397step0Labels := by
      have ha : raw2397step0 = (fun i j => raw2397 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2397step0 raw2397; decide +kernel
      have hl : raw2397step0Labels = raw2397Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2397 raw2397Labels permutation152 permutation4
    mixedMoment B raw2397step0 raw2397step0Labels = mixedMoment B raw2397step1 raw2397step1Labels := by
      have ha : raw2397step1 = raw2397step0 := by apply Matrix.ext; unfold raw2397step1 raw2397step0; decide +kernel
      have hl : raw2397step0Labels = labelEmbedding7 ∘ raw2397step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2397step0 raw2397step0Labels raw2397step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw2398 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2398 raw2398Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw2398 raw2398Labels = mixedMoment B raw2398step0 raw2398step0Labels := by
      have ha : raw2398step0 = (fun i j => raw2398 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2398step0 raw2398; decide +kernel
      have hl : raw2398step0Labels = raw2398Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2398 raw2398Labels permutation152 permutation4
    _ = mixedMoment B node3692 node3692Labels := by rfl

def raw2399 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2399Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2399step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2399step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2399 raw2399Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw2399 raw2399Labels = mixedMoment B raw2399step0 raw2399step0Labels := by
      have ha : raw2399step0 = (fun i j => raw2399 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2399step0 raw2399; decide +kernel
      have hl : raw2399step0Labels = raw2399Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2399 raw2399Labels permutation170 permutation6
    mixedMoment B raw2399step0 raw2399step0Labels = mixedMoment B raw2399step1 raw2399step1Labels := by
      have ha : raw2399step1 = -raw2399step0 := by apply Matrix.ext; change ∀ i j, raw2399step1 i j = -(raw2399step0 i j); unfold raw2399step1 raw2399step0; decide +kernel
      have hl : raw2399step1Labels = raw2399step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2399step1 raw2399step1Labels = mixedMoment B raw2399step2 raw2399step2Labels := by
      have ha : raw2399step2 = raw2399step1 := by apply Matrix.ext; unfold raw2399step2 raw2399step1; decide +kernel
      have hl : raw2399step1Labels = labelEmbedding1 ∘ raw2399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2399step1 raw2399step1Labels raw2399step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

def raw2400 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2400step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2400 raw2400Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw2400 raw2400Labels = mixedMoment B raw2400step0 raw2400step0Labels := by
      have ha : raw2400step0 = (fun i j => raw2400 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2400step0 raw2400; decide +kernel
      have hl : raw2400step0Labels = raw2400Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2400 raw2400Labels permutation32 permutation4
    mixedMoment B raw2400step0 raw2400step0Labels = mixedMoment B raw2400step1 raw2400step1Labels := by
      have ha : raw2400step1 = raw2400step0 := by apply Matrix.ext; unfold raw2400step1 raw2400step0; decide +kernel
      have hl : raw2400step0Labels = labelEmbedding7 ∘ raw2400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2400step0 raw2400step0Labels raw2400step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw2401 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2401 raw2401Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw2401 raw2401Labels = mixedMoment B raw2401step0 raw2401step0Labels := by
      have ha : raw2401step0 = (fun i j => raw2401 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2401step0 raw2401; decide +kernel
      have hl : raw2401step0Labels = raw2401Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2401 raw2401Labels permutation32 permutation4
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw2402 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2402Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw2402step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2402step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2402step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2402 raw2402Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw2402 raw2402Labels = mixedMoment B raw2402step0 raw2402step0Labels := by
      have ha : raw2402step0 = (fun i j => raw2402 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2402step0 raw2402; decide +kernel
      have hl : raw2402step0Labels = raw2402Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2402 raw2402Labels permutation34 permutation6
    mixedMoment B raw2402step0 raw2402step0Labels = mixedMoment B raw2402step1 raw2402step1Labels := by
      have ha : raw2402step1 = -raw2402step0 := by apply Matrix.ext; change ∀ i j, raw2402step1 i j = -(raw2402step0 i j); unfold raw2402step1 raw2402step0; decide +kernel
      have hl : raw2402step1Labels = raw2402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2402step1 raw2402step1Labels = mixedMoment B raw2402step2 raw2402step2Labels := by
      have ha : raw2402step2 = raw2402step1 := by apply Matrix.ext; unfold raw2402step2 raw2402step1; decide +kernel
      have hl : raw2402step1Labels = labelEmbedding1 ∘ raw2402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2402step1 raw2402step1Labels raw2402step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw2403 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2403step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2403 raw2403Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw2403 raw2403Labels = mixedMoment B raw2403step0 raw2403step0Labels := by
      have ha : raw2403step0 = (fun i j => raw2403 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2403step0 raw2403; decide +kernel
      have hl : raw2403step0Labels = raw2403Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2403 raw2403Labels permutation32 permutation4
    mixedMoment B raw2403step0 raw2403step0Labels = mixedMoment B raw2403step1 raw2403step1Labels := by
      have ha : raw2403step1 = raw2403step0 := by apply Matrix.ext; unfold raw2403step1 raw2403step0; decide +kernel
      have hl : raw2403step0Labels = labelEmbedding7 ∘ raw2403step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2403step0 raw2403step0Labels raw2403step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw2404 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2404 raw2404Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw2404 raw2404Labels = mixedMoment B raw2404step0 raw2404step0Labels := by
      have ha : raw2404step0 = (fun i j => raw2404 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2404step0 raw2404; decide +kernel
      have hl : raw2404step0Labels = raw2404Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2404 raw2404Labels permutation32 permutation4
    _ = mixedMoment B node3694 node3694Labels := by rfl

def raw2405 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2405Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw2405step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2405step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2405 raw2405Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw2405 raw2405Labels = mixedMoment B raw2405step0 raw2405step0Labels := by
      have ha : raw2405step0 = (fun i j => raw2405 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2405step0 raw2405; decide +kernel
      have hl : raw2405step0Labels = raw2405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2405 raw2405Labels permutation32 permutation6
    mixedMoment B raw2405step0 raw2405step0Labels = mixedMoment B raw2405step1 raw2405step1Labels := by
      have ha : raw2405step1 = -raw2405step0 := by apply Matrix.ext; change ∀ i j, raw2405step1 i j = -(raw2405step0 i j); unfold raw2405step1 raw2405step0; decide +kernel
      have hl : raw2405step1Labels = raw2405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2405step1 raw2405step1Labels = mixedMoment B raw2405step2 raw2405step2Labels := by
      have ha : raw2405step2 = raw2405step1 := by apply Matrix.ext; unfold raw2405step2 raw2405step1; decide +kernel
      have hl : raw2405step1Labels = labelEmbedding1 ∘ raw2405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2405step1 raw2405step1Labels raw2405step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

def raw2406 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2406step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2406step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2406step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2406 raw2406Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw2406 raw2406Labels = mixedMoment B raw2406step0 raw2406step0Labels := by
      have ha : raw2406step0 = (fun i j => raw2406 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2406step0 raw2406; decide +kernel
      have hl : raw2406step0Labels = raw2406Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2406 raw2406Labels permutation152 permutation4
    mixedMoment B raw2406step0 raw2406step0Labels = mixedMoment B raw2406step1 raw2406step1Labels := by
      have ha : raw2406step1 = raw2406step0 := by apply Matrix.ext; unfold raw2406step1 raw2406step0; decide +kernel
      have hl : raw2406step0Labels = labelEmbedding7 ∘ raw2406step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2406step0 raw2406step0Labels raw2406step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

def raw2407 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2407 raw2407Labels = mixedMoment B node3701 node3701Labels := by
  calc
    mixedMoment B raw2407 raw2407Labels = mixedMoment B raw2407step0 raw2407step0Labels := by
      have ha : raw2407step0 = (fun i j => raw2407 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2407step0 raw2407; decide +kernel
      have hl : raw2407step0Labels = raw2407Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2407 raw2407Labels permutation152 permutation4
    _ = mixedMoment B node3701 node3701Labels := by rfl

def raw2408 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2408Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2408 raw2408Labels = mixedMoment B node3751 node3751Labels := by
  calc
    mixedMoment B raw2408 raw2408Labels = mixedMoment B raw2408step0 raw2408step0Labels := by
      have ha : raw2408step0 = (fun i j => raw2408 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2408step0 raw2408; decide +kernel
      have hl : raw2408step0Labels = raw2408Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2408 raw2408Labels permutation152 permutation6
    mixedMoment B raw2408step0 raw2408step0Labels = mixedMoment B raw2408step1 raw2408step1Labels := by
      have ha : raw2408step1 = -raw2408step0 := by apply Matrix.ext; change ∀ i j, raw2408step1 i j = -(raw2408step0 i j); unfold raw2408step1 raw2408step0; decide +kernel
      have hl : raw2408step1Labels = raw2408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2408step1 raw2408step1Labels = mixedMoment B raw2408step2 raw2408step2Labels := by
      have ha : raw2408step2 = raw2408step1 := by apply Matrix.ext; unfold raw2408step2 raw2408step1; decide +kernel
      have hl : raw2408step1Labels = labelEmbedding1 ∘ raw2408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2408step1 raw2408step1Labels raw2408step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3751 node3751Labels := by rfl

def raw2409 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2409step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2409step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2409 raw2409Labels = mixedMoment B node5364 node5364Labels := by
  calc
    mixedMoment B raw2409 raw2409Labels = mixedMoment B raw2409step0 raw2409step0Labels := by
      have ha : raw2409step0 = (fun i j => raw2409 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2409step0 raw2409; decide +kernel
      have hl : raw2409step0Labels = raw2409Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2409 raw2409Labels permutation32 permutation4
    mixedMoment B raw2409step0 raw2409step0Labels = mixedMoment B raw2409step1 raw2409step1Labels := by
      have ha : raw2409step1 = raw2409step0 := by apply Matrix.ext; unfold raw2409step1 raw2409step0; decide +kernel
      have hl : raw2409step0Labels = labelEmbedding7 ∘ raw2409step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2409step0 raw2409step0Labels raw2409step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5364 node5364Labels := by rfl

def raw2410 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2410 raw2410Labels = mixedMoment B node3702 node3702Labels := by
  calc
    mixedMoment B raw2410 raw2410Labels = mixedMoment B raw2410step0 raw2410step0Labels := by
      have ha : raw2410step0 = (fun i j => raw2410 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2410step0 raw2410; decide +kernel
      have hl : raw2410step0Labels = raw2410Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2410 raw2410Labels permutation32 permutation4
    _ = mixedMoment B node3702 node3702Labels := by rfl

def raw2411 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2411Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2411step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2411 raw2411Labels = mixedMoment B node3702 node3702Labels := by
  calc
    mixedMoment B raw2411 raw2411Labels = mixedMoment B raw2411step0 raw2411step0Labels := by
      have ha : raw2411step0 = (fun i j => raw2411 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2411step0 raw2411; decide +kernel
      have hl : raw2411step0Labels = raw2411Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2411 raw2411Labels permutation151 permutation6
    mixedMoment B raw2411step0 raw2411step0Labels = mixedMoment B raw2411step1 raw2411step1Labels := by
      have ha : raw2411step1 = raw2411step0 := by apply Matrix.ext; unfold raw2411step1 raw2411step0; decide +kernel
      have hl : raw2411step0Labels = labelEmbedding1 ∘ raw2411step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2411step0 raw2411step0Labels raw2411step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3702 node3702Labels := by rfl

def raw2412 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2412step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2412step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2412 raw2412Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw2412 raw2412Labels = mixedMoment B raw2412step0 raw2412step0Labels := by
      have ha : raw2412step0 = (fun i j => raw2412 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2412step0 raw2412; decide +kernel
      have hl : raw2412step0Labels = raw2412Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2412 raw2412Labels permutation152 permutation4
    mixedMoment B raw2412step0 raw2412step0Labels = mixedMoment B raw2412step1 raw2412step1Labels := by
      have ha : raw2412step1 = raw2412step0 := by apply Matrix.ext; unfold raw2412step1 raw2412step0; decide +kernel
      have hl : raw2412step0Labels = labelEmbedding7 ∘ raw2412step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2412step0 raw2412step0Labels raw2412step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw2413 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2413 raw2413Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw2413 raw2413Labels = mixedMoment B raw2413step0 raw2413step0Labels := by
      have ha : raw2413step0 = (fun i j => raw2413 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2413step0 raw2413; decide +kernel
      have hl : raw2413step0Labels = raw2413Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2413 raw2413Labels permutation152 permutation4
    _ = mixedMoment B node3703 node3703Labels := by rfl

def raw2414 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2414Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2414step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2414step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2414 raw2414Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw2414 raw2414Labels = mixedMoment B raw2414step0 raw2414step0Labels := by
      have ha : raw2414step0 = (fun i j => raw2414 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2414step0 raw2414; decide +kernel
      have hl : raw2414step0Labels = raw2414Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2414 raw2414Labels permutation152 permutation6
    mixedMoment B raw2414step0 raw2414step0Labels = mixedMoment B raw2414step1 raw2414step1Labels := by
      have ha : raw2414step1 = -raw2414step0 := by apply Matrix.ext; change ∀ i j, raw2414step1 i j = -(raw2414step0 i j); unfold raw2414step1 raw2414step0; decide +kernel
      have hl : raw2414step1Labels = raw2414step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2414step1 raw2414step1Labels = mixedMoment B raw2414step2 raw2414step2Labels := by
      have ha : raw2414step2 = raw2414step1 := by apply Matrix.ext; unfold raw2414step2 raw2414step1; decide +kernel
      have hl : raw2414step1Labels = labelEmbedding1 ∘ raw2414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2414step1 raw2414step1Labels raw2414step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

def raw2415 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2415step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2415step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2415 raw2415Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw2415 raw2415Labels = mixedMoment B raw2415step0 raw2415step0Labels := by
      have ha : raw2415step0 = (fun i j => raw2415 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2415step0 raw2415; decide +kernel
      have hl : raw2415step0Labels = raw2415Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2415 raw2415Labels permutation32 permutation4
    mixedMoment B raw2415step0 raw2415step0Labels = mixedMoment B raw2415step1 raw2415step1Labels := by
      have ha : raw2415step1 = raw2415step0 := by apply Matrix.ext; unfold raw2415step1 raw2415step0; decide +kernel
      have hl : raw2415step0Labels = labelEmbedding7 ∘ raw2415step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2415step0 raw2415step0Labels raw2415step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw2416 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2416 raw2416Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw2416 raw2416Labels = mixedMoment B raw2416step0 raw2416step0Labels := by
      have ha : raw2416step0 = (fun i j => raw2416 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2416step0 raw2416; decide +kernel
      have hl : raw2416step0Labels = raw2416Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2416 raw2416Labels permutation32 permutation4
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw2417 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2417Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2417step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2417step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2417 raw2417Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw2417 raw2417Labels = mixedMoment B raw2417step0 raw2417step0Labels := by
      have ha : raw2417step0 = (fun i j => raw2417 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2417step0 raw2417; decide +kernel
      have hl : raw2417step0Labels = raw2417Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2417 raw2417Labels permutation33 permutation6
    mixedMoment B raw2417step0 raw2417step0Labels = mixedMoment B raw2417step1 raw2417step1Labels := by
      have ha : raw2417step1 = -raw2417step0 := by apply Matrix.ext; change ∀ i j, raw2417step1 i j = -(raw2417step0 i j); unfold raw2417step1 raw2417step0; decide +kernel
      have hl : raw2417step1Labels = raw2417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2417step1 raw2417step1Labels = mixedMoment B raw2417step2 raw2417step2Labels := by
      have ha : raw2417step2 = raw2417step1 := by apply Matrix.ext; unfold raw2417step2 raw2417step1; decide +kernel
      have hl : raw2417step1Labels = labelEmbedding1 ∘ raw2417step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2417step1 raw2417step1Labels raw2417step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

def raw2418 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2418step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2418 raw2418Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw2418 raw2418Labels = mixedMoment B raw2418step0 raw2418step0Labels := by
      have ha : raw2418step0 = (fun i j => raw2418 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2418step0 raw2418; decide +kernel
      have hl : raw2418step0Labels = raw2418Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2418 raw2418Labels permutation32 permutation4
    mixedMoment B raw2418step0 raw2418step0Labels = mixedMoment B raw2418step1 raw2418step1Labels := by
      have ha : raw2418step1 = raw2418step0 := by apply Matrix.ext; unfold raw2418step1 raw2418step0; decide +kernel
      have hl : raw2418step0Labels = labelEmbedding7 ∘ raw2418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2418step0 raw2418step0Labels raw2418step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw2419 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2419 raw2419Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw2419 raw2419Labels = mixedMoment B raw2419step0 raw2419step0Labels := by
      have ha : raw2419step0 = (fun i j => raw2419 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2419step0 raw2419; decide +kernel
      have hl : raw2419step0Labels = raw2419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2419 raw2419Labels permutation32 permutation4
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw2420 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2420Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw2420step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw2420step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw2420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2420 raw2420Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw2420 raw2420Labels = mixedMoment B raw2420step0 raw2420step0Labels := by
      have ha : raw2420step0 = (fun i j => raw2420 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2420step0 raw2420; decide +kernel
      have hl : raw2420step0Labels = raw2420Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2420 raw2420Labels permutation36 permutation6
    mixedMoment B raw2420step0 raw2420step0Labels = mixedMoment B raw2420step1 raw2420step1Labels := by
      have ha : raw2420step1 = -raw2420step0 := by apply Matrix.ext; change ∀ i j, raw2420step1 i j = -(raw2420step0 i j); unfold raw2420step1 raw2420step0; decide +kernel
      have hl : raw2420step1Labels = raw2420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2420step1 raw2420step1Labels = mixedMoment B raw2420step2 raw2420step2Labels := by
      have ha : raw2420step2 = raw2420step1 := by apply Matrix.ext; unfold raw2420step2 raw2420step1; decide +kernel
      have hl : raw2420step1Labels = labelEmbedding1 ∘ raw2420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2420step1 raw2420step1Labels raw2420step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3771 node3771Labels := by rfl

def raw2421 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2421step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2421 raw2421Labels = mixedMoment B node5372 node5372Labels := by
  calc
    mixedMoment B raw2421 raw2421Labels = mixedMoment B raw2421step0 raw2421step0Labels := by
      have ha : raw2421step0 = (fun i j => raw2421 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2421step0 raw2421; decide +kernel
      have hl : raw2421step0Labels = raw2421Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2421 raw2421Labels permutation152 permutation4
    mixedMoment B raw2421step0 raw2421step0Labels = mixedMoment B raw2421step1 raw2421step1Labels := by
      have ha : raw2421step1 = raw2421step0 := by apply Matrix.ext; unfold raw2421step1 raw2421step0; decide +kernel
      have hl : raw2421step0Labels = labelEmbedding7 ∘ raw2421step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2421step0 raw2421step0Labels raw2421step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5372 node5372Labels := by rfl

def raw2422 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2422 raw2422Labels = mixedMoment B node3708 node3708Labels := by
  calc
    mixedMoment B raw2422 raw2422Labels = mixedMoment B raw2422step0 raw2422step0Labels := by
      have ha : raw2422step0 = (fun i j => raw2422 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2422step0 raw2422; decide +kernel
      have hl : raw2422step0Labels = raw2422Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2422 raw2422Labels permutation152 permutation4
    _ = mixedMoment B node3708 node3708Labels := by rfl

def raw2423 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2423Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2423step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2423 raw2423Labels = mixedMoment B node3791 node3791Labels := by
  calc
    mixedMoment B raw2423 raw2423Labels = mixedMoment B raw2423step0 raw2423step0Labels := by
      have ha : raw2423step0 = (fun i j => raw2423 (permutation662 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2423step0 raw2423; decide +kernel
      have hl : raw2423step0Labels = raw2423Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2423 raw2423Labels permutation662 permutation6
    mixedMoment B raw2423step0 raw2423step0Labels = mixedMoment B raw2423step1 raw2423step1Labels := by
      have ha : raw2423step1 = raw2423step0 := by apply Matrix.ext; unfold raw2423step1 raw2423step0; decide +kernel
      have hl : raw2423step0Labels = labelEmbedding1 ∘ raw2423step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2423step0 raw2423step0Labels raw2423step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3791 node3791Labels := by rfl

def raw2424 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2424step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2424 raw2424Labels = mixedMoment B node5373 node5373Labels := by
  calc
    mixedMoment B raw2424 raw2424Labels = mixedMoment B raw2424step0 raw2424step0Labels := by
      have ha : raw2424step0 = (fun i j => raw2424 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2424step0 raw2424; decide +kernel
      have hl : raw2424step0Labels = raw2424Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2424 raw2424Labels permutation152 permutation4
    mixedMoment B raw2424step0 raw2424step0Labels = mixedMoment B raw2424step1 raw2424step1Labels := by
      have ha : raw2424step1 = raw2424step0 := by apply Matrix.ext; unfold raw2424step1 raw2424step0; decide +kernel
      have hl : raw2424step0Labels = labelEmbedding7 ∘ raw2424step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2424step0 raw2424step0Labels raw2424step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5373 node5373Labels := by rfl

def raw2425 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2425 raw2425Labels = mixedMoment B node3709 node3709Labels := by
  calc
    mixedMoment B raw2425 raw2425Labels = mixedMoment B raw2425step0 raw2425step0Labels := by
      have ha : raw2425step0 = (fun i j => raw2425 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2425step0 raw2425; decide +kernel
      have hl : raw2425step0Labels = raw2425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2425 raw2425Labels permutation152 permutation4
    _ = mixedMoment B node3709 node3709Labels := by rfl

def raw2426 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2426Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2426step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2426step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2426 raw2426Labels = mixedMoment B node3792 node3792Labels := by
  calc
    mixedMoment B raw2426 raw2426Labels = mixedMoment B raw2426step0 raw2426step0Labels := by
      have ha : raw2426step0 = (fun i j => raw2426 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2426step0 raw2426; decide +kernel
      have hl : raw2426step0Labels = raw2426Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2426 raw2426Labels permutation176 permutation6
    mixedMoment B raw2426step0 raw2426step0Labels = mixedMoment B raw2426step1 raw2426step1Labels := by
      have ha : raw2426step1 = -raw2426step0 := by apply Matrix.ext; change ∀ i j, raw2426step1 i j = -(raw2426step0 i j); unfold raw2426step1 raw2426step0; decide +kernel
      have hl : raw2426step1Labels = raw2426step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2426step1 raw2426step1Labels = mixedMoment B raw2426step2 raw2426step2Labels := by
      have ha : raw2426step2 = raw2426step1 := by apply Matrix.ext; unfold raw2426step2 raw2426step1; decide +kernel
      have hl : raw2426step1Labels = labelEmbedding1 ∘ raw2426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2426step1 raw2426step1Labels raw2426step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3792 node3792Labels := by rfl

def raw2427 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2427step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2427 raw2427Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw2427 raw2427Labels = mixedMoment B raw2427step0 raw2427step0Labels := by
      have ha : raw2427step0 = (fun i j => raw2427 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2427step0 raw2427; decide +kernel
      have hl : raw2427step0Labels = raw2427Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2427 raw2427Labels permutation152 permutation4
    mixedMoment B raw2427step0 raw2427step0Labels = mixedMoment B raw2427step1 raw2427step1Labels := by
      have ha : raw2427step1 = raw2427step0 := by apply Matrix.ext; unfold raw2427step1 raw2427step0; decide +kernel
      have hl : raw2427step0Labels = labelEmbedding7 ∘ raw2427step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2427step0 raw2427step0Labels raw2427step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

def raw2428 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2428 raw2428Labels = mixedMoment B node3713 node3713Labels := by
  calc
    mixedMoment B raw2428 raw2428Labels = mixedMoment B raw2428step0 raw2428step0Labels := by
      have ha : raw2428step0 = (fun i j => raw2428 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2428step0 raw2428; decide +kernel
      have hl : raw2428step0Labels = raw2428Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2428 raw2428Labels permutation152 permutation4
    _ = mixedMoment B node3713 node3713Labels := by rfl

def raw2429 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2429Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw2429step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2429step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2429step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2429 raw2429Labels = mixedMoment B node3713 node3713Labels := by
  calc
    mixedMoment B raw2429 raw2429Labels = mixedMoment B raw2429step0 raw2429step0Labels := by
      have ha : raw2429step0 = (fun i j => raw2429 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2429step0 raw2429; decide +kernel
      have hl : raw2429step0Labels = raw2429Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2429 raw2429Labels permutation176 permutation6
    mixedMoment B raw2429step0 raw2429step0Labels = mixedMoment B raw2429step1 raw2429step1Labels := by
      have ha : raw2429step1 = -raw2429step0 := by apply Matrix.ext; change ∀ i j, raw2429step1 i j = -(raw2429step0 i j); unfold raw2429step1 raw2429step0; decide +kernel
      have hl : raw2429step1Labels = raw2429step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2429step1 raw2429step1Labels = mixedMoment B raw2429step2 raw2429step2Labels := by
      have ha : raw2429step2 = raw2429step1 := by apply Matrix.ext; unfold raw2429step2 raw2429step1; decide +kernel
      have hl : raw2429step1Labels = labelEmbedding1 ∘ raw2429step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2429step1 raw2429step1Labels raw2429step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3713 node3713Labels := by rfl

def raw2430 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2430step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2430step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2430 raw2430Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw2430 raw2430Labels = mixedMoment B raw2430step0 raw2430step0Labels := by
      have ha : raw2430step0 = (fun i j => raw2430 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2430step0 raw2430; decide +kernel
      have hl : raw2430step0Labels = raw2430Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2430 raw2430Labels permutation152 permutation4
    mixedMoment B raw2430step0 raw2430step0Labels = mixedMoment B raw2430step1 raw2430step1Labels := by
      have ha : raw2430step1 = raw2430step0 := by apply Matrix.ext; unfold raw2430step1 raw2430step0; decide +kernel
      have hl : raw2430step0Labels = labelEmbedding7 ∘ raw2430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2430step0 raw2430step0Labels raw2430step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw2431 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2431 raw2431Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw2431 raw2431Labels = mixedMoment B raw2431step0 raw2431step0Labels := by
      have ha : raw2431step0 = (fun i j => raw2431 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2431step0 raw2431; decide +kernel
      have hl : raw2431step0Labels = raw2431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2431 raw2431Labels permutation152 permutation4
    _ = mixedMoment B node3719 node3719Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
