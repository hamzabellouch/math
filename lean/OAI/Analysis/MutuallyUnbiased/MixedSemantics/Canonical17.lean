import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2176 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2176Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2176 raw2176Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw2176 raw2176Labels = mixedMoment B raw2176step0 raw2176step0Labels := by
      have ha : raw2176step0 = (fun i j => raw2176 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2176step0 raw2176; decide +kernel
      have hl : raw2176step0Labels = raw2176Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2176 raw2176Labels permutation154 permutation4
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw2177 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2177Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw2177step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2177step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2177 raw2177Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw2177 raw2177Labels = mixedMoment B raw2177step0 raw2177step0Labels := by
      have ha : raw2177step0 = (fun i j => raw2177 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2177step0 raw2177; decide +kernel
      have hl : raw2177step0Labels = raw2177Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2177 raw2177Labels permutation162 permutation3
    mixedMoment B raw2177step0 raw2177step0Labels = mixedMoment B raw2177step1 raw2177step1Labels := by
      have ha : raw2177step1 = -raw2177step0 := by apply Matrix.ext; change ∀ i j, raw2177step1 i j = -(raw2177step0 i j); unfold raw2177step1 raw2177step0; decide +kernel
      have hl : raw2177step1Labels = raw2177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2177step1 raw2177step1Labels = mixedMoment B raw2177step2 raw2177step2Labels := by
      have ha : raw2177step2 = raw2177step1 := by apply Matrix.ext; unfold raw2177step2 raw2177step1; decide +kernel
      have hl : raw2177step1Labels = labelEmbedding1 ∘ raw2177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2177step1 raw2177step1Labels raw2177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw2178 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw2178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2178step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2178step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2178 raw2178Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw2178 raw2178Labels = mixedMoment B raw2178step0 raw2178step0Labels := by
      have ha : raw2178step0 = (fun i j => raw2178 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2178step0 raw2178; decide +kernel
      have hl : raw2178step0Labels = raw2178Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2178 raw2178Labels permutation32 permutation5
    mixedMoment B raw2178step0 raw2178step0Labels = mixedMoment B raw2178step1 raw2178step1Labels := by
      have ha : raw2178step1 = raw2178step0 := by apply Matrix.ext; unfold raw2178step1 raw2178step0; decide +kernel
      have hl : raw2178step0Labels = labelEmbedding8 ∘ raw2178step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2178step0 raw2178step0Labels raw2178step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw2179 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw2179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw2179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2179 raw2179Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw2179 raw2179Labels = mixedMoment B raw2179step0 raw2179step0Labels := by
      have ha : raw2179step0 = (fun i j => raw2179 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2179step0 raw2179; decide +kernel
      have hl : raw2179step0Labels = raw2179Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2179 raw2179Labels permutation33 permutation4
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw2180 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw2180Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw2180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw2180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw2180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2180 raw2180Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw2180 raw2180Labels = mixedMoment B raw2180step0 raw2180step0Labels := by
      have ha : raw2180step0 = (fun i j => raw2180 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2180step0 raw2180; decide +kernel
      have hl : raw2180step0Labels = raw2180Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2180 raw2180Labels permutation34 permutation3
    mixedMoment B raw2180step0 raw2180step0Labels = mixedMoment B raw2180step1 raw2180step1Labels := by
      have ha : raw2180step1 = -raw2180step0 := by apply Matrix.ext; change ∀ i j, raw2180step1 i j = -(raw2180step0 i j); unfold raw2180step1 raw2180step0; decide +kernel
      have hl : raw2180step1Labels = raw2180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2180step1 raw2180step1Labels = mixedMoment B raw2180step2 raw2180step2Labels := by
      have ha : raw2180step2 = raw2180step1 := by apply Matrix.ext; unfold raw2180step2 raw2180step1; decide +kernel
      have hl : raw2180step1Labels = labelEmbedding1 ∘ raw2180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2180step1 raw2180step1Labels raw2180step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw2181 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2181step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2181 raw2181Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw2181 raw2181Labels = mixedMoment B raw2181step0 raw2181step0Labels := by
      have ha : raw2181step0 = (fun i j => raw2181 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2181step0 raw2181; decide +kernel
      have hl : raw2181step0Labels = raw2181Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2181 raw2181Labels permutation152 permutation5
    mixedMoment B raw2181step0 raw2181step0Labels = mixedMoment B raw2181step1 raw2181step1Labels := by
      have ha : raw2181step1 = raw2181step0 := by apply Matrix.ext; unfold raw2181step1 raw2181step0; decide +kernel
      have hl : raw2181step0Labels = labelEmbedding8 ∘ raw2181step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2181step0 raw2181step0Labels raw2181step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw2182 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2182 raw2182Labels = mixedMoment B node2908 node2908Labels := by
  calc
    mixedMoment B raw2182 raw2182Labels = mixedMoment B raw2182step0 raw2182step0Labels := by
      have ha : raw2182step0 = (fun i j => raw2182 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2182step0 raw2182; decide +kernel
      have hl : raw2182step0Labels = raw2182Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2182 raw2182Labels permutation152 permutation4
    _ = mixedMoment B node2908 node2908Labels := by rfl

def raw2183 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2183Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw2183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw2183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw2183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2183 raw2183Labels = mixedMoment B node3600 node3600Labels := by
  calc
    mixedMoment B raw2183 raw2183Labels = mixedMoment B raw2183step0 raw2183step0Labels := by
      have ha : raw2183step0 = (fun i j => raw2183 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2183step0 raw2183; decide +kernel
      have hl : raw2183step0Labels = raw2183Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2183 raw2183Labels permutation161 permutation3
    mixedMoment B raw2183step0 raw2183step0Labels = mixedMoment B raw2183step1 raw2183step1Labels := by
      have ha : raw2183step1 = -raw2183step0 := by apply Matrix.ext; change ∀ i j, raw2183step1 i j = -(raw2183step0 i j); unfold raw2183step1 raw2183step0; decide +kernel
      have hl : raw2183step1Labels = raw2183step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2183step1 raw2183step1Labels = mixedMoment B raw2183step2 raw2183step2Labels := by
      have ha : raw2183step2 = raw2183step1 := by apply Matrix.ext; unfold raw2183step2 raw2183step1; decide +kernel
      have hl : raw2183step1Labels = labelEmbedding1 ∘ raw2183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2183step1 raw2183step1Labels raw2183step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3600 node3600Labels := by rfl

def raw2184 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw2184step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw2184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2184 raw2184Labels = mixedMoment B node5156 node5156Labels := by
  calc
    mixedMoment B raw2184 raw2184Labels = mixedMoment B raw2184step0 raw2184step0Labels := by
      have ha : raw2184step0 = (fun i j => raw2184 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2184step0 raw2184; decide +kernel
      have hl : raw2184step0Labels = raw2184Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2184 raw2184Labels permutation32 permutation5
    mixedMoment B raw2184step0 raw2184step0Labels = mixedMoment B raw2184step1 raw2184step1Labels := by
      have ha : raw2184step1 = raw2184step0 := by apply Matrix.ext; unfold raw2184step1 raw2184step0; decide +kernel
      have hl : raw2184step0Labels = labelEmbedding8 ∘ raw2184step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2184step0 raw2184step0Labels raw2184step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5156 node5156Labels := by rfl

def raw2185 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2185Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw2185step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2185 raw2185Labels = mixedMoment B node2911 node2911Labels := by
  calc
    mixedMoment B raw2185 raw2185Labels = mixedMoment B raw2185step0 raw2185step0Labels := by
      have ha : raw2185step0 = (fun i j => raw2185 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2185step0 raw2185; decide +kernel
      have hl : raw2185step0Labels = raw2185Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2185 raw2185Labels permutation32 permutation4
    _ = mixedMoment B node2911 node2911Labels := by rfl

def raw2186 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2186Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-2, 2, 0]]
def raw2186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]
def raw2186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]
def raw2186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2186 raw2186Labels = mixedMoment B node3611 node3611Labels := by
  calc
    mixedMoment B raw2186 raw2186Labels = mixedMoment B raw2186step0 raw2186step0Labels := by
      have ha : raw2186step0 = (fun i j => raw2186 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2186step0 raw2186; decide +kernel
      have hl : raw2186step0Labels = raw2186Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2186 raw2186Labels permutation35 permutation3
    mixedMoment B raw2186step0 raw2186step0Labels = mixedMoment B raw2186step1 raw2186step1Labels := by
      have ha : raw2186step1 = -raw2186step0 := by apply Matrix.ext; change ∀ i j, raw2186step1 i j = -(raw2186step0 i j); unfold raw2186step1 raw2186step0; decide +kernel
      have hl : raw2186step1Labels = raw2186step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2186step1 raw2186step1Labels = mixedMoment B raw2186step2 raw2186step2Labels := by
      have ha : raw2186step2 = raw2186step1 := by apply Matrix.ext; unfold raw2186step2 raw2186step1; decide +kernel
      have hl : raw2186step1Labels = labelEmbedding1 ∘ raw2186step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2186step1 raw2186step1Labels raw2186step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3611 node3611Labels := by rfl

def raw2187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2187step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2187 raw2187Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw2187 raw2187Labels = mixedMoment B raw2187step0 raw2187step0Labels := by
      have ha : raw2187step0 = (fun i j => raw2187 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2187step0 raw2187; decide +kernel
      have hl : raw2187step0Labels = raw2187Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2187 raw2187Labels permutation152 permutation4
    mixedMoment B raw2187step0 raw2187step0Labels = mixedMoment B raw2187step1 raw2187step1Labels := by
      have ha : raw2187step1 = raw2187step0 := by apply Matrix.ext; unfold raw2187step1 raw2187step0; decide +kernel
      have hl : raw2187step0Labels = labelEmbedding7 ∘ raw2187step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2187step0 raw2187step0Labels raw2187step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

def raw2188 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2188Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2188step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2188 raw2188Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw2188 raw2188Labels = mixedMoment B raw2188step0 raw2188step0Labels := by
      have ha : raw2188step0 = (fun i j => raw2188 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2188step0 raw2188; decide +kernel
      have hl : raw2188step0Labels = raw2188Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2188 raw2188Labels permutation152 permutation4
    _ = mixedMoment B node2589 node2589Labels := by rfl

def raw2189 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2189Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2189step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2189step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2189 raw2189Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw2189 raw2189Labels = mixedMoment B raw2189step0 raw2189step0Labels := by
      have ha : raw2189step0 = (fun i j => raw2189 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2189step0 raw2189; decide +kernel
      have hl : raw2189step0Labels = raw2189Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2189 raw2189Labels permutation176 permutation6
    mixedMoment B raw2189step0 raw2189step0Labels = mixedMoment B raw2189step1 raw2189step1Labels := by
      have ha : raw2189step1 = -raw2189step0 := by apply Matrix.ext; change ∀ i j, raw2189step1 i j = -(raw2189step0 i j); unfold raw2189step1 raw2189step0; decide +kernel
      have hl : raw2189step1Labels = raw2189step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2189step1 raw2189step1Labels = mixedMoment B raw2189step2 raw2189step2Labels := by
      have ha : raw2189step2 = raw2189step1 := by apply Matrix.ext; unfold raw2189step2 raw2189step1; decide +kernel
      have hl : raw2189step1Labels = labelEmbedding1 ∘ raw2189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2189step1 raw2189step1Labels raw2189step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3563 node3563Labels := by rfl

def raw2190 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2190step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2190 raw2190Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw2190 raw2190Labels = mixedMoment B raw2190step0 raw2190step0Labels := by
      have ha : raw2190step0 = (fun i j => raw2190 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2190step0 raw2190; decide +kernel
      have hl : raw2190step0Labels = raw2190Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2190 raw2190Labels permutation32 permutation4
    mixedMoment B raw2190step0 raw2190step0Labels = mixedMoment B raw2190step1 raw2190step1Labels := by
      have ha : raw2190step1 = raw2190step0 := by apply Matrix.ext; unfold raw2190step1 raw2190step0; decide +kernel
      have hl : raw2190step0Labels = labelEmbedding7 ∘ raw2190step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2190step0 raw2190step0Labels raw2190step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw2191 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2191 raw2191Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw2191 raw2191Labels = mixedMoment B raw2191step0 raw2191step0Labels := by
      have ha : raw2191step0 = (fun i j => raw2191 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2191step0 raw2191; decide +kernel
      have hl : raw2191step0Labels = raw2191Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2191 raw2191Labels permutation32 permutation4
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw2192 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2192Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw2192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2192 raw2192Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw2192 raw2192Labels = mixedMoment B raw2192step0 raw2192step0Labels := by
      have ha : raw2192step0 = (fun i j => raw2192 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2192step0 raw2192; decide +kernel
      have hl : raw2192step0Labels = raw2192Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2192 raw2192Labels permutation38 permutation6
    mixedMoment B raw2192step0 raw2192step0Labels = mixedMoment B raw2192step1 raw2192step1Labels := by
      have ha : raw2192step1 = -raw2192step0 := by apply Matrix.ext; change ∀ i j, raw2192step1 i j = -(raw2192step0 i j); unfold raw2192step1 raw2192step0; decide +kernel
      have hl : raw2192step1Labels = raw2192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2192step1 raw2192step1Labels = mixedMoment B raw2192step2 raw2192step2Labels := by
      have ha : raw2192step2 = raw2192step1 := by apply Matrix.ext; unfold raw2192step2 raw2192step1; decide +kernel
      have hl : raw2192step1Labels = labelEmbedding1 ∘ raw2192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2192step1 raw2192step1Labels raw2192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw2193 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2193step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2193 raw2193Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw2193 raw2193Labels = mixedMoment B raw2193step0 raw2193step0Labels := by
      have ha : raw2193step0 = (fun i j => raw2193 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2193step0 raw2193; decide +kernel
      have hl : raw2193step0Labels = raw2193Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2193 raw2193Labels permutation152 permutation4
    mixedMoment B raw2193step0 raw2193step0Labels = mixedMoment B raw2193step1 raw2193step1Labels := by
      have ha : raw2193step1 = raw2193step0 := by apply Matrix.ext; unfold raw2193step1 raw2193step0; decide +kernel
      have hl : raw2193step0Labels = labelEmbedding7 ∘ raw2193step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2193step0 raw2193step0Labels raw2193step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw2194 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2194 raw2194Labels = mixedMoment B node2593 node2593Labels := by
  calc
    mixedMoment B raw2194 raw2194Labels = mixedMoment B raw2194step0 raw2194step0Labels := by
      have ha : raw2194step0 = (fun i j => raw2194 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2194step0 raw2194; decide +kernel
      have hl : raw2194step0Labels = raw2194Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2194 raw2194Labels permutation152 permutation4
    _ = mixedMoment B node2593 node2593Labels := by rfl

def raw2195 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2195Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2195step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2195step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2195 raw2195Labels = mixedMoment B node3602 node3602Labels := by
  calc
    mixedMoment B raw2195 raw2195Labels = mixedMoment B raw2195step0 raw2195step0Labels := by
      have ha : raw2195step0 = (fun i j => raw2195 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2195step0 raw2195; decide +kernel
      have hl : raw2195step0Labels = raw2195Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2195 raw2195Labels permutation152 permutation6
    mixedMoment B raw2195step0 raw2195step0Labels = mixedMoment B raw2195step1 raw2195step1Labels := by
      have ha : raw2195step1 = -raw2195step0 := by apply Matrix.ext; change ∀ i j, raw2195step1 i j = -(raw2195step0 i j); unfold raw2195step1 raw2195step0; decide +kernel
      have hl : raw2195step1Labels = raw2195step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2195step1 raw2195step1Labels = mixedMoment B raw2195step2 raw2195step2Labels := by
      have ha : raw2195step2 = raw2195step1 := by apply Matrix.ext; unfold raw2195step2 raw2195step1; decide +kernel
      have hl : raw2195step1Labels = labelEmbedding1 ∘ raw2195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2195step1 raw2195step1Labels raw2195step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3602 node3602Labels := by rfl

def raw2196 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2196step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2196 raw2196Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw2196 raw2196Labels = mixedMoment B raw2196step0 raw2196step0Labels := by
      have ha : raw2196step0 = (fun i j => raw2196 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2196step0 raw2196; decide +kernel
      have hl : raw2196step0Labels = raw2196Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2196 raw2196Labels permutation32 permutation4
    mixedMoment B raw2196step0 raw2196step0Labels = mixedMoment B raw2196step1 raw2196step1Labels := by
      have ha : raw2196step1 = raw2196step0 := by apply Matrix.ext; unfold raw2196step1 raw2196step0; decide +kernel
      have hl : raw2196step0Labels = labelEmbedding7 ∘ raw2196step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2196step0 raw2196step0Labels raw2196step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw2197 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2197 raw2197Labels = mixedMoment B node2594 node2594Labels := by
  calc
    mixedMoment B raw2197 raw2197Labels = mixedMoment B raw2197step0 raw2197step0Labels := by
      have ha : raw2197step0 = (fun i j => raw2197 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2197step0 raw2197; decide +kernel
      have hl : raw2197step0Labels = raw2197Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2197 raw2197Labels permutation32 permutation4
    _ = mixedMoment B node2594 node2594Labels := by rfl

def raw2198 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2198Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw2198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2198 raw2198Labels = mixedMoment B node3603 node3603Labels := by
  calc
    mixedMoment B raw2198 raw2198Labels = mixedMoment B raw2198step0 raw2198step0Labels := by
      have ha : raw2198step0 = (fun i j => raw2198 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2198step0 raw2198; decide +kernel
      have hl : raw2198step0Labels = raw2198Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2198 raw2198Labels permutation32 permutation6
    mixedMoment B raw2198step0 raw2198step0Labels = mixedMoment B raw2198step1 raw2198step1Labels := by
      have ha : raw2198step1 = -raw2198step0 := by apply Matrix.ext; change ∀ i j, raw2198step1 i j = -(raw2198step0 i j); unfold raw2198step1 raw2198step0; decide +kernel
      have hl : raw2198step1Labels = raw2198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2198step1 raw2198step1Labels = mixedMoment B raw2198step2 raw2198step2Labels := by
      have ha : raw2198step2 = raw2198step1 := by apply Matrix.ext; unfold raw2198step2 raw2198step1; decide +kernel
      have hl : raw2198step1Labels = labelEmbedding1 ∘ raw2198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2198step1 raw2198step1Labels raw2198step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3603 node3603Labels := by rfl

def raw2199 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2199step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2199 raw2199Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw2199 raw2199Labels = mixedMoment B raw2199step0 raw2199step0Labels := by
      have ha : raw2199step0 = (fun i j => raw2199 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2199step0 raw2199; decide +kernel
      have hl : raw2199step0Labels = raw2199Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2199 raw2199Labels permutation32 permutation4
    mixedMoment B raw2199step0 raw2199step0Labels = mixedMoment B raw2199step1 raw2199step1Labels := by
      have ha : raw2199step1 = raw2199step0 := by apply Matrix.ext; unfold raw2199step1 raw2199step0; decide +kernel
      have hl : raw2199step0Labels = labelEmbedding7 ∘ raw2199step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2199step0 raw2199step0Labels raw2199step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw2200 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2200 raw2200Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw2200 raw2200Labels = mixedMoment B raw2200step0 raw2200step0Labels := by
      have ha : raw2200step0 = (fun i j => raw2200 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2200step0 raw2200; decide +kernel
      have hl : raw2200step0Labels = raw2200Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2200 raw2200Labels permutation32 permutation4
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw2201 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2201Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2201step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2201step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2201 raw2201Labels = mixedMoment B node3607 node3607Labels := by
  calc
    mixedMoment B raw2201 raw2201Labels = mixedMoment B raw2201step0 raw2201step0Labels := by
      have ha : raw2201step0 = (fun i j => raw2201 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2201step0 raw2201; decide +kernel
      have hl : raw2201step0Labels = raw2201Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2201 raw2201Labels permutation32 permutation6
    mixedMoment B raw2201step0 raw2201step0Labels = mixedMoment B raw2201step1 raw2201step1Labels := by
      have ha : raw2201step1 = -raw2201step0 := by apply Matrix.ext; change ∀ i j, raw2201step1 i j = -(raw2201step0 i j); unfold raw2201step1 raw2201step0; decide +kernel
      have hl : raw2201step1Labels = raw2201step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2201step1 raw2201step1Labels = mixedMoment B raw2201step2 raw2201step2Labels := by
      have ha : raw2201step2 = raw2201step1 := by apply Matrix.ext; unfold raw2201step2 raw2201step1; decide +kernel
      have hl : raw2201step1Labels = labelEmbedding1 ∘ raw2201step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2201step1 raw2201step1Labels raw2201step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3607 node3607Labels := by rfl

def raw2202 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2202step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2202 raw2202Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw2202 raw2202Labels = mixedMoment B raw2202step0 raw2202step0Labels := by
      have ha : raw2202step0 = (fun i j => raw2202 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2202step0 raw2202; decide +kernel
      have hl : raw2202step0Labels = raw2202Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2202 raw2202Labels permutation32 permutation5
    mixedMoment B raw2202step0 raw2202step0Labels = mixedMoment B raw2202step1 raw2202step1Labels := by
      have ha : raw2202step1 = raw2202step0 := by apply Matrix.ext; unfold raw2202step1 raw2202step0; decide +kernel
      have hl : raw2202step0Labels = labelEmbedding8 ∘ raw2202step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2202step0 raw2202step0Labels raw2202step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw2203 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2203 raw2203Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw2203 raw2203Labels = mixedMoment B raw2203step0 raw2203step0Labels := by
      have ha : raw2203step0 = (fun i j => raw2203 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2203step0 raw2203; decide +kernel
      have hl : raw2203step0Labels = raw2203Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2203 raw2203Labels permutation34 permutation4
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw2204 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2204Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw2204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw2204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw2204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2204 raw2204Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw2204 raw2204Labels = mixedMoment B raw2204step0 raw2204step0Labels := by
      have ha : raw2204step0 = (fun i j => raw2204 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2204step0 raw2204; decide +kernel
      have hl : raw2204step0Labels = raw2204Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2204 raw2204Labels permutation33 permutation3
    mixedMoment B raw2204step0 raw2204step0Labels = mixedMoment B raw2204step1 raw2204step1Labels := by
      have ha : raw2204step1 = -raw2204step0 := by apply Matrix.ext; change ∀ i j, raw2204step1 i j = -(raw2204step0 i j); unfold raw2204step1 raw2204step0; decide +kernel
      have hl : raw2204step1Labels = raw2204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2204step1 raw2204step1Labels = mixedMoment B raw2204step2 raw2204step2Labels := by
      have ha : raw2204step2 = raw2204step1 := by apply Matrix.ext; unfold raw2204step2 raw2204step1; decide +kernel
      have hl : raw2204step1Labels = labelEmbedding1 ∘ raw2204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2204step1 raw2204step1Labels raw2204step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw2205 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 3, -2]]
def raw2205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2205step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2205step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2205step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2205 raw2205Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw2205 raw2205Labels = mixedMoment B raw2205step0 raw2205step0Labels := by
      have ha : raw2205step0 = (fun i j => raw2205 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2205step0 raw2205; decide +kernel
      have hl : raw2205step0Labels = raw2205Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2205 raw2205Labels permutation8 permutation4
    mixedMoment B raw2205step0 raw2205step0Labels = mixedMoment B raw2205step1 raw2205step1Labels := by
      have ha : raw2205step1 = raw2205step0 := by apply Matrix.ext; unfold raw2205step1 raw2205step0; decide +kernel
      have hl : raw2205step0Labels = labelEmbedding7 ∘ raw2205step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2205step0 raw2205step0Labels raw2205step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw2206 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 3, -2]]
def raw2206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2206step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2206 raw2206Labels = mixedMoment B node2598 node2598Labels := by
  calc
    mixedMoment B raw2206 raw2206Labels = mixedMoment B raw2206step0 raw2206step0Labels := by
      have ha : raw2206step0 = (fun i j => raw2206 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2206step0 raw2206; decide +kernel
      have hl : raw2206step0Labels = raw2206Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2206 raw2206Labels permutation8 permutation4
    _ = mixedMoment B node2598 node2598Labels := by rfl

def raw2207 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 3, -2]]
def raw2207Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2207step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]
def raw2207step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]
def raw2207step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2207 raw2207Labels = mixedMoment B node3608 node3608Labels := by
  calc
    mixedMoment B raw2207 raw2207Labels = mixedMoment B raw2207step0 raw2207step0Labels := by
      have ha : raw2207step0 = (fun i j => raw2207 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2207step0 raw2207; decide +kernel
      have hl : raw2207step0Labels = raw2207Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2207 raw2207Labels permutation31 permutation6
    mixedMoment B raw2207step0 raw2207step0Labels = mixedMoment B raw2207step1 raw2207step1Labels := by
      have ha : raw2207step1 = raw2207step0 := by apply Matrix.ext; unfold raw2207step1 raw2207step0; decide +kernel
      have hl : raw2207step0Labels = labelEmbedding1 ∘ raw2207step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2207step0 raw2207step0Labels raw2207step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3608 node3608Labels := by rfl

def raw2208 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2208step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2208 raw2208Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw2208 raw2208Labels = mixedMoment B raw2208step0 raw2208step0Labels := by
      have ha : raw2208step0 = (fun i j => raw2208 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2208step0 raw2208; decide +kernel
      have hl : raw2208step0Labels = raw2208Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2208 raw2208Labels permutation32 permutation4
    mixedMoment B raw2208step0 raw2208step0Labels = mixedMoment B raw2208step1 raw2208step1Labels := by
      have ha : raw2208step1 = raw2208step0 := by apply Matrix.ext; unfold raw2208step1 raw2208step0; decide +kernel
      have hl : raw2208step0Labels = labelEmbedding7 ∘ raw2208step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2208step0 raw2208step0Labels raw2208step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw2209 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2209 raw2209Labels = mixedMoment B node2599 node2599Labels := by
  calc
    mixedMoment B raw2209 raw2209Labels = mixedMoment B raw2209step0 raw2209step0Labels := by
      have ha : raw2209step0 = (fun i j => raw2209 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2209step0 raw2209; decide +kernel
      have hl : raw2209step0Labels = raw2209Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2209 raw2209Labels permutation32 permutation4
    _ = mixedMoment B node2599 node2599Labels := by rfl

def raw2210 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2210Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1]]
def raw2210step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw2210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw2210step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2210 raw2210Labels = mixedMoment B node3613 node3613Labels := by
  calc
    mixedMoment B raw2210 raw2210Labels = mixedMoment B raw2210step0 raw2210step0Labels := by
      have ha : raw2210step0 = (fun i j => raw2210 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2210step0 raw2210; decide +kernel
      have hl : raw2210step0Labels = raw2210Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2210 raw2210Labels permutation36 permutation6
    mixedMoment B raw2210step0 raw2210step0Labels = mixedMoment B raw2210step1 raw2210step1Labels := by
      have ha : raw2210step1 = -raw2210step0 := by apply Matrix.ext; change ∀ i j, raw2210step1 i j = -(raw2210step0 i j); unfold raw2210step1 raw2210step0; decide +kernel
      have hl : raw2210step1Labels = raw2210step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2210step1 raw2210step1Labels = mixedMoment B raw2210step2 raw2210step2Labels := by
      have ha : raw2210step2 = raw2210step1 := by apply Matrix.ext; unfold raw2210step2 raw2210step1; decide +kernel
      have hl : raw2210step1Labels = labelEmbedding1 ∘ raw2210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2210step1 raw2210step1Labels raw2210step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3613 node3613Labels := by rfl

def raw2211 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-2, 3, -1]]
def raw2211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2211step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw2211step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw2211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2211 raw2211Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw2211 raw2211Labels = mixedMoment B raw2211step0 raw2211step0Labels := by
      have ha : raw2211step0 = (fun i j => raw2211 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2211step0 raw2211; decide +kernel
      have hl : raw2211step0Labels = raw2211Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2211 raw2211Labels permutation8 permutation4
    mixedMoment B raw2211step0 raw2211step0Labels = mixedMoment B raw2211step1 raw2211step1Labels := by
      have ha : raw2211step1 = raw2211step0 := by apply Matrix.ext; unfold raw2211step1 raw2211step0; decide +kernel
      have hl : raw2211step0Labels = labelEmbedding7 ∘ raw2211step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2211step0 raw2211step0Labels raw2211step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5174 node5174Labels := by rfl

def raw2212 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-2, 3, -1]]
def raw2212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2212step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw2212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2212 raw2212Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw2212 raw2212Labels = mixedMoment B raw2212step0 raw2212step0Labels := by
      have ha : raw2212step0 = (fun i j => raw2212 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2212step0 raw2212; decide +kernel
      have hl : raw2212step0Labels = raw2212Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2212 raw2212Labels permutation8 permutation4
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw2213 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-2, 3, -1]]
def raw2213Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2213step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]
def raw2213step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]
def raw2213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2213 raw2213Labels = mixedMoment B node3615 node3615Labels := by
  calc
    mixedMoment B raw2213 raw2213Labels = mixedMoment B raw2213step0 raw2213step0Labels := by
      have ha : raw2213step0 = (fun i j => raw2213 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2213step0 raw2213; decide +kernel
      have hl : raw2213step0Labels = raw2213Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2213 raw2213Labels permutation31 permutation3
    mixedMoment B raw2213step0 raw2213step0Labels = mixedMoment B raw2213step1 raw2213step1Labels := by
      have ha : raw2213step1 = raw2213step0 := by apply Matrix.ext; unfold raw2213step1 raw2213step0; decide +kernel
      have hl : raw2213step0Labels = labelEmbedding1 ∘ raw2213step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2213step0 raw2213step0Labels raw2213step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3615 node3615Labels := by rfl

def raw2214 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2214step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2214step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2214 raw2214Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw2214 raw2214Labels = mixedMoment B raw2214step0 raw2214step0Labels := by
      have ha : raw2214step0 = (fun i j => raw2214 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2214step0 raw2214; decide +kernel
      have hl : raw2214step0Labels = raw2214Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2214 raw2214Labels permutation8 permutation4
    mixedMoment B raw2214step0 raw2214step0Labels = mixedMoment B raw2214step1 raw2214step1Labels := by
      have ha : raw2214step1 = raw2214step0 := by apply Matrix.ext; unfold raw2214step1 raw2214step0; decide +kernel
      have hl : raw2214step0Labels = labelEmbedding7 ∘ raw2214step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2214step0 raw2214step0Labels raw2214step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw2215 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2215step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2215 raw2215Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw2215 raw2215Labels = mixedMoment B raw2215step0 raw2215step0Labels := by
      have ha : raw2215step0 = (fun i j => raw2215 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2215step0 raw2215; decide +kernel
      have hl : raw2215step0Labels = raw2215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2215 raw2215Labels permutation8 permutation4
    _ = mixedMoment B node2604 node2604Labels := by rfl

def raw2216 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2216Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2216step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw2216step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]
def raw2216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2216step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]
def raw2216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2216 raw2216Labels = mixedMoment B node3614 node3614Labels := by
  calc
    mixedMoment B raw2216 raw2216Labels = mixedMoment B raw2216step0 raw2216step0Labels := by
      have ha : raw2216step0 = (fun i j => raw2216 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2216step0 raw2216; decide +kernel
      have hl : raw2216step0Labels = raw2216Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2216 raw2216Labels permutation8 permutation6
    mixedMoment B raw2216step0 raw2216step0Labels = mixedMoment B raw2216step1 raw2216step1Labels := by
      have ha : raw2216step1 = -raw2216step0 := by apply Matrix.ext; change ∀ i j, raw2216step1 i j = -(raw2216step0 i j); unfold raw2216step1 raw2216step0; decide +kernel
      have hl : raw2216step1Labels = raw2216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2216step1 raw2216step1Labels = mixedMoment B raw2216step2 raw2216step2Labels := by
      have ha : raw2216step2 = raw2216step1 := by apply Matrix.ext; unfold raw2216step2 raw2216step1; decide +kernel
      have hl : raw2216step1Labels = labelEmbedding1 ∘ raw2216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2216step1 raw2216step1Labels raw2216step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3614 node3614Labels := by rfl

def raw2217 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2217step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2217step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2217 raw2217Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw2217 raw2217Labels = mixedMoment B raw2217step0 raw2217step0Labels := by
      have ha : raw2217step0 = (fun i j => raw2217 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2217step0 raw2217; decide +kernel
      have hl : raw2217step0Labels = raw2217Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2217 raw2217Labels permutation8 permutation4
    mixedMoment B raw2217step0 raw2217step0Labels = mixedMoment B raw2217step1 raw2217step1Labels := by
      have ha : raw2217step1 = raw2217step0 := by apply Matrix.ext; unfold raw2217step1 raw2217step0; decide +kernel
      have hl : raw2217step0Labels = labelEmbedding7 ∘ raw2217step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2217step0 raw2217step0Labels raw2217step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw2218 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2218step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2218 raw2218Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw2218 raw2218Labels = mixedMoment B raw2218step0 raw2218step0Labels := by
      have ha : raw2218step0 = (fun i j => raw2218 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2218step0 raw2218; decide +kernel
      have hl : raw2218step0Labels = raw2218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2218 raw2218Labels permutation8 permutation4
    _ = mixedMoment B node2605 node2605Labels := by rfl

def raw2219 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2219Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2219step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2219step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2219step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2219step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2219 raw2219Labels = mixedMoment B node3616 node3616Labels := by
  calc
    mixedMoment B raw2219 raw2219Labels = mixedMoment B raw2219step0 raw2219step0Labels := by
      have ha : raw2219step0 = (fun i j => raw2219 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2219step0 raw2219; decide +kernel
      have hl : raw2219step0Labels = raw2219Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2219 raw2219Labels permutation8 permutation6
    mixedMoment B raw2219step0 raw2219step0Labels = mixedMoment B raw2219step1 raw2219step1Labels := by
      have ha : raw2219step1 = -raw2219step0 := by apply Matrix.ext; change ∀ i j, raw2219step1 i j = -(raw2219step0 i j); unfold raw2219step1 raw2219step0; decide +kernel
      have hl : raw2219step1Labels = raw2219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2219step1 raw2219step1Labels = mixedMoment B raw2219step2 raw2219step2Labels := by
      have ha : raw2219step2 = raw2219step1 := by apply Matrix.ext; unfold raw2219step2 raw2219step1; decide +kernel
      have hl : raw2219step1Labels = labelEmbedding1 ∘ raw2219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2219step1 raw2219step1Labels raw2219step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3616 node3616Labels := by rfl

def raw2220 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2220step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2220step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2220 raw2220Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw2220 raw2220Labels = mixedMoment B raw2220step0 raw2220step0Labels := by
      have ha : raw2220step0 = (fun i j => raw2220 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2220step0 raw2220; decide +kernel
      have hl : raw2220step0Labels = raw2220Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2220 raw2220Labels permutation152 permutation5
    mixedMoment B raw2220step0 raw2220step0Labels = mixedMoment B raw2220step1 raw2220step1Labels := by
      have ha : raw2220step1 = raw2220step0 := by apply Matrix.ext; unfold raw2220step1 raw2220step0; decide +kernel
      have hl : raw2220step0Labels = labelEmbedding8 ∘ raw2220step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2220step0 raw2220step0Labels raw2220step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw2221 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2221 raw2221Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw2221 raw2221Labels = mixedMoment B raw2221step0 raw2221step0Labels := by
      have ha : raw2221step0 = (fun i j => raw2221 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2221step0 raw2221; decide +kernel
      have hl : raw2221step0Labels = raw2221Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2221 raw2221Labels permutation152 permutation4
    _ = mixedMoment B node2853 node2853Labels := by rfl

def raw2222 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2222Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0]]
def raw2222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw2222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2222step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw2222step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2222 raw2222Labels = mixedMoment B node3620 node3620Labels := by
  calc
    mixedMoment B raw2222 raw2222Labels = mixedMoment B raw2222step0 raw2222step0Labels := by
      have ha : raw2222step0 = (fun i j => raw2222 (permutation216 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2222step0 raw2222; decide +kernel
      have hl : raw2222step0Labels = raw2222Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2222 raw2222Labels permutation216 permutation3
    mixedMoment B raw2222step0 raw2222step0Labels = mixedMoment B raw2222step1 raw2222step1Labels := by
      have ha : raw2222step1 = -raw2222step0 := by apply Matrix.ext; change ∀ i j, raw2222step1 i j = -(raw2222step0 i j); unfold raw2222step1 raw2222step0; decide +kernel
      have hl : raw2222step1Labels = raw2222step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2222step1 raw2222step1Labels = mixedMoment B raw2222step2 raw2222step2Labels := by
      have ha : raw2222step2 = raw2222step1 := by apply Matrix.ext; unfold raw2222step2 raw2222step1; decide +kernel
      have hl : raw2222step1Labels = labelEmbedding1 ∘ raw2222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2222step1 raw2222step1Labels raw2222step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3620 node3620Labels := by rfl

def raw2223 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw2223step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw2223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2223 raw2223Labels = mixedMoment B node5193 node5193Labels := by
  calc
    mixedMoment B raw2223 raw2223Labels = mixedMoment B raw2223step0 raw2223step0Labels := by
      have ha : raw2223step0 = (fun i j => raw2223 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2223step0 raw2223; decide +kernel
      have hl : raw2223step0Labels = raw2223Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2223 raw2223Labels permutation32 permutation5
    mixedMoment B raw2223step0 raw2223step0Labels = mixedMoment B raw2223step1 raw2223step1Labels := by
      have ha : raw2223step1 = raw2223step0 := by apply Matrix.ext; unfold raw2223step1 raw2223step0; decide +kernel
      have hl : raw2223step0Labels = labelEmbedding8 ∘ raw2223step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2223step0 raw2223step0Labels raw2223step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5193 node5193Labels := by rfl

def raw2224 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2224 raw2224Labels = mixedMoment B node2856 node2856Labels := by
  calc
    mixedMoment B raw2224 raw2224Labels = mixedMoment B raw2224step0 raw2224step0Labels := by
      have ha : raw2224step0 = (fun i j => raw2224 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2224step0 raw2224; decide +kernel
      have hl : raw2224step0Labels = raw2224Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2224 raw2224Labels permutation32 permutation4
    _ = mixedMoment B node2856 node2856Labels := by rfl

def raw2225 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2225Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0]]
def raw2225step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw2225step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2225step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw2225step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2225 raw2225Labels = mixedMoment B node3630 node3630Labels := by
  calc
    mixedMoment B raw2225 raw2225Labels = mixedMoment B raw2225step0 raw2225step0Labels := by
      have ha : raw2225step0 = (fun i j => raw2225 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2225step0 raw2225; decide +kernel
      have hl : raw2225step0Labels = raw2225Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2225 raw2225Labels permutation48 permutation3
    mixedMoment B raw2225step0 raw2225step0Labels = mixedMoment B raw2225step1 raw2225step1Labels := by
      have ha : raw2225step1 = -raw2225step0 := by apply Matrix.ext; change ∀ i j, raw2225step1 i j = -(raw2225step0 i j); unfold raw2225step1 raw2225step0; decide +kernel
      have hl : raw2225step1Labels = raw2225step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2225step1 raw2225step1Labels = mixedMoment B raw2225step2 raw2225step2Labels := by
      have ha : raw2225step2 = raw2225step1 := by apply Matrix.ext; unfold raw2225step2 raw2225step1; decide +kernel
      have hl : raw2225step1Labels = labelEmbedding1 ∘ raw2225step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2225step1 raw2225step1Labels raw2225step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3630 node3630Labels := by rfl

def raw2226 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw2226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2226step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2226 raw2226Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw2226 raw2226Labels = mixedMoment B raw2226step0 raw2226step0Labels := by
      have ha : raw2226step0 = (fun i j => raw2226 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2226step0 raw2226; decide +kernel
      have hl : raw2226step0Labels = raw2226Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2226 raw2226Labels permutation152 permutation5
    mixedMoment B raw2226step0 raw2226step0Labels = mixedMoment B raw2226step1 raw2226step1Labels := by
      have ha : raw2226step1 = raw2226step0 := by apply Matrix.ext; unfold raw2226step1 raw2226step0; decide +kernel
      have hl : raw2226step0Labels = labelEmbedding8 ∘ raw2226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2226step0 raw2226step0Labels raw2226step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw2227 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw2227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2227 raw2227Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw2227 raw2227Labels = mixedMoment B raw2227step0 raw2227step0Labels := by
      have ha : raw2227step0 = (fun i j => raw2227 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2227step0 raw2227; decide +kernel
      have hl : raw2227step0Labels = raw2227Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2227 raw2227Labels permutation170 permutation4
    _ = mixedMoment B node2880 node2880Labels := by rfl

def raw2228 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw2228Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw2228step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2228step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2228step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2228step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2228 raw2228Labels = mixedMoment B node3617 node3617Labels := by
  calc
    mixedMoment B raw2228 raw2228Labels = mixedMoment B raw2228step0 raw2228step0Labels := by
      have ha : raw2228step0 = (fun i j => raw2228 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2228step0 raw2228; decide +kernel
      have hl : raw2228step0Labels = raw2228Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2228 raw2228Labels permutation184 permutation3
    mixedMoment B raw2228step0 raw2228step0Labels = mixedMoment B raw2228step1 raw2228step1Labels := by
      have ha : raw2228step1 = -raw2228step0 := by apply Matrix.ext; change ∀ i j, raw2228step1 i j = -(raw2228step0 i j); unfold raw2228step1 raw2228step0; decide +kernel
      have hl : raw2228step1Labels = raw2228step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2228step1 raw2228step1Labels = mixedMoment B raw2228step2 raw2228step2Labels := by
      have ha : raw2228step2 = raw2228step1 := by apply Matrix.ext; unfold raw2228step2 raw2228step1; decide +kernel
      have hl : raw2228step1Labels = labelEmbedding1 ∘ raw2228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2228step1 raw2228step1Labels raw2228step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3617 node3617Labels := by rfl

def raw2229 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2229step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2229 raw2229Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw2229 raw2229Labels = mixedMoment B raw2229step0 raw2229step0Labels := by
      have ha : raw2229step0 = (fun i j => raw2229 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2229step0 raw2229; decide +kernel
      have hl : raw2229step0Labels = raw2229Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2229 raw2229Labels permutation32 permutation5
    mixedMoment B raw2229step0 raw2229step0Labels = mixedMoment B raw2229step1 raw2229step1Labels := by
      have ha : raw2229step1 = raw2229step0 := by apply Matrix.ext; unfold raw2229step1 raw2229step0; decide +kernel
      have hl : raw2229step0Labels = labelEmbedding8 ∘ raw2229step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2229step0 raw2229step0Labels raw2229step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw2230 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2230 raw2230Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw2230 raw2230Labels = mixedMoment B raw2230step0 raw2230step0Labels := by
      have ha : raw2230step0 = (fun i j => raw2230 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2230step0 raw2230; decide +kernel
      have hl : raw2230step0Labels = raw2230Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2230 raw2230Labels permutation32 permutation4
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw2231 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2231Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw2231step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2231step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2231step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2231 raw2231Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw2231 raw2231Labels = mixedMoment B raw2231step0 raw2231step0Labels := by
      have ha : raw2231step0 = (fun i j => raw2231 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2231step0 raw2231; decide +kernel
      have hl : raw2231step0Labels = raw2231Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2231 raw2231Labels permutation40 permutation3
    mixedMoment B raw2231step0 raw2231step0Labels = mixedMoment B raw2231step1 raw2231step1Labels := by
      have ha : raw2231step1 = -raw2231step0 := by apply Matrix.ext; change ∀ i j, raw2231step1 i j = -(raw2231step0 i j); unfold raw2231step1 raw2231step0; decide +kernel
      have hl : raw2231step1Labels = raw2231step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2231step1 raw2231step1Labels = mixedMoment B raw2231step2 raw2231step2Labels := by
      have ha : raw2231step2 = raw2231step1 := by apply Matrix.ext; unfold raw2231step2 raw2231step1; decide +kernel
      have hl : raw2231step1Labels = labelEmbedding1 ∘ raw2231step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2231step1 raw2231step1Labels raw2231step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

def raw2232 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw2232step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw2232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2232 raw2232Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw2232 raw2232Labels = mixedMoment B raw2232step0 raw2232step0Labels := by
      have ha : raw2232step0 = (fun i j => raw2232 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2232step0 raw2232; decide +kernel
      have hl : raw2232step0Labels = raw2232Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2232 raw2232Labels permutation32 permutation5
    mixedMoment B raw2232step0 raw2232step0Labels = mixedMoment B raw2232step1 raw2232step1Labels := by
      have ha : raw2232step1 = raw2232step0 := by apply Matrix.ext; unfold raw2232step1 raw2232step0; decide +kernel
      have hl : raw2232step0Labels = labelEmbedding8 ∘ raw2232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2232step0 raw2232step0Labels raw2232step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw2233 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2233 raw2233Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw2233 raw2233Labels = mixedMoment B raw2233step0 raw2233step0Labels := by
      have ha : raw2233step0 = (fun i j => raw2233 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2233step0 raw2233; decide +kernel
      have hl : raw2233step0Labels = raw2233Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2233 raw2233Labels permutation34 permutation4
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw2234 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2234Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw2234step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw2234step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw2234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2234 raw2234Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw2234 raw2234Labels = mixedMoment B raw2234step0 raw2234step0Labels := by
      have ha : raw2234step0 = (fun i j => raw2234 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2234step0 raw2234; decide +kernel
      have hl : raw2234step0Labels = raw2234Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2234 raw2234Labels permutation42 permutation3
    mixedMoment B raw2234step0 raw2234step0Labels = mixedMoment B raw2234step1 raw2234step1Labels := by
      have ha : raw2234step1 = -raw2234step0 := by apply Matrix.ext; change ∀ i j, raw2234step1 i j = -(raw2234step0 i j); unfold raw2234step1 raw2234step0; decide +kernel
      have hl : raw2234step1Labels = raw2234step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2234step1 raw2234step1Labels = mixedMoment B raw2234step2 raw2234step2Labels := by
      have ha : raw2234step2 = raw2234step1 := by apply Matrix.ext; unfold raw2234step2 raw2234step1; decide +kernel
      have hl : raw2234step1Labels = labelEmbedding1 ∘ raw2234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2234step1 raw2234step1Labels raw2234step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw2235 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw2235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2235step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2235step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2235 raw2235Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw2235 raw2235Labels = mixedMoment B raw2235step0 raw2235step0Labels := by
      have ha : raw2235step0 = (fun i j => raw2235 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2235step0 raw2235; decide +kernel
      have hl : raw2235step0Labels = raw2235Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2235 raw2235Labels permutation8 permutation5
    mixedMoment B raw2235step0 raw2235step0Labels = mixedMoment B raw2235step1 raw2235step1Labels := by
      have ha : raw2235step1 = raw2235step0 := by apply Matrix.ext; unfold raw2235step1 raw2235step0; decide +kernel
      have hl : raw2235step0Labels = labelEmbedding8 ∘ raw2235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2235step0 raw2235step0Labels raw2235step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw2236 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw2236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2236step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw2236step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2236 raw2236Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw2236 raw2236Labels = mixedMoment B raw2236step0 raw2236step0Labels := by
      have ha : raw2236step0 = (fun i j => raw2236 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2236step0 raw2236; decide +kernel
      have hl : raw2236step0Labels = raw2236Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2236 raw2236Labels permutation9 permutation4
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw2237 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw2237Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2237step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw2237step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw2237step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2237step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw2237step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2237 raw2237Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw2237 raw2237Labels = mixedMoment B raw2237step0 raw2237step0Labels := by
      have ha : raw2237step0 = (fun i j => raw2237 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2237step0 raw2237; decide +kernel
      have hl : raw2237step0Labels = raw2237Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2237 raw2237Labels permutation10 permutation3
    mixedMoment B raw2237step0 raw2237step0Labels = mixedMoment B raw2237step1 raw2237step1Labels := by
      have ha : raw2237step1 = -raw2237step0 := by apply Matrix.ext; change ∀ i j, raw2237step1 i j = -(raw2237step0 i j); unfold raw2237step1 raw2237step0; decide +kernel
      have hl : raw2237step1Labels = raw2237step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2237step1 raw2237step1Labels = mixedMoment B raw2237step2 raw2237step2Labels := by
      have ha : raw2237step2 = raw2237step1 := by apply Matrix.ext; unfold raw2237step2 raw2237step1; decide +kernel
      have hl : raw2237step1Labels = labelEmbedding1 ∘ raw2237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2237step1 raw2237step1Labels raw2237step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

def raw2238 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2238step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2238 raw2238Labels = mixedMoment B node5212 node5212Labels := by
  calc
    mixedMoment B raw2238 raw2238Labels = mixedMoment B raw2238step0 raw2238step0Labels := by
      have ha : raw2238step0 = (fun i j => raw2238 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2238step0 raw2238; decide +kernel
      have hl : raw2238step0Labels = raw2238Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2238 raw2238Labels permutation152 permutation5
    mixedMoment B raw2238step0 raw2238step0Labels = mixedMoment B raw2238step1 raw2238step1Labels := by
      have ha : raw2238step1 = raw2238step0 := by apply Matrix.ext; unfold raw2238step1 raw2238step0; decide +kernel
      have hl : raw2238step0Labels = labelEmbedding8 ∘ raw2238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2238step0 raw2238step0Labels raw2238step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5212 node5212Labels := by rfl

def raw2239 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2239Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2239 raw2239Labels = mixedMoment B node2839 node2839Labels := by
  calc
    mixedMoment B raw2239 raw2239Labels = mixedMoment B raw2239step0 raw2239step0Labels := by
      have ha : raw2239step0 = (fun i j => raw2239 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2239step0 raw2239; decide +kernel
      have hl : raw2239step0Labels = raw2239Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2239 raw2239Labels permutation152 permutation4
    _ = mixedMoment B node2839 node2839Labels := by rfl

def raw2240 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2240Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2240step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2240step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2240step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2240step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2240 raw2240Labels = mixedMoment B node2839 node2839Labels := by
  calc
    mixedMoment B raw2240 raw2240Labels = mixedMoment B raw2240step0 raw2240step0Labels := by
      have ha : raw2240step0 = (fun i j => raw2240 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2240step0 raw2240; decide +kernel
      have hl : raw2240step0Labels = raw2240Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2240 raw2240Labels permutation265 permutation6
    mixedMoment B raw2240step0 raw2240step0Labels = mixedMoment B raw2240step1 raw2240step1Labels := by
      have ha : raw2240step1 = -raw2240step0 := by apply Matrix.ext; change ∀ i j, raw2240step1 i j = -(raw2240step0 i j); unfold raw2240step1 raw2240step0; decide +kernel
      have hl : raw2240step1Labels = raw2240step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2240step1 raw2240step1Labels = mixedMoment B raw2240step2 raw2240step2Labels := by
      have ha : raw2240step2 = raw2240step1 := by apply Matrix.ext; unfold raw2240step2 raw2240step1; decide +kernel
      have hl : raw2240step1Labels = labelEmbedding1 ∘ raw2240step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2240step1 raw2240step1Labels raw2240step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2839 node2839Labels := by rfl

def raw2241 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2241step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2241 raw2241Labels = mixedMoment B node5213 node5213Labels := by
  calc
    mixedMoment B raw2241 raw2241Labels = mixedMoment B raw2241step0 raw2241step0Labels := by
      have ha : raw2241step0 = (fun i j => raw2241 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2241step0 raw2241; decide +kernel
      have hl : raw2241step0Labels = raw2241Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2241 raw2241Labels permutation32 permutation5
    mixedMoment B raw2241step0 raw2241step0Labels = mixedMoment B raw2241step1 raw2241step1Labels := by
      have ha : raw2241step1 = raw2241step0 := by apply Matrix.ext; unfold raw2241step1 raw2241step0; decide +kernel
      have hl : raw2241step0Labels = labelEmbedding8 ∘ raw2241step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2241step0 raw2241step0Labels raw2241step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5213 node5213Labels := by rfl

def raw2242 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2242Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2242step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2242 raw2242Labels = mixedMoment B node2840 node2840Labels := by
  calc
    mixedMoment B raw2242 raw2242Labels = mixedMoment B raw2242step0 raw2242step0Labels := by
      have ha : raw2242step0 = (fun i j => raw2242 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2242step0 raw2242; decide +kernel
      have hl : raw2242step0Labels = raw2242Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2242 raw2242Labels permutation32 permutation4
    _ = mixedMoment B node2840 node2840Labels := by rfl

def raw2243 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2243Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw2243step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2243step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2243step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2243 raw2243Labels = mixedMoment B node2840 node2840Labels := by
  calc
    mixedMoment B raw2243 raw2243Labels = mixedMoment B raw2243step0 raw2243step0Labels := by
      have ha : raw2243step0 = (fun i j => raw2243 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2243step0 raw2243; decide +kernel
      have hl : raw2243step0Labels = raw2243Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2243 raw2243Labels permutation56 permutation6
    mixedMoment B raw2243step0 raw2243step0Labels = mixedMoment B raw2243step1 raw2243step1Labels := by
      have ha : raw2243step1 = -raw2243step0 := by apply Matrix.ext; change ∀ i j, raw2243step1 i j = -(raw2243step0 i j); unfold raw2243step1 raw2243step0; decide +kernel
      have hl : raw2243step1Labels = raw2243step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2243step1 raw2243step1Labels = mixedMoment B raw2243step2 raw2243step2Labels := by
      have ha : raw2243step2 = raw2243step1 := by apply Matrix.ext; unfold raw2243step2 raw2243step1; decide +kernel
      have hl : raw2243step1Labels = labelEmbedding1 ∘ raw2243step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2243step1 raw2243step1Labels raw2243step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2840 node2840Labels := by rfl

def raw2244 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, -1, 3], ![0, 2, -2], ![0, 2, -2]]
def raw2244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2244step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw2244step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw2244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2244 raw2244Labels = mixedMoment B node5214 node5214Labels := by
  calc
    mixedMoment B raw2244 raw2244Labels = mixedMoment B raw2244step0 raw2244step0Labels := by
      have ha : raw2244step0 = (fun i j => raw2244 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2244step0 raw2244; decide +kernel
      have hl : raw2244step0Labels = raw2244Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2244 raw2244Labels permutation8 permutation5
    mixedMoment B raw2244step0 raw2244step0Labels = mixedMoment B raw2244step1 raw2244step1Labels := by
      have ha : raw2244step1 = raw2244step0 := by apply Matrix.ext; unfold raw2244step1 raw2244step0; decide +kernel
      have hl : raw2244step0Labels = labelEmbedding8 ∘ raw2244step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2244step0 raw2244step0Labels raw2244step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5214 node5214Labels := by rfl

def raw2245 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, -1, 3], ![0, 2, -2], ![0, 2, -2]]
def raw2245Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2245step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, 0, -2], ![2, 0, -2]]
def raw2245step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2245 raw2245Labels = mixedMoment B node2843 node2843Labels := by
  calc
    mixedMoment B raw2245 raw2245Labels = mixedMoment B raw2245step0 raw2245step0Labels := by
      have ha : raw2245step0 = (fun i j => raw2245 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2245step0 raw2245; decide +kernel
      have hl : raw2245step0Labels = raw2245Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2245 raw2245Labels permutation8 permutation4
    _ = mixedMoment B node2843 node2843Labels := by rfl

def raw2246 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, -1, 3], ![0, 2, -2], ![0, 2, -2]]
def raw2246Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2246step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-2, 0, 2], ![-2, 0, 2]]
def raw2246step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, 0, -2], ![2, 0, -2]]
def raw2246step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, 0, -2], ![2, 0, -2]]
def raw2246step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2246 raw2246Labels = mixedMoment B node2843 node2843Labels := by
  calc
    mixedMoment B raw2246 raw2246Labels = mixedMoment B raw2246step0 raw2246step0Labels := by
      have ha : raw2246step0 = (fun i j => raw2246 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2246step0 raw2246; decide +kernel
      have hl : raw2246step0Labels = raw2246Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2246 raw2246Labels permutation14 permutation6
    mixedMoment B raw2246step0 raw2246step0Labels = mixedMoment B raw2246step1 raw2246step1Labels := by
      have ha : raw2246step1 = -raw2246step0 := by apply Matrix.ext; change ∀ i j, raw2246step1 i j = -(raw2246step0 i j); unfold raw2246step1 raw2246step0; decide +kernel
      have hl : raw2246step1Labels = raw2246step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2246step1 raw2246step1Labels = mixedMoment B raw2246step2 raw2246step2Labels := by
      have ha : raw2246step2 = raw2246step1 := by apply Matrix.ext; unfold raw2246step2 raw2246step1; decide +kernel
      have hl : raw2246step1Labels = labelEmbedding1 ∘ raw2246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2246step1 raw2246step1Labels raw2246step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2843 node2843Labels := by rfl

def raw2247 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2247step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2247 raw2247Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw2247 raw2247Labels = mixedMoment B raw2247step0 raw2247step0Labels := by
      have ha : raw2247step0 = (fun i j => raw2247 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2247step0 raw2247; decide +kernel
      have hl : raw2247step0Labels = raw2247Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2247 raw2247Labels permutation152 permutation4
    mixedMoment B raw2247step0 raw2247step0Labels = mixedMoment B raw2247step1 raw2247step1Labels := by
      have ha : raw2247step1 = raw2247step0 := by apply Matrix.ext; unfold raw2247step1 raw2247step0; decide +kernel
      have hl : raw2247step0Labels = labelEmbedding7 ∘ raw2247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2247step0 raw2247step0Labels raw2247step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

def raw2248 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2248Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2248 raw2248Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw2248 raw2248Labels = mixedMoment B raw2248step0 raw2248step0Labels := by
      have ha : raw2248step0 = (fun i j => raw2248 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2248step0 raw2248; decide +kernel
      have hl : raw2248step0Labels = raw2248Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2248 raw2248Labels permutation152 permutation4
    _ = mixedMoment B node2671 node2671Labels := by rfl

def raw2249 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2249Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2249step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2249step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2249 raw2249Labels = mixedMoment B node3390 node3390Labels := by
  calc
    mixedMoment B raw2249 raw2249Labels = mixedMoment B raw2249step0 raw2249step0Labels := by
      have ha : raw2249step0 = (fun i j => raw2249 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2249step0 raw2249; decide +kernel
      have hl : raw2249step0Labels = raw2249Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2249 raw2249Labels permutation152 permutation6
    mixedMoment B raw2249step0 raw2249step0Labels = mixedMoment B raw2249step1 raw2249step1Labels := by
      have ha : raw2249step1 = -raw2249step0 := by apply Matrix.ext; change ∀ i j, raw2249step1 i j = -(raw2249step0 i j); unfold raw2249step1 raw2249step0; decide +kernel
      have hl : raw2249step1Labels = raw2249step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2249step1 raw2249step1Labels = mixedMoment B raw2249step2 raw2249step2Labels := by
      have ha : raw2249step2 = raw2249step1 := by apply Matrix.ext; unfold raw2249step2 raw2249step1; decide +kernel
      have hl : raw2249step1Labels = labelEmbedding1 ∘ raw2249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2249step1 raw2249step1Labels raw2249step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3390 node3390Labels := by rfl

def raw2250 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2250step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2250 raw2250Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw2250 raw2250Labels = mixedMoment B raw2250step0 raw2250step0Labels := by
      have ha : raw2250step0 = (fun i j => raw2250 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2250step0 raw2250; decide +kernel
      have hl : raw2250step0Labels = raw2250Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2250 raw2250Labels permutation32 permutation4
    mixedMoment B raw2250step0 raw2250step0Labels = mixedMoment B raw2250step1 raw2250step1Labels := by
      have ha : raw2250step1 = raw2250step0 := by apply Matrix.ext; unfold raw2250step1 raw2250step0; decide +kernel
      have hl : raw2250step0Labels = labelEmbedding7 ∘ raw2250step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2250step0 raw2250step0Labels raw2250step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw2251 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2251Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2251 raw2251Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw2251 raw2251Labels = mixedMoment B raw2251step0 raw2251step0Labels := by
      have ha : raw2251step0 = (fun i j => raw2251 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2251step0 raw2251; decide +kernel
      have hl : raw2251step0Labels = raw2251Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2251 raw2251Labels permutation32 permutation4
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw2252 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2252Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw2252step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2252step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2252step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2252 raw2252Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw2252 raw2252Labels = mixedMoment B raw2252step0 raw2252step0Labels := by
      have ha : raw2252step0 = (fun i j => raw2252 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2252step0 raw2252; decide +kernel
      have hl : raw2252step0Labels = raw2252Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2252 raw2252Labels permutation32 permutation6
    mixedMoment B raw2252step0 raw2252step0Labels = mixedMoment B raw2252step1 raw2252step1Labels := by
      have ha : raw2252step1 = -raw2252step0 := by apply Matrix.ext; change ∀ i j, raw2252step1 i j = -(raw2252step0 i j); unfold raw2252step1 raw2252step0; decide +kernel
      have hl : raw2252step1Labels = raw2252step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2252step1 raw2252step1Labels = mixedMoment B raw2252step2 raw2252step2Labels := by
      have ha : raw2252step2 = raw2252step1 := by apply Matrix.ext; unfold raw2252step2 raw2252step1; decide +kernel
      have hl : raw2252step1Labels = labelEmbedding1 ∘ raw2252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2252step1 raw2252step1Labels raw2252step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw2253 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2253step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2253 raw2253Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw2253 raw2253Labels = mixedMoment B raw2253step0 raw2253step0Labels := by
      have ha : raw2253step0 = (fun i j => raw2253 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2253step0 raw2253; decide +kernel
      have hl : raw2253step0Labels = raw2253Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2253 raw2253Labels permutation32 permutation4
    mixedMoment B raw2253step0 raw2253step0Labels = mixedMoment B raw2253step1 raw2253step1Labels := by
      have ha : raw2253step1 = raw2253step0 := by apply Matrix.ext; unfold raw2253step1 raw2253step0; decide +kernel
      have hl : raw2253step0Labels = labelEmbedding7 ∘ raw2253step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2253step0 raw2253step0Labels raw2253step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw2254 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2254Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2254step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2254 raw2254Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw2254 raw2254Labels = mixedMoment B raw2254step0 raw2254step0Labels := by
      have ha : raw2254step0 = (fun i j => raw2254 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2254step0 raw2254; decide +kernel
      have hl : raw2254step0Labels = raw2254Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2254 raw2254Labels permutation32 permutation4
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw2255 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2255Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2255step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2255step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2255 raw2255Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw2255 raw2255Labels = mixedMoment B raw2255step0 raw2255step0Labels := by
      have ha : raw2255step0 = (fun i j => raw2255 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2255step0 raw2255; decide +kernel
      have hl : raw2255step0Labels = raw2255Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2255 raw2255Labels permutation32 permutation6
    mixedMoment B raw2255step0 raw2255step0Labels = mixedMoment B raw2255step1 raw2255step1Labels := by
      have ha : raw2255step1 = -raw2255step0 := by apply Matrix.ext; change ∀ i j, raw2255step1 i j = -(raw2255step0 i j); unfold raw2255step1 raw2255step0; decide +kernel
      have hl : raw2255step1Labels = raw2255step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2255step1 raw2255step1Labels = mixedMoment B raw2255step2 raw2255step2Labels := by
      have ha : raw2255step2 = raw2255step1 := by apply Matrix.ext; unfold raw2255step2 raw2255step1; decide +kernel
      have hl : raw2255step1Labels = labelEmbedding1 ∘ raw2255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2255step1 raw2255step1Labels raw2255step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3394 node3394Labels := by rfl

def raw2256 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 2, -2]]
def raw2256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2256step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw2256step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw2256step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2256 raw2256Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw2256 raw2256Labels = mixedMoment B raw2256step0 raw2256step0Labels := by
      have ha : raw2256step0 = (fun i j => raw2256 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2256step0 raw2256; decide +kernel
      have hl : raw2256step0Labels = raw2256Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2256 raw2256Labels permutation8 permutation4
    mixedMoment B raw2256step0 raw2256step0Labels = mixedMoment B raw2256step1 raw2256step1Labels := by
      have ha : raw2256step1 = raw2256step0 := by apply Matrix.ext; unfold raw2256step1 raw2256step0; decide +kernel
      have hl : raw2256step0Labels = labelEmbedding7 ∘ raw2256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2256step0 raw2256step0Labels raw2256step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw2257 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 2, -2]]
def raw2257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2257step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw2257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2257 raw2257Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw2257 raw2257Labels = mixedMoment B raw2257step0 raw2257step0Labels := by
      have ha : raw2257step0 = (fun i j => raw2257 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2257step0 raw2257; decide +kernel
      have hl : raw2257step0Labels = raw2257Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2257 raw2257Labels permutation8 permutation4
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw2258 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 2, -2]]
def raw2258Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2258step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw2258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2258step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2258step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2258 raw2258Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw2258 raw2258Labels = mixedMoment B raw2258step0 raw2258step0Labels := by
      have ha : raw2258step0 = (fun i j => raw2258 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2258step0 raw2258; decide +kernel
      have hl : raw2258step0Labels = raw2258Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2258 raw2258Labels permutation8 permutation6
    mixedMoment B raw2258step0 raw2258step0Labels = mixedMoment B raw2258step1 raw2258step1Labels := by
      have ha : raw2258step1 = -raw2258step0 := by apply Matrix.ext; change ∀ i j, raw2258step1 i j = -(raw2258step0 i j); unfold raw2258step1 raw2258step0; decide +kernel
      have hl : raw2258step1Labels = raw2258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2258step1 raw2258step1Labels = mixedMoment B raw2258step2 raw2258step2Labels := by
      have ha : raw2258step2 = raw2258step1 := by apply Matrix.ext; unfold raw2258step2 raw2258step1; decide +kernel
      have hl : raw2258step1Labels = labelEmbedding1 ∘ raw2258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2258step1 raw2258step1Labels raw2258step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3397 node3397Labels := by rfl

def raw2259 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2259step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2259 raw2259Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw2259 raw2259Labels = mixedMoment B raw2259step0 raw2259step0Labels := by
      have ha : raw2259step0 = (fun i j => raw2259 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2259step0 raw2259; decide +kernel
      have hl : raw2259step0Labels = raw2259Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2259 raw2259Labels permutation152 permutation4
    mixedMoment B raw2259step0 raw2259step0Labels = mixedMoment B raw2259step1 raw2259step1Labels := by
      have ha : raw2259step1 = raw2259step0 := by apply Matrix.ext; unfold raw2259step1 raw2259step0; decide +kernel
      have hl : raw2259step0Labels = labelEmbedding7 ∘ raw2259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2259step0 raw2259step0Labels raw2259step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw2260 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2260 raw2260Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw2260 raw2260Labels = mixedMoment B raw2260step0 raw2260step0Labels := by
      have ha : raw2260step0 = (fun i j => raw2260 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2260step0 raw2260; decide +kernel
      have hl : raw2260step0Labels = raw2260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2260 raw2260Labels permutation152 permutation4
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw2261 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2261Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw2261step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2261step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2261step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2261 raw2261Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw2261 raw2261Labels = mixedMoment B raw2261step0 raw2261step0Labels := by
      have ha : raw2261step0 = (fun i j => raw2261 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2261step0 raw2261; decide +kernel
      have hl : raw2261step0Labels = raw2261Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2261 raw2261Labels permutation152 permutation6
    mixedMoment B raw2261step0 raw2261step0Labels = mixedMoment B raw2261step1 raw2261step1Labels := by
      have ha : raw2261step1 = -raw2261step0 := by apply Matrix.ext; change ∀ i j, raw2261step1 i j = -(raw2261step0 i j); unfold raw2261step1 raw2261step0; decide +kernel
      have hl : raw2261step1Labels = raw2261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2261step1 raw2261step1Labels = mixedMoment B raw2261step2 raw2261step2Labels := by
      have ha : raw2261step2 = raw2261step1 := by apply Matrix.ext; unfold raw2261step2 raw2261step1; decide +kernel
      have hl : raw2261step1Labels = labelEmbedding1 ∘ raw2261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2261step1 raw2261step1Labels raw2261step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3493 node3493Labels := by rfl

def raw2262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2262step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2262 raw2262Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw2262 raw2262Labels = mixedMoment B raw2262step0 raw2262step0Labels := by
      have ha : raw2262step0 = (fun i j => raw2262 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2262step0 raw2262; decide +kernel
      have hl : raw2262step0Labels = raw2262Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2262 raw2262Labels permutation152 permutation4
    mixedMoment B raw2262step0 raw2262step0Labels = mixedMoment B raw2262step1 raw2262step1Labels := by
      have ha : raw2262step1 = raw2262step0 := by apply Matrix.ext; unfold raw2262step1 raw2262step0; decide +kernel
      have hl : raw2262step0Labels = labelEmbedding7 ∘ raw2262step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2262step0 raw2262step0Labels raw2262step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

def raw2263 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2263 raw2263Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw2263 raw2263Labels = mixedMoment B raw2263step0 raw2263step0Labels := by
      have ha : raw2263step0 = (fun i j => raw2263 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2263step0 raw2263; decide +kernel
      have hl : raw2263step0Labels = raw2263Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2263 raw2263Labels permutation152 permutation4
    _ = mixedMoment B node2703 node2703Labels := by rfl

def raw2264 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2264Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2264step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2264step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2264 raw2264Labels = mixedMoment B node3496 node3496Labels := by
  calc
    mixedMoment B raw2264 raw2264Labels = mixedMoment B raw2264step0 raw2264step0Labels := by
      have ha : raw2264step0 = (fun i j => raw2264 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2264step0 raw2264; decide +kernel
      have hl : raw2264step0Labels = raw2264Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2264 raw2264Labels permutation152 permutation6
    mixedMoment B raw2264step0 raw2264step0Labels = mixedMoment B raw2264step1 raw2264step1Labels := by
      have ha : raw2264step1 = -raw2264step0 := by apply Matrix.ext; change ∀ i j, raw2264step1 i j = -(raw2264step0 i j); unfold raw2264step1 raw2264step0; decide +kernel
      have hl : raw2264step1Labels = raw2264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2264step1 raw2264step1Labels = mixedMoment B raw2264step2 raw2264step2Labels := by
      have ha : raw2264step2 = raw2264step1 := by apply Matrix.ext; unfold raw2264step2 raw2264step1; decide +kernel
      have hl : raw2264step1Labels = labelEmbedding1 ∘ raw2264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2264step1 raw2264step1Labels raw2264step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3496 node3496Labels := by rfl

def raw2265 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2265step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2265 raw2265Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw2265 raw2265Labels = mixedMoment B raw2265step0 raw2265step0Labels := by
      have ha : raw2265step0 = (fun i j => raw2265 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2265step0 raw2265; decide +kernel
      have hl : raw2265step0Labels = raw2265Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2265 raw2265Labels permutation32 permutation4
    mixedMoment B raw2265step0 raw2265step0Labels = mixedMoment B raw2265step1 raw2265step1Labels := by
      have ha : raw2265step1 = raw2265step0 := by apply Matrix.ext; unfold raw2265step1 raw2265step0; decide +kernel
      have hl : raw2265step0Labels = labelEmbedding7 ∘ raw2265step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2265step0 raw2265step0Labels raw2265step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw2266 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2266 raw2266Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw2266 raw2266Labels = mixedMoment B raw2266step0 raw2266step0Labels := by
      have ha : raw2266step0 = (fun i j => raw2266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2266step0 raw2266; decide +kernel
      have hl : raw2266step0Labels = raw2266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2266 raw2266Labels permutation32 permutation4
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw2267 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2267Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw2267step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2267step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2267 raw2267Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw2267 raw2267Labels = mixedMoment B raw2267step0 raw2267step0Labels := by
      have ha : raw2267step0 = (fun i j => raw2267 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2267step0 raw2267; decide +kernel
      have hl : raw2267step0Labels = raw2267Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2267 raw2267Labels permutation32 permutation6
    mixedMoment B raw2267step0 raw2267step0Labels = mixedMoment B raw2267step1 raw2267step1Labels := by
      have ha : raw2267step1 = -raw2267step0 := by apply Matrix.ext; change ∀ i j, raw2267step1 i j = -(raw2267step0 i j); unfold raw2267step1 raw2267step0; decide +kernel
      have hl : raw2267step1Labels = raw2267step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2267step1 raw2267step1Labels = mixedMoment B raw2267step2 raw2267step2Labels := by
      have ha : raw2267step2 = raw2267step1 := by apply Matrix.ext; unfold raw2267step2 raw2267step1; decide +kernel
      have hl : raw2267step1Labels = labelEmbedding1 ∘ raw2267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2267step1 raw2267step1Labels raw2267step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3498 node3498Labels := by rfl

def raw2268 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2268step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2268 raw2268Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw2268 raw2268Labels = mixedMoment B raw2268step0 raw2268step0Labels := by
      have ha : raw2268step0 = (fun i j => raw2268 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2268step0 raw2268; decide +kernel
      have hl : raw2268step0Labels = raw2268Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2268 raw2268Labels permutation152 permutation4
    mixedMoment B raw2268step0 raw2268step0Labels = mixedMoment B raw2268step1 raw2268step1Labels := by
      have ha : raw2268step1 = raw2268step0 := by apply Matrix.ext; unfold raw2268step1 raw2268step0; decide +kernel
      have hl : raw2268step0Labels = labelEmbedding7 ∘ raw2268step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2268step0 raw2268step0Labels raw2268step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw2269 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2269 raw2269Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw2269 raw2269Labels = mixedMoment B raw2269step0 raw2269step0Labels := by
      have ha : raw2269step0 = (fun i j => raw2269 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2269step0 raw2269; decide +kernel
      have hl : raw2269step0Labels = raw2269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2269 raw2269Labels permutation152 permutation4
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw2270 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2270Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2270step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2270step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2270step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2270 raw2270Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw2270 raw2270Labels = mixedMoment B raw2270step0 raw2270step0Labels := by
      have ha : raw2270step0 = (fun i j => raw2270 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2270step0 raw2270; decide +kernel
      have hl : raw2270step0Labels = raw2270Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2270 raw2270Labels permutation158 permutation6
    mixedMoment B raw2270step0 raw2270step0Labels = mixedMoment B raw2270step1 raw2270step1Labels := by
      have ha : raw2270step1 = -raw2270step0 := by apply Matrix.ext; change ∀ i j, raw2270step1 i j = -(raw2270step0 i j); unfold raw2270step1 raw2270step0; decide +kernel
      have hl : raw2270step1Labels = raw2270step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2270step1 raw2270step1Labels = mixedMoment B raw2270step2 raw2270step2Labels := by
      have ha : raw2270step2 = raw2270step1 := by apply Matrix.ext; unfold raw2270step2 raw2270step1; decide +kernel
      have hl : raw2270step1Labels = labelEmbedding1 ∘ raw2270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2270step1 raw2270step1Labels raw2270step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw2271 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2271step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2271 raw2271Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw2271 raw2271Labels = mixedMoment B raw2271step0 raw2271step0Labels := by
      have ha : raw2271step0 = (fun i j => raw2271 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2271step0 raw2271; decide +kernel
      have hl : raw2271step0Labels = raw2271Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2271 raw2271Labels permutation32 permutation4
    mixedMoment B raw2271step0 raw2271step0Labels = mixedMoment B raw2271step1 raw2271step1Labels := by
      have ha : raw2271step1 = raw2271step0 := by apply Matrix.ext; unfold raw2271step1 raw2271step0; decide +kernel
      have hl : raw2271step0Labels = labelEmbedding7 ∘ raw2271step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2271step0 raw2271step0Labels raw2271step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw2272 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2272 raw2272Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw2272 raw2272Labels = mixedMoment B raw2272step0 raw2272step0Labels := by
      have ha : raw2272step0 = (fun i j => raw2272 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2272step0 raw2272; decide +kernel
      have hl : raw2272step0Labels = raw2272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2272 raw2272Labels permutation32 permutation4
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw2273 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2273Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw2273step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2273 raw2273Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw2273 raw2273Labels = mixedMoment B raw2273step0 raw2273step0Labels := by
      have ha : raw2273step0 = (fun i j => raw2273 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2273step0 raw2273; decide +kernel
      have hl : raw2273step0Labels = raw2273Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2273 raw2273Labels permutation34 permutation6
    mixedMoment B raw2273step0 raw2273step0Labels = mixedMoment B raw2273step1 raw2273step1Labels := by
      have ha : raw2273step1 = -raw2273step0 := by apply Matrix.ext; change ∀ i j, raw2273step1 i j = -(raw2273step0 i j); unfold raw2273step1 raw2273step0; decide +kernel
      have hl : raw2273step1Labels = raw2273step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2273step1 raw2273step1Labels = mixedMoment B raw2273step2 raw2273step2Labels := by
      have ha : raw2273step2 = raw2273step1 := by apply Matrix.ext; unfold raw2273step2 raw2273step1; decide +kernel
      have hl : raw2273step1Labels = labelEmbedding1 ∘ raw2273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2273step1 raw2273step1Labels raw2273step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw2274 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2274step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2274 raw2274Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2274 raw2274Labels = mixedMoment B raw2274step0 raw2274step0Labels := by
      have ha : raw2274step0 = (fun i j => raw2274 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2274step0 raw2274; decide +kernel
      have hl : raw2274step0Labels = raw2274Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2274 raw2274Labels permutation32 permutation4
    mixedMoment B raw2274step0 raw2274step0Labels = mixedMoment B raw2274step1 raw2274step1Labels := by
      have ha : raw2274step1 = raw2274step0 := by apply Matrix.ext; unfold raw2274step1 raw2274step0; decide +kernel
      have hl : raw2274step0Labels = labelEmbedding7 ∘ raw2274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2274step0 raw2274step0Labels raw2274step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw2275 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2275 raw2275Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2275 raw2275Labels = mixedMoment B raw2275step0 raw2275step0Labels := by
      have ha : raw2275step0 = (fun i j => raw2275 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2275step0 raw2275; decide +kernel
      have hl : raw2275step0Labels = raw2275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2275 raw2275Labels permutation32 permutation4
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw2276 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2276Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2276step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2276step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2276 raw2276Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw2276 raw2276Labels = mixedMoment B raw2276step0 raw2276step0Labels := by
      have ha : raw2276step0 = (fun i j => raw2276 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2276step0 raw2276; decide +kernel
      have hl : raw2276step0Labels = raw2276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2276 raw2276Labels permutation32 permutation6
    mixedMoment B raw2276step0 raw2276step0Labels = mixedMoment B raw2276step1 raw2276step1Labels := by
      have ha : raw2276step1 = -raw2276step0 := by apply Matrix.ext; change ∀ i j, raw2276step1 i j = -(raw2276step0 i j); unfold raw2276step1 raw2276step0; decide +kernel
      have hl : raw2276step1Labels = raw2276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2276step1 raw2276step1Labels = mixedMoment B raw2276step2 raw2276step2Labels := by
      have ha : raw2276step2 = raw2276step1 := by apply Matrix.ext; unfold raw2276step2 raw2276step1; decide +kernel
      have hl : raw2276step1Labels = labelEmbedding1 ∘ raw2276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2276step1 raw2276step1Labels raw2276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw2277 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2]]
def raw2277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2277step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2277step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2277 raw2277Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw2277 raw2277Labels = mixedMoment B raw2277step0 raw2277step0Labels := by
      have ha : raw2277step0 = (fun i j => raw2277 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2277step0 raw2277; decide +kernel
      have hl : raw2277step0Labels = raw2277Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2277 raw2277Labels permutation8 permutation4
    mixedMoment B raw2277step0 raw2277step0Labels = mixedMoment B raw2277step1 raw2277step1Labels := by
      have ha : raw2277step1 = raw2277step0 := by apply Matrix.ext; unfold raw2277step1 raw2277step0; decide +kernel
      have hl : raw2277step0Labels = labelEmbedding7 ∘ raw2277step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2277step0 raw2277step0Labels raw2277step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw2278 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2]]
def raw2278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2278step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2278 raw2278Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw2278 raw2278Labels = mixedMoment B raw2278step0 raw2278step0Labels := by
      have ha : raw2278step0 = (fun i j => raw2278 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2278step0 raw2278; decide +kernel
      have hl : raw2278step0Labels = raw2278Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2278 raw2278Labels permutation8 permutation4
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw2279 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2]]
def raw2279Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2279step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw2279step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw2279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2279 raw2279Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw2279 raw2279Labels = mixedMoment B raw2279step0 raw2279step0Labels := by
      have ha : raw2279step0 = (fun i j => raw2279 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2279step0 raw2279; decide +kernel
      have hl : raw2279step0Labels = raw2279Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2279 raw2279Labels permutation31 permutation6
    mixedMoment B raw2279step0 raw2279step0Labels = mixedMoment B raw2279step1 raw2279step1Labels := by
      have ha : raw2279step1 = raw2279step0 := by apply Matrix.ext; unfold raw2279step1 raw2279step0; decide +kernel
      have hl : raw2279step0Labels = labelEmbedding1 ∘ raw2279step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2279step0 raw2279step0Labels raw2279step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3545 node3545Labels := by rfl

def raw2280 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2280step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2280 raw2280Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw2280 raw2280Labels = mixedMoment B raw2280step0 raw2280step0Labels := by
      have ha : raw2280step0 = (fun i j => raw2280 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2280step0 raw2280; decide +kernel
      have hl : raw2280step0Labels = raw2280Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2280 raw2280Labels permutation32 permutation4
    mixedMoment B raw2280step0 raw2280step0Labels = mixedMoment B raw2280step1 raw2280step1Labels := by
      have ha : raw2280step1 = raw2280step0 := by apply Matrix.ext; unfold raw2280step1 raw2280step0; decide +kernel
      have hl : raw2280step0Labels = labelEmbedding7 ∘ raw2280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2280step0 raw2280step0Labels raw2280step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw2281 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2281 raw2281Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw2281 raw2281Labels = mixedMoment B raw2281step0 raw2281step0Labels := by
      have ha : raw2281step0 = (fun i j => raw2281 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2281step0 raw2281; decide +kernel
      have hl : raw2281step0Labels = raw2281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2281 raw2281Labels permutation32 permutation4
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw2282 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2282Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2282step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2282 raw2282Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw2282 raw2282Labels = mixedMoment B raw2282step0 raw2282step0Labels := by
      have ha : raw2282step0 = (fun i j => raw2282 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2282step0 raw2282; decide +kernel
      have hl : raw2282step0Labels = raw2282Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2282 raw2282Labels permutation32 permutation6
    mixedMoment B raw2282step0 raw2282step0Labels = mixedMoment B raw2282step1 raw2282step1Labels := by
      have ha : raw2282step1 = -raw2282step0 := by apply Matrix.ext; change ∀ i j, raw2282step1 i j = -(raw2282step0 i j); unfold raw2282step1 raw2282step0; decide +kernel
      have hl : raw2282step1Labels = raw2282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2282step1 raw2282step1Labels = mixedMoment B raw2282step2 raw2282step2Labels := by
      have ha : raw2282step2 = raw2282step1 := by apply Matrix.ext; unfold raw2282step2 raw2282step1; decide +kernel
      have hl : raw2282step1Labels = labelEmbedding1 ∘ raw2282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2282step1 raw2282step1Labels raw2282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw2283 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3]]
def raw2283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2283step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2283step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2283 raw2283Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw2283 raw2283Labels = mixedMoment B raw2283step0 raw2283step0Labels := by
      have ha : raw2283step0 = (fun i j => raw2283 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2283step0 raw2283; decide +kernel
      have hl : raw2283step0Labels = raw2283Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2283 raw2283Labels permutation8 permutation4
    mixedMoment B raw2283step0 raw2283step0Labels = mixedMoment B raw2283step1 raw2283step1Labels := by
      have ha : raw2283step1 = raw2283step0 := by apply Matrix.ext; unfold raw2283step1 raw2283step0; decide +kernel
      have hl : raw2283step0Labels = labelEmbedding7 ∘ raw2283step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2283step0 raw2283step0Labels raw2283step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw2284 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3]]
def raw2284Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2284step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2284step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2284 raw2284Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2284 raw2284Labels = mixedMoment B raw2284step0 raw2284step0Labels := by
      have ha : raw2284step0 = (fun i j => raw2284 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2284step0 raw2284; decide +kernel
      have hl : raw2284step0Labels = raw2284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2284 raw2284Labels permutation8 permutation4
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw2285 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3]]
def raw2285Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2285step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2285step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2285step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2285 raw2285Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2285 raw2285Labels = mixedMoment B raw2285step0 raw2285step0Labels := by
      have ha : raw2285step0 = (fun i j => raw2285 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2285step0 raw2285; decide +kernel
      have hl : raw2285step0Labels = raw2285Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2285 raw2285Labels permutation31 permutation6
    mixedMoment B raw2285step0 raw2285step0Labels = mixedMoment B raw2285step1 raw2285step1Labels := by
      have ha : raw2285step1 = raw2285step0 := by apply Matrix.ext; unfold raw2285step1 raw2285step0; decide +kernel
      have hl : raw2285step0Labels = labelEmbedding1 ∘ raw2285step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2285step0 raw2285step0Labels raw2285step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw2286 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2286step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2286step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2286 raw2286Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw2286 raw2286Labels = mixedMoment B raw2286step0 raw2286step0Labels := by
      have ha : raw2286step0 = (fun i j => raw2286 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2286step0 raw2286; decide +kernel
      have hl : raw2286step0Labels = raw2286Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2286 raw2286Labels permutation8 permutation4
    mixedMoment B raw2286step0 raw2286step0Labels = mixedMoment B raw2286step1 raw2286step1Labels := by
      have ha : raw2286step1 = raw2286step0 := by apply Matrix.ext; unfold raw2286step1 raw2286step0; decide +kernel
      have hl : raw2286step0Labels = labelEmbedding7 ∘ raw2286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2286step0 raw2286step0Labels raw2286step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw2287 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2287Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2287step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2287 raw2287Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw2287 raw2287Labels = mixedMoment B raw2287step0 raw2287step0Labels := by
      have ha : raw2287step0 = (fun i j => raw2287 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2287step0 raw2287; decide +kernel
      have hl : raw2287step0Labels = raw2287Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2287 raw2287Labels permutation8 permutation4
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw2288 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2288Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2288step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw2288step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2288step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2288step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2288 raw2288Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw2288 raw2288Labels = mixedMoment B raw2288step0 raw2288step0Labels := by
      have ha : raw2288step0 = (fun i j => raw2288 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2288step0 raw2288; decide +kernel
      have hl : raw2288step0Labels = raw2288Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2288 raw2288Labels permutation9 permutation6
    mixedMoment B raw2288step0 raw2288step0Labels = mixedMoment B raw2288step1 raw2288step1Labels := by
      have ha : raw2288step1 = -raw2288step0 := by apply Matrix.ext; change ∀ i j, raw2288step1 i j = -(raw2288step0 i j); unfold raw2288step1 raw2288step0; decide +kernel
      have hl : raw2288step1Labels = raw2288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2288step1 raw2288step1Labels = mixedMoment B raw2288step2 raw2288step2Labels := by
      have ha : raw2288step2 = raw2288step1 := by apply Matrix.ext; unfold raw2288step2 raw2288step1; decide +kernel
      have hl : raw2288step1Labels = labelEmbedding1 ∘ raw2288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2288step1 raw2288step1Labels raw2288step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw2289 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2289step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2289 raw2289Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw2289 raw2289Labels = mixedMoment B raw2289step0 raw2289step0Labels := by
      have ha : raw2289step0 = (fun i j => raw2289 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2289step0 raw2289; decide +kernel
      have hl : raw2289step0Labels = raw2289Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2289 raw2289Labels permutation32 permutation5
    mixedMoment B raw2289step0 raw2289step0Labels = mixedMoment B raw2289step1 raw2289step1Labels := by
      have ha : raw2289step1 = raw2289step0 := by apply Matrix.ext; unfold raw2289step1 raw2289step0; decide +kernel
      have hl : raw2289step0Labels = labelEmbedding8 ∘ raw2289step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2289step0 raw2289step0Labels raw2289step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw2290 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2290Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2290step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2290 raw2290Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw2290 raw2290Labels = mixedMoment B raw2290step0 raw2290step0Labels := by
      have ha : raw2290step0 = (fun i j => raw2290 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2290step0 raw2290; decide +kernel
      have hl : raw2290step0Labels = raw2290Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2290 raw2290Labels permutation32 permutation4
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw2291 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2291Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw2291step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw2291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw2291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2291 raw2291Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw2291 raw2291Labels = mixedMoment B raw2291step0 raw2291step0Labels := by
      have ha : raw2291step0 = (fun i j => raw2291 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2291step0 raw2291; decide +kernel
      have hl : raw2291step0Labels = raw2291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2291 raw2291Labels permutation48 permutation3
    mixedMoment B raw2291step0 raw2291step0Labels = mixedMoment B raw2291step1 raw2291step1Labels := by
      have ha : raw2291step1 = -raw2291step0 := by apply Matrix.ext; change ∀ i j, raw2291step1 i j = -(raw2291step0 i j); unfold raw2291step1 raw2291step0; decide +kernel
      have hl : raw2291step1Labels = raw2291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2291step1 raw2291step1Labels = mixedMoment B raw2291step2 raw2291step2Labels := by
      have ha : raw2291step2 = raw2291step1 := by apply Matrix.ext; unfold raw2291step2 raw2291step1; decide +kernel
      have hl : raw2291step1Labels = labelEmbedding1 ∘ raw2291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2291step1 raw2291step1Labels raw2291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw2292 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2292step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2292 raw2292Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw2292 raw2292Labels = mixedMoment B raw2292step0 raw2292step0Labels := by
      have ha : raw2292step0 = (fun i j => raw2292 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2292step0 raw2292; decide +kernel
      have hl : raw2292step0Labels = raw2292Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2292 raw2292Labels permutation32 permutation4
    mixedMoment B raw2292step0 raw2292step0Labels = mixedMoment B raw2292step1 raw2292step1Labels := by
      have ha : raw2292step1 = raw2292step0 := by apply Matrix.ext; unfold raw2292step1 raw2292step0; decide +kernel
      have hl : raw2292step0Labels = labelEmbedding7 ∘ raw2292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2292step0 raw2292step0Labels raw2292step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw2293 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2293Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2293step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2293 raw2293Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw2293 raw2293Labels = mixedMoment B raw2293step0 raw2293step0Labels := by
      have ha : raw2293step0 = (fun i j => raw2293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2293step0 raw2293; decide +kernel
      have hl : raw2293step0Labels = raw2293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2293 raw2293Labels permutation32 permutation4
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw2294 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2294Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2294 raw2294Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw2294 raw2294Labels = mixedMoment B raw2294step0 raw2294step0Labels := by
      have ha : raw2294step0 = (fun i j => raw2294 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2294step0 raw2294; decide +kernel
      have hl : raw2294step0Labels = raw2294Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2294 raw2294Labels permutation38 permutation6
    mixedMoment B raw2294step0 raw2294step0Labels = mixedMoment B raw2294step1 raw2294step1Labels := by
      have ha : raw2294step1 = -raw2294step0 := by apply Matrix.ext; change ∀ i j, raw2294step1 i j = -(raw2294step0 i j); unfold raw2294step1 raw2294step0; decide +kernel
      have hl : raw2294step1Labels = raw2294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2294step1 raw2294step1Labels = mixedMoment B raw2294step2 raw2294step2Labels := by
      have ha : raw2294step2 = raw2294step1 := by apply Matrix.ext; unfold raw2294step2 raw2294step1; decide +kernel
      have hl : raw2294step1Labels = labelEmbedding1 ∘ raw2294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2294step1 raw2294step1Labels raw2294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw2295 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2295step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2295step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2295 raw2295Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw2295 raw2295Labels = mixedMoment B raw2295step0 raw2295step0Labels := by
      have ha : raw2295step0 = (fun i j => raw2295 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2295step0 raw2295; decide +kernel
      have hl : raw2295step0Labels = raw2295Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2295 raw2295Labels permutation8 permutation4
    mixedMoment B raw2295step0 raw2295step0Labels = mixedMoment B raw2295step1 raw2295step1Labels := by
      have ha : raw2295step1 = raw2295step0 := by apply Matrix.ext; unfold raw2295step1 raw2295step0; decide +kernel
      have hl : raw2295step0Labels = labelEmbedding7 ∘ raw2295step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2295step0 raw2295step0Labels raw2295step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw2296 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2296Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2296step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2296 raw2296Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw2296 raw2296Labels = mixedMoment B raw2296step0 raw2296step0Labels := by
      have ha : raw2296step0 = (fun i j => raw2296 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2296step0 raw2296; decide +kernel
      have hl : raw2296step0Labels = raw2296Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2296 raw2296Labels permutation8 permutation4
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw2297 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2297Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2297step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw2297step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2297 raw2297Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw2297 raw2297Labels = mixedMoment B raw2297step0 raw2297step0Labels := by
      have ha : raw2297step0 = (fun i j => raw2297 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2297step0 raw2297; decide +kernel
      have hl : raw2297step0Labels = raw2297Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2297 raw2297Labels permutation10 permutation6
    mixedMoment B raw2297step0 raw2297step0Labels = mixedMoment B raw2297step1 raw2297step1Labels := by
      have ha : raw2297step1 = -raw2297step0 := by apply Matrix.ext; change ∀ i j, raw2297step1 i j = -(raw2297step0 i j); unfold raw2297step1 raw2297step0; decide +kernel
      have hl : raw2297step1Labels = raw2297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2297step1 raw2297step1Labels = mixedMoment B raw2297step2 raw2297step2Labels := by
      have ha : raw2297step2 = raw2297step1 := by apply Matrix.ext; unfold raw2297step2 raw2297step1; decide +kernel
      have hl : raw2297step1Labels = labelEmbedding1 ∘ raw2297step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2297step1 raw2297step1Labels raw2297step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw2298 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2298step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2298 raw2298Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw2298 raw2298Labels = mixedMoment B raw2298step0 raw2298step0Labels := by
      have ha : raw2298step0 = (fun i j => raw2298 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2298step0 raw2298; decide +kernel
      have hl : raw2298step0Labels = raw2298Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2298 raw2298Labels permutation32 permutation4
    mixedMoment B raw2298step0 raw2298step0Labels = mixedMoment B raw2298step1 raw2298step1Labels := by
      have ha : raw2298step1 = raw2298step0 := by apply Matrix.ext; unfold raw2298step1 raw2298step0; decide +kernel
      have hl : raw2298step0Labels = labelEmbedding7 ∘ raw2298step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2298step0 raw2298step0Labels raw2298step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw2299 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2299 raw2299Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw2299 raw2299Labels = mixedMoment B raw2299step0 raw2299step0Labels := by
      have ha : raw2299step0 = (fun i j => raw2299 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2299step0 raw2299; decide +kernel
      have hl : raw2299step0Labels = raw2299Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2299 raw2299Labels permutation32 permutation4
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw2300 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2300Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2300 raw2300Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw2300 raw2300Labels = mixedMoment B raw2300step0 raw2300step0Labels := by
      have ha : raw2300step0 = (fun i j => raw2300 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2300step0 raw2300; decide +kernel
      have hl : raw2300step0Labels = raw2300Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2300 raw2300Labels permutation40 permutation6
    mixedMoment B raw2300step0 raw2300step0Labels = mixedMoment B raw2300step1 raw2300step1Labels := by
      have ha : raw2300step1 = -raw2300step0 := by apply Matrix.ext; change ∀ i j, raw2300step1 i j = -(raw2300step0 i j); unfold raw2300step1 raw2300step0; decide +kernel
      have hl : raw2300step1Labels = raw2300step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2300step1 raw2300step1Labels = mixedMoment B raw2300step2 raw2300step2Labels := by
      have ha : raw2300step2 = raw2300step1 := by apply Matrix.ext; unfold raw2300step2 raw2300step1; decide +kernel
      have hl : raw2300step1Labels = labelEmbedding1 ∘ raw2300step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2300step1 raw2300step1Labels raw2300step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3622 node3622Labels := by rfl

def raw2301 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2301step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2301step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2301 raw2301Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2301 raw2301Labels = mixedMoment B raw2301step0 raw2301step0Labels := by
      have ha : raw2301step0 = (fun i j => raw2301 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2301step0 raw2301; decide +kernel
      have hl : raw2301step0Labels = raw2301Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2301 raw2301Labels permutation8 permutation4
    mixedMoment B raw2301step0 raw2301step0Labels = mixedMoment B raw2301step1 raw2301step1Labels := by
      have ha : raw2301step1 = raw2301step0 := by apply Matrix.ext; unfold raw2301step1 raw2301step0; decide +kernel
      have hl : raw2301step0Labels = labelEmbedding7 ∘ raw2301step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2301step0 raw2301step0Labels raw2301step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw2302 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2302step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2302step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2302 raw2302Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw2302 raw2302Labels = mixedMoment B raw2302step0 raw2302step0Labels := by
      have ha : raw2302step0 = (fun i j => raw2302 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2302step0 raw2302; decide +kernel
      have hl : raw2302step0Labels = raw2302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2302 raw2302Labels permutation8 permutation4
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw2303 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2303Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2303step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw2303step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2303step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2303 raw2303Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw2303 raw2303Labels = mixedMoment B raw2303step0 raw2303step0Labels := by
      have ha : raw2303step0 = (fun i j => raw2303 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2303step0 raw2303; decide +kernel
      have hl : raw2303step0Labels = raw2303Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2303 raw2303Labels permutation10 permutation6
    mixedMoment B raw2303step0 raw2303step0Labels = mixedMoment B raw2303step1 raw2303step1Labels := by
      have ha : raw2303step1 = -raw2303step0 := by apply Matrix.ext; change ∀ i j, raw2303step1 i j = -(raw2303step0 i j); unfold raw2303step1 raw2303step0; decide +kernel
      have hl : raw2303step1Labels = raw2303step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2303step1 raw2303step1Labels = mixedMoment B raw2303step2 raw2303step2Labels := by
      have ha : raw2303step2 = raw2303step1 := by apply Matrix.ext; unfold raw2303step2 raw2303step1; decide +kernel
      have hl : raw2303step1Labels = labelEmbedding1 ∘ raw2303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2303step1 raw2303step1Labels raw2303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3627 node3627Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
