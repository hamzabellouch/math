import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1920 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1920step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1920step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1920 raw1920Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw1920 raw1920Labels = mixedMoment B raw1920step0 raw1920step0Labels := by
      have ha : raw1920step0 = (fun i j => raw1920 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1920step0 raw1920; decide +kernel
      have hl : raw1920step0Labels = raw1920Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1920 raw1920Labels permutation32 permutation4
    mixedMoment B raw1920step0 raw1920step0Labels = mixedMoment B raw1920step1 raw1920step1Labels := by
      have ha : raw1920step1 = raw1920step0 := by apply Matrix.ext; unfold raw1920step1 raw1920step0; decide +kernel
      have hl : raw1920step0Labels = labelEmbedding7 ∘ raw1920step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1920step0 raw1920step0Labels raw1920step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw1921 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1921 raw1921Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw1921 raw1921Labels = mixedMoment B raw1921step0 raw1921step0Labels := by
      have ha : raw1921step0 = (fun i j => raw1921 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1921step0 raw1921; decide +kernel
      have hl : raw1921step0Labels = raw1921Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1921 raw1921Labels permutation32 permutation4
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw1922 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1922Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw1922step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1922step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1922step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1922 raw1922Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw1922 raw1922Labels = mixedMoment B raw1922step0 raw1922step0Labels := by
      have ha : raw1922step0 = (fun i j => raw1922 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1922step0 raw1922; decide +kernel
      have hl : raw1922step0Labels = raw1922Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1922 raw1922Labels permutation34 permutation6
    mixedMoment B raw1922step0 raw1922step0Labels = mixedMoment B raw1922step1 raw1922step1Labels := by
      have ha : raw1922step1 = -raw1922step0 := by apply Matrix.ext; change ∀ i j, raw1922step1 i j = -(raw1922step0 i j); unfold raw1922step1 raw1922step0; decide +kernel
      have hl : raw1922step1Labels = raw1922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1922step1 raw1922step1Labels = mixedMoment B raw1922step2 raw1922step2Labels := by
      have ha : raw1922step2 = raw1922step1 := by apply Matrix.ext; unfold raw1922step2 raw1922step1; decide +kernel
      have hl : raw1922step1Labels = labelEmbedding1 ∘ raw1922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1922step1 raw1922step1Labels raw1922step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3417 node3417Labels := by rfl

def raw1923 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1923step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1923 raw1923Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw1923 raw1923Labels = mixedMoment B raw1923step0 raw1923step0Labels := by
      have ha : raw1923step0 = (fun i j => raw1923 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1923step0 raw1923; decide +kernel
      have hl : raw1923step0Labels = raw1923Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1923 raw1923Labels permutation32 permutation4
    mixedMoment B raw1923step0 raw1923step0Labels = mixedMoment B raw1923step1 raw1923step1Labels := by
      have ha : raw1923step1 = raw1923step0 := by apply Matrix.ext; unfold raw1923step1 raw1923step0; decide +kernel
      have hl : raw1923step0Labels = labelEmbedding7 ∘ raw1923step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1923step0 raw1923step0Labels raw1923step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw1924 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1924 raw1924Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw1924 raw1924Labels = mixedMoment B raw1924step0 raw1924step0Labels := by
      have ha : raw1924step0 = (fun i j => raw1924 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1924step0 raw1924; decide +kernel
      have hl : raw1924step0Labels = raw1924Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1924 raw1924Labels permutation32 permutation4
    _ = mixedMoment B node2342 node2342Labels := by rfl

def raw1925 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1925Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1925step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1925step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1925 raw1925Labels = mixedMoment B node3421 node3421Labels := by
  calc
    mixedMoment B raw1925 raw1925Labels = mixedMoment B raw1925step0 raw1925step0Labels := by
      have ha : raw1925step0 = (fun i j => raw1925 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1925step0 raw1925; decide +kernel
      have hl : raw1925step0Labels = raw1925Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1925 raw1925Labels permutation32 permutation6
    mixedMoment B raw1925step0 raw1925step0Labels = mixedMoment B raw1925step1 raw1925step1Labels := by
      have ha : raw1925step1 = -raw1925step0 := by apply Matrix.ext; change ∀ i j, raw1925step1 i j = -(raw1925step0 i j); unfold raw1925step1 raw1925step0; decide +kernel
      have hl : raw1925step1Labels = raw1925step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1925step1 raw1925step1Labels = mixedMoment B raw1925step2 raw1925step2Labels := by
      have ha : raw1925step2 = raw1925step1 := by apply Matrix.ext; unfold raw1925step2 raw1925step1; decide +kernel
      have hl : raw1925step1Labels = labelEmbedding1 ∘ raw1925step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1925step1 raw1925step1Labels raw1925step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3421 node3421Labels := by rfl

def raw1926 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1926step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw1926step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw1926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1926 raw1926Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw1926 raw1926Labels = mixedMoment B raw1926step0 raw1926step0Labels := by
      have ha : raw1926step0 = (fun i j => raw1926 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1926step0 raw1926; decide +kernel
      have hl : raw1926step0Labels = raw1926Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1926 raw1926Labels permutation8 permutation4
    mixedMoment B raw1926step0 raw1926step0Labels = mixedMoment B raw1926step1 raw1926step1Labels := by
      have ha : raw1926step1 = raw1926step0 := by apply Matrix.ext; unfold raw1926step1 raw1926step0; decide +kernel
      have hl : raw1926step0Labels = labelEmbedding7 ∘ raw1926step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1926step0 raw1926step0Labels raw1926step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4952 node4952Labels := by rfl

def raw1927 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1927step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw1927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1927 raw1927Labels = mixedMoment B node2344 node2344Labels := by
  calc
    mixedMoment B raw1927 raw1927Labels = mixedMoment B raw1927step0 raw1927step0Labels := by
      have ha : raw1927step0 = (fun i j => raw1927 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1927step0 raw1927; decide +kernel
      have hl : raw1927step0Labels = raw1927Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1927 raw1927Labels permutation8 permutation4
    _ = mixedMoment B node2344 node2344Labels := by rfl

def raw1928 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1928Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1928step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw1928step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw1928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1928 raw1928Labels = mixedMoment B node3422 node3422Labels := by
  calc
    mixedMoment B raw1928 raw1928Labels = mixedMoment B raw1928step0 raw1928step0Labels := by
      have ha : raw1928step0 = (fun i j => raw1928 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1928step0 raw1928; decide +kernel
      have hl : raw1928step0Labels = raw1928Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1928 raw1928Labels permutation31 permutation6
    mixedMoment B raw1928step0 raw1928step0Labels = mixedMoment B raw1928step1 raw1928step1Labels := by
      have ha : raw1928step1 = raw1928step0 := by apply Matrix.ext; unfold raw1928step1 raw1928step0; decide +kernel
      have hl : raw1928step0Labels = labelEmbedding1 ∘ raw1928step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1928step0 raw1928step0Labels raw1928step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3422 node3422Labels := by rfl

def raw1929 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw1929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1929step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw1929step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw1929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1929 raw1929Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw1929 raw1929Labels = mixedMoment B raw1929step0 raw1929step0Labels := by
      have ha : raw1929step0 = (fun i j => raw1929 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1929step0 raw1929; decide +kernel
      have hl : raw1929step0Labels = raw1929Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1929 raw1929Labels permutation8 permutation4
    mixedMoment B raw1929step0 raw1929step0Labels = mixedMoment B raw1929step1 raw1929step1Labels := by
      have ha : raw1929step1 = raw1929step0 := by apply Matrix.ext; unfold raw1929step1 raw1929step0; decide +kernel
      have hl : raw1929step0Labels = labelEmbedding7 ∘ raw1929step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1929step0 raw1929step0Labels raw1929step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4953 node4953Labels := by rfl

def raw1930 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw1930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1930step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw1930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1930 raw1930Labels = mixedMoment B node2345 node2345Labels := by
  calc
    mixedMoment B raw1930 raw1930Labels = mixedMoment B raw1930step0 raw1930step0Labels := by
      have ha : raw1930step0 = (fun i j => raw1930 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1930step0 raw1930; decide +kernel
      have hl : raw1930step0Labels = raw1930Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1930 raw1930Labels permutation8 permutation4
    _ = mixedMoment B node2345 node2345Labels := by rfl

def raw1931 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw1931Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1931step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw1931step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw1931step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw1931step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1931 raw1931Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw1931 raw1931Labels = mixedMoment B raw1931step0 raw1931step0Labels := by
      have ha : raw1931step0 = (fun i j => raw1931 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1931step0 raw1931; decide +kernel
      have hl : raw1931step0Labels = raw1931Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1931 raw1931Labels permutation9 permutation6
    mixedMoment B raw1931step0 raw1931step0Labels = mixedMoment B raw1931step1 raw1931step1Labels := by
      have ha : raw1931step1 = -raw1931step0 := by apply Matrix.ext; change ∀ i j, raw1931step1 i j = -(raw1931step0 i j); unfold raw1931step1 raw1931step0; decide +kernel
      have hl : raw1931step1Labels = raw1931step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1931step1 raw1931step1Labels = mixedMoment B raw1931step2 raw1931step2Labels := by
      have ha : raw1931step2 = raw1931step1 := by apply Matrix.ext; unfold raw1931step2 raw1931step1; decide +kernel
      have hl : raw1931step1Labels = labelEmbedding1 ∘ raw1931step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1931step1 raw1931step1Labels raw1931step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3423 node3423Labels := by rfl

def raw1932 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw1932step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw1932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1932 raw1932Labels = mixedMoment B node4960 node4960Labels := by
  calc
    mixedMoment B raw1932 raw1932Labels = mixedMoment B raw1932step0 raw1932step0Labels := by
      have ha : raw1932step0 = (fun i j => raw1932 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1932step0 raw1932; decide +kernel
      have hl : raw1932step0Labels = raw1932Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1932 raw1932Labels permutation152 permutation5
    mixedMoment B raw1932step0 raw1932step0Labels = mixedMoment B raw1932step1 raw1932step1Labels := by
      have ha : raw1932step1 = raw1932step0 := by apply Matrix.ext; unfold raw1932step1 raw1932step0; decide +kernel
      have hl : raw1932step0Labels = labelEmbedding8 ∘ raw1932step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1932step0 raw1932step0Labels raw1932step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4960 node4960Labels := by rfl

def raw1933 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw1933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1933step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1933 raw1933Labels = mixedMoment B node2412 node2412Labels := by
  calc
    mixedMoment B raw1933 raw1933Labels = mixedMoment B raw1933step0 raw1933step0Labels := by
      have ha : raw1933step0 = (fun i j => raw1933 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1933step0 raw1933; decide +kernel
      have hl : raw1933step0Labels = raw1933Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1933 raw1933Labels permutation664 permutation4
    mixedMoment B raw1933step0 raw1933step0Labels = mixedMoment B raw1933step1 raw1933step1Labels := by
      have ha : raw1933step1 = -raw1933step0 := by apply Matrix.ext; change ∀ i j, raw1933step1 i j = -(raw1933step0 i j); unfold raw1933step1 raw1933step0; decide +kernel
      have hl : raw1933step1Labels = raw1933step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2412 node2412Labels := by rfl

def raw1934 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1934Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1934step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1934step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1934 raw1934Labels = mixedMoment B node3426 node3426Labels := by
  calc
    mixedMoment B raw1934 raw1934Labels = mixedMoment B raw1934step0 raw1934step0Labels := by
      have ha : raw1934step0 = (fun i j => raw1934 (permutation663 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1934step0 raw1934; decide +kernel
      have hl : raw1934step0Labels = raw1934Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1934 raw1934Labels permutation663 permutation6
    mixedMoment B raw1934step0 raw1934step0Labels = mixedMoment B raw1934step1 raw1934step1Labels := by
      have ha : raw1934step1 = raw1934step0 := by apply Matrix.ext; unfold raw1934step1 raw1934step0; decide +kernel
      have hl : raw1934step0Labels = labelEmbedding1 ∘ raw1934step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1934step0 raw1934step0Labels raw1934step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3426 node3426Labels := by rfl

def raw1935 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![-1, 2, -1]]
def raw1935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw1935step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw1935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1935 raw1935Labels = mixedMoment B node4961 node4961Labels := by
  calc
    mixedMoment B raw1935 raw1935Labels = mixedMoment B raw1935step0 raw1935step0Labels := by
      have ha : raw1935step0 = (fun i j => raw1935 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1935step0 raw1935; decide +kernel
      have hl : raw1935step0Labels = raw1935Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1935 raw1935Labels permutation152 permutation5
    mixedMoment B raw1935step0 raw1935step0Labels = mixedMoment B raw1935step1 raw1935step1Labels := by
      have ha : raw1935step1 = raw1935step0 := by apply Matrix.ext; unfold raw1935step1 raw1935step0; decide +kernel
      have hl : raw1935step0Labels = labelEmbedding8 ∘ raw1935step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1935step0 raw1935step0Labels raw1935step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4961 node4961Labels := by rfl

def raw1936 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![-1, 2, -1]]
def raw1936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1936 raw1936Labels = mixedMoment B node2796 node2796Labels := by
  calc
    mixedMoment B raw1936 raw1936Labels = mixedMoment B raw1936step0 raw1936step0Labels := by
      have ha : raw1936step0 = (fun i j => raw1936 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1936step0 raw1936; decide +kernel
      have hl : raw1936step0Labels = raw1936Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1936 raw1936Labels permutation153 permutation4
    _ = mixedMoment B node2796 node2796Labels := by rfl

def raw1937 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![-1, 2, -1]]
def raw1937Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw1937step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1937step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw1937step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1937step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw1937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1937 raw1937Labels = mixedMoment B node3589 node3589Labels := by
  calc
    mixedMoment B raw1937 raw1937Labels = mixedMoment B raw1937step0 raw1937step0Labels := by
      have ha : raw1937step0 = (fun i j => raw1937 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1937step0 raw1937; decide +kernel
      have hl : raw1937step0Labels = raw1937Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1937 raw1937Labels permutation160 permutation3
    mixedMoment B raw1937step0 raw1937step0Labels = mixedMoment B raw1937step1 raw1937step1Labels := by
      have ha : raw1937step1 = -raw1937step0 := by apply Matrix.ext; change ∀ i j, raw1937step1 i j = -(raw1937step0 i j); unfold raw1937step1 raw1937step0; decide +kernel
      have hl : raw1937step1Labels = raw1937step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1937step1 raw1937step1Labels = mixedMoment B raw1937step2 raw1937step2Labels := by
      have ha : raw1937step2 = raw1937step1 := by apply Matrix.ext; unfold raw1937step2 raw1937step1; decide +kernel
      have hl : raw1937step1Labels = labelEmbedding1 ∘ raw1937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1937step1 raw1937step1Labels raw1937step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3589 node3589Labels := by rfl

def raw1938 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw1938step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw1938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1938 raw1938Labels = mixedMoment B node4962 node4962Labels := by
  calc
    mixedMoment B raw1938 raw1938Labels = mixedMoment B raw1938step0 raw1938step0Labels := by
      have ha : raw1938step0 = (fun i j => raw1938 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1938step0 raw1938; decide +kernel
      have hl : raw1938step0Labels = raw1938Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1938 raw1938Labels permutation152 permutation5
    mixedMoment B raw1938step0 raw1938step0Labels = mixedMoment B raw1938step1 raw1938step1Labels := by
      have ha : raw1938step1 = raw1938step0 := by apply Matrix.ext; unfold raw1938step1 raw1938step0; decide +kernel
      have hl : raw1938step0Labels = labelEmbedding8 ∘ raw1938step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1938step0 raw1938step0Labels raw1938step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4962 node4962Labels := by rfl

def raw1939 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1939 raw1939Labels = mixedMoment B node2795 node2795Labels := by
  calc
    mixedMoment B raw1939 raw1939Labels = mixedMoment B raw1939step0 raw1939step0Labels := by
      have ha : raw1939step0 = (fun i j => raw1939 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1939step0 raw1939; decide +kernel
      have hl : raw1939step0Labels = raw1939Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1939 raw1939Labels permutation152 permutation4
    _ = mixedMoment B node2795 node2795Labels := by rfl

def raw1940 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1940Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw1940step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw1940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1940step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw1940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1940 raw1940Labels = mixedMoment B node3593 node3593Labels := by
  calc
    mixedMoment B raw1940 raw1940Labels = mixedMoment B raw1940step0 raw1940step0Labels := by
      have ha : raw1940step0 = (fun i j => raw1940 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1940step0 raw1940; decide +kernel
      have hl : raw1940step0Labels = raw1940Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1940 raw1940Labels permutation168 permutation3
    mixedMoment B raw1940step0 raw1940step0Labels = mixedMoment B raw1940step1 raw1940step1Labels := by
      have ha : raw1940step1 = -raw1940step0 := by apply Matrix.ext; change ∀ i j, raw1940step1 i j = -(raw1940step0 i j); unfold raw1940step1 raw1940step0; decide +kernel
      have hl : raw1940step1Labels = raw1940step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1940step1 raw1940step1Labels = mixedMoment B raw1940step2 raw1940step2Labels := by
      have ha : raw1940step2 = raw1940step1 := by apply Matrix.ext; unfold raw1940step2 raw1940step1; decide +kernel
      have hl : raw1940step1Labels = labelEmbedding1 ∘ raw1940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1940step1 raw1940step1Labels raw1940step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3593 node3593Labels := by rfl

def raw1941 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1941step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1941 raw1941Labels = mixedMoment B node4967 node4967Labels := by
  calc
    mixedMoment B raw1941 raw1941Labels = mixedMoment B raw1941step0 raw1941step0Labels := by
      have ha : raw1941step0 = (fun i j => raw1941 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1941step0 raw1941; decide +kernel
      have hl : raw1941step0Labels = raw1941Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1941 raw1941Labels permutation152 permutation5
    mixedMoment B raw1941step0 raw1941step0Labels = mixedMoment B raw1941step1 raw1941step1Labels := by
      have ha : raw1941step1 = raw1941step0 := by apply Matrix.ext; unfold raw1941step1 raw1941step0; decide +kernel
      have hl : raw1941step0Labels = labelEmbedding8 ∘ raw1941step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1941step0 raw1941step0Labels raw1941step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4967 node4967Labels := by rfl

def raw1942 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1942step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1942 raw1942Labels = mixedMoment B node2814 node2814Labels := by
  calc
    mixedMoment B raw1942 raw1942Labels = mixedMoment B raw1942step0 raw1942step0Labels := by
      have ha : raw1942step0 = (fun i j => raw1942 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1942step0 raw1942; decide +kernel
      have hl : raw1942step0Labels = raw1942Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1942 raw1942Labels permutation152 permutation4
    _ = mixedMoment B node2814 node2814Labels := by rfl

def raw1943 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1943Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw1943step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1943step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw1943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1943step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw1943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1943 raw1943Labels = mixedMoment B node3585 node3585Labels := by
  calc
    mixedMoment B raw1943 raw1943Labels = mixedMoment B raw1943step0 raw1943step0Labels := by
      have ha : raw1943step0 = (fun i j => raw1943 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1943step0 raw1943; decide +kernel
      have hl : raw1943step0Labels = raw1943Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1943 raw1943Labels permutation152 permutation3
    mixedMoment B raw1943step0 raw1943step0Labels = mixedMoment B raw1943step1 raw1943step1Labels := by
      have ha : raw1943step1 = -raw1943step0 := by apply Matrix.ext; change ∀ i j, raw1943step1 i j = -(raw1943step0 i j); unfold raw1943step1 raw1943step0; decide +kernel
      have hl : raw1943step1Labels = raw1943step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1943step1 raw1943step1Labels = mixedMoment B raw1943step2 raw1943step2Labels := by
      have ha : raw1943step2 = raw1943step1 := by apply Matrix.ext; unfold raw1943step2 raw1943step1; decide +kernel
      have hl : raw1943step1Labels = labelEmbedding1 ∘ raw1943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1943step1 raw1943step1Labels raw1943step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3585 node3585Labels := by rfl

def raw1944 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1944step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1944step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1944 raw1944Labels = mixedMoment B node4968 node4968Labels := by
  calc
    mixedMoment B raw1944 raw1944Labels = mixedMoment B raw1944step0 raw1944step0Labels := by
      have ha : raw1944step0 = (fun i j => raw1944 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1944step0 raw1944; decide +kernel
      have hl : raw1944step0Labels = raw1944Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1944 raw1944Labels permutation152 permutation5
    mixedMoment B raw1944step0 raw1944step0Labels = mixedMoment B raw1944step1 raw1944step1Labels := by
      have ha : raw1944step1 = raw1944step0 := by apply Matrix.ext; unfold raw1944step1 raw1944step0; decide +kernel
      have hl : raw1944step0Labels = labelEmbedding8 ∘ raw1944step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1944step0 raw1944step0Labels raw1944step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4968 node4968Labels := by rfl

def raw1945 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1945 raw1945Labels = mixedMoment B node2809 node2809Labels := by
  calc
    mixedMoment B raw1945 raw1945Labels = mixedMoment B raw1945step0 raw1945step0Labels := by
      have ha : raw1945step0 = (fun i j => raw1945 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1945step0 raw1945; decide +kernel
      have hl : raw1945step0Labels = raw1945Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1945 raw1945Labels permutation164 permutation4
    _ = mixedMoment B node2809 node2809Labels := by rfl

def raw1946 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1946Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1946 raw1946Labels = mixedMoment B node3587 node3587Labels := by
  calc
    mixedMoment B raw1946 raw1946Labels = mixedMoment B raw1946step0 raw1946step0Labels := by
      have ha : raw1946step0 = (fun i j => raw1946 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1946step0 raw1946; decide +kernel
      have hl : raw1946step0Labels = raw1946Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1946 raw1946Labels permutation152 permutation3
    mixedMoment B raw1946step0 raw1946step0Labels = mixedMoment B raw1946step1 raw1946step1Labels := by
      have ha : raw1946step1 = -raw1946step0 := by apply Matrix.ext; change ∀ i j, raw1946step1 i j = -(raw1946step0 i j); unfold raw1946step1 raw1946step0; decide +kernel
      have hl : raw1946step1Labels = raw1946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1946step1 raw1946step1Labels = mixedMoment B raw1946step2 raw1946step2Labels := by
      have ha : raw1946step2 = raw1946step1 := by apply Matrix.ext; unfold raw1946step2 raw1946step1; decide +kernel
      have hl : raw1946step1Labels = labelEmbedding1 ∘ raw1946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1946step1 raw1946step1Labels raw1946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3587 node3587Labels := by rfl

def raw1947 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw1947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw1947step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw1947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1947 raw1947Labels = mixedMoment B node4969 node4969Labels := by
  calc
    mixedMoment B raw1947 raw1947Labels = mixedMoment B raw1947step0 raw1947step0Labels := by
      have ha : raw1947step0 = (fun i j => raw1947 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1947step0 raw1947; decide +kernel
      have hl : raw1947step0Labels = raw1947Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1947 raw1947Labels permutation152 permutation5
    mixedMoment B raw1947step0 raw1947step0Labels = mixedMoment B raw1947step1 raw1947step1Labels := by
      have ha : raw1947step1 = raw1947step0 := by apply Matrix.ext; unfold raw1947step1 raw1947step0; decide +kernel
      have hl : raw1947step0Labels = labelEmbedding8 ∘ raw1947step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1947step0 raw1947step0Labels raw1947step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4969 node4969Labels := by rfl

def raw1948 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw1948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1948 raw1948Labels = mixedMoment B node2804 node2804Labels := by
  calc
    mixedMoment B raw1948 raw1948Labels = mixedMoment B raw1948step0 raw1948step0Labels := by
      have ha : raw1948step0 = (fun i j => raw1948 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1948step0 raw1948; decide +kernel
      have hl : raw1948step0Labels = raw1948Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1948 raw1948Labels permutation164 permutation4
    _ = mixedMoment B node2804 node2804Labels := by rfl

def raw1949 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw1949Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw1949step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw1949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw1949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1949 raw1949Labels = mixedMoment B node3586 node3586Labels := by
  calc
    mixedMoment B raw1949 raw1949Labels = mixedMoment B raw1949step0 raw1949step0Labels := by
      have ha : raw1949step0 = (fun i j => raw1949 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1949step0 raw1949; decide +kernel
      have hl : raw1949step0Labels = raw1949Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1949 raw1949Labels permutation153 permutation3
    mixedMoment B raw1949step0 raw1949step0Labels = mixedMoment B raw1949step1 raw1949step1Labels := by
      have ha : raw1949step1 = -raw1949step0 := by apply Matrix.ext; change ∀ i j, raw1949step1 i j = -(raw1949step0 i j); unfold raw1949step1 raw1949step0; decide +kernel
      have hl : raw1949step1Labels = raw1949step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1949step1 raw1949step1Labels = mixedMoment B raw1949step2 raw1949step2Labels := by
      have ha : raw1949step2 = raw1949step1 := by apply Matrix.ext; unfold raw1949step2 raw1949step1; decide +kernel
      have hl : raw1949step1Labels = labelEmbedding1 ∘ raw1949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1949step1 raw1949step1Labels raw1949step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3586 node3586Labels := by rfl

def raw1950 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw1950step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw1950step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1950 raw1950Labels = mixedMoment B node4970 node4970Labels := by
  calc
    mixedMoment B raw1950 raw1950Labels = mixedMoment B raw1950step0 raw1950step0Labels := by
      have ha : raw1950step0 = (fun i j => raw1950 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1950step0 raw1950; decide +kernel
      have hl : raw1950step0Labels = raw1950Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1950 raw1950Labels permutation32 permutation5
    mixedMoment B raw1950step0 raw1950step0Labels = mixedMoment B raw1950step1 raw1950step1Labels := by
      have ha : raw1950step1 = raw1950step0 := by apply Matrix.ext; unfold raw1950step1 raw1950step0; decide +kernel
      have hl : raw1950step0Labels = labelEmbedding8 ∘ raw1950step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1950step0 raw1950step0Labels raw1950step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4970 node4970Labels := by rfl

def raw1951 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1951 raw1951Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw1951 raw1951Labels = mixedMoment B raw1951step0 raw1951step0Labels := by
      have ha : raw1951step0 = (fun i j => raw1951 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1951step0 raw1951; decide +kernel
      have hl : raw1951step0Labels = raw1951Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1951 raw1951Labels permutation32 permutation4
    _ = mixedMoment B node2815 node2815Labels := by rfl

def raw1952 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1952Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw1952step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw1952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw1952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1952 raw1952Labels = mixedMoment B node3588 node3588Labels := by
  calc
    mixedMoment B raw1952 raw1952Labels = mixedMoment B raw1952step0 raw1952step0Labels := by
      have ha : raw1952step0 = (fun i j => raw1952 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1952step0 raw1952; decide +kernel
      have hl : raw1952step0Labels = raw1952Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1952 raw1952Labels permutation32 permutation3
    mixedMoment B raw1952step0 raw1952step0Labels = mixedMoment B raw1952step1 raw1952step1Labels := by
      have ha : raw1952step1 = -raw1952step0 := by apply Matrix.ext; change ∀ i j, raw1952step1 i j = -(raw1952step0 i j); unfold raw1952step1 raw1952step0; decide +kernel
      have hl : raw1952step1Labels = raw1952step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1952step1 raw1952step1Labels = mixedMoment B raw1952step2 raw1952step2Labels := by
      have ha : raw1952step2 = raw1952step1 := by apply Matrix.ext; unfold raw1952step2 raw1952step1; decide +kernel
      have hl : raw1952step1Labels = labelEmbedding1 ∘ raw1952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1952step1 raw1952step1Labels raw1952step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3588 node3588Labels := by rfl

def raw1953 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1953step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1953 raw1953Labels = mixedMoment B node4971 node4971Labels := by
  calc
    mixedMoment B raw1953 raw1953Labels = mixedMoment B raw1953step0 raw1953step0Labels := by
      have ha : raw1953step0 = (fun i j => raw1953 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1953step0 raw1953; decide +kernel
      have hl : raw1953step0Labels = raw1953Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1953 raw1953Labels permutation152 permutation5
    mixedMoment B raw1953step0 raw1953step0Labels = mixedMoment B raw1953step1 raw1953step1Labels := by
      have ha : raw1953step1 = raw1953step0 := by apply Matrix.ext; unfold raw1953step1 raw1953step0; decide +kernel
      have hl : raw1953step0Labels = labelEmbedding8 ∘ raw1953step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1953step0 raw1953step0Labels raw1953step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4971 node4971Labels := by rfl

def raw1954 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1954 raw1954Labels = mixedMoment B node2807 node2807Labels := by
  calc
    mixedMoment B raw1954 raw1954Labels = mixedMoment B raw1954step0 raw1954step0Labels := by
      have ha : raw1954step0 = (fun i j => raw1954 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1954step0 raw1954; decide +kernel
      have hl : raw1954step0Labels = raw1954Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1954 raw1954Labels permutation160 permutation4
    _ = mixedMoment B node2807 node2807Labels := by rfl

def raw1955 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1955Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1]]
def raw1955step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw1955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw1955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1955 raw1955Labels = mixedMoment B node3590 node3590Labels := by
  calc
    mixedMoment B raw1955 raw1955Labels = mixedMoment B raw1955step0 raw1955step0Labels := by
      have ha : raw1955step0 = (fun i j => raw1955 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1955step0 raw1955; decide +kernel
      have hl : raw1955step0Labels = raw1955Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1955 raw1955Labels permutation156 permutation3
    mixedMoment B raw1955step0 raw1955step0Labels = mixedMoment B raw1955step1 raw1955step1Labels := by
      have ha : raw1955step1 = -raw1955step0 := by apply Matrix.ext; change ∀ i j, raw1955step1 i j = -(raw1955step0 i j); unfold raw1955step1 raw1955step0; decide +kernel
      have hl : raw1955step1Labels = raw1955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1955step1 raw1955step1Labels = mixedMoment B raw1955step2 raw1955step2Labels := by
      have ha : raw1955step2 = raw1955step1 := by apply Matrix.ext; unfold raw1955step2 raw1955step1; decide +kernel
      have hl : raw1955step1Labels = labelEmbedding1 ∘ raw1955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1955step1 raw1955step1Labels raw1955step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3590 node3590Labels := by rfl

def raw1956 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw1956step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw1956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1956 raw1956Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw1956 raw1956Labels = mixedMoment B raw1956step0 raw1956step0Labels := by
      have ha : raw1956step0 = (fun i j => raw1956 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1956step0 raw1956; decide +kernel
      have hl : raw1956step0Labels = raw1956Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1956 raw1956Labels permutation32 permutation5
    mixedMoment B raw1956step0 raw1956step0Labels = mixedMoment B raw1956step1 raw1956step1Labels := by
      have ha : raw1956step1 = raw1956step0 := by apply Matrix.ext; unfold raw1956step1 raw1956step0; decide +kernel
      have hl : raw1956step0Labels = labelEmbedding8 ∘ raw1956step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1956step0 raw1956step0Labels raw1956step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

def raw1957 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw1957step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1957 raw1957Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw1957 raw1957Labels = mixedMoment B raw1957step0 raw1957step0Labels := by
      have ha : raw1957step0 = (fun i j => raw1957 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1957step0 raw1957; decide +kernel
      have hl : raw1957step0Labels = raw1957Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1957 raw1957Labels permutation145 permutation4
    mixedMoment B raw1957step0 raw1957step0Labels = mixedMoment B raw1957step1 raw1957step1Labels := by
      have ha : raw1957step1 = -raw1957step0 := by apply Matrix.ext; change ∀ i j, raw1957step1 i j = -(raw1957step0 i j); unfold raw1957step1 raw1957step0; decide +kernel
      have hl : raw1957step1Labels = raw1957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2434 node2434Labels := by rfl

def raw1958 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1958Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1958step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1958 raw1958Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw1958 raw1958Labels = mixedMoment B raw1958step0 raw1958step0Labels := by
      have ha : raw1958step0 = (fun i j => raw1958 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1958step0 raw1958; decide +kernel
      have hl : raw1958step0Labels = raw1958Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1958 raw1958Labels permutation144 permutation6
    mixedMoment B raw1958step0 raw1958step0Labels = mixedMoment B raw1958step1 raw1958step1Labels := by
      have ha : raw1958step1 = raw1958step0 := by apply Matrix.ext; unfold raw1958step1 raw1958step0; decide +kernel
      have hl : raw1958step0Labels = labelEmbedding1 ∘ raw1958step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1958step0 raw1958step0Labels raw1958step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

def raw1959 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw1959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw1959step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw1959step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1959 raw1959Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw1959 raw1959Labels = mixedMoment B raw1959step0 raw1959step0Labels := by
      have ha : raw1959step0 = (fun i j => raw1959 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1959step0 raw1959; decide +kernel
      have hl : raw1959step0Labels = raw1959Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1959 raw1959Labels permutation32 permutation5
    mixedMoment B raw1959step0 raw1959step0Labels = mixedMoment B raw1959step1 raw1959step1Labels := by
      have ha : raw1959step1 = raw1959step0 := by apply Matrix.ext; unfold raw1959step1 raw1959step0; decide +kernel
      have hl : raw1959step0Labels = labelEmbedding8 ∘ raw1959step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1959step0 raw1959step0Labels raw1959step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4973 node4973Labels := by rfl

def raw1960 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw1960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1960 raw1960Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw1960 raw1960Labels = mixedMoment B raw1960step0 raw1960step0Labels := by
      have ha : raw1960step0 = (fun i j => raw1960 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1960step0 raw1960; decide +kernel
      have hl : raw1960step0Labels = raw1960Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1960 raw1960Labels permutation33 permutation4
    _ = mixedMoment B node2817 node2817Labels := by rfl

def raw1961 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw1961Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw1961step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw1961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw1961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1961 raw1961Labels = mixedMoment B node3591 node3591Labels := by
  calc
    mixedMoment B raw1961 raw1961Labels = mixedMoment B raw1961step0 raw1961step0Labels := by
      have ha : raw1961step0 = (fun i j => raw1961 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1961step0 raw1961; decide +kernel
      have hl : raw1961step0Labels = raw1961Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1961 raw1961Labels permutation32 permutation3
    mixedMoment B raw1961step0 raw1961step0Labels = mixedMoment B raw1961step1 raw1961step1Labels := by
      have ha : raw1961step1 = -raw1961step0 := by apply Matrix.ext; change ∀ i j, raw1961step1 i j = -(raw1961step0 i j); unfold raw1961step1 raw1961step0; decide +kernel
      have hl : raw1961step1Labels = raw1961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1961step1 raw1961step1Labels = mixedMoment B raw1961step2 raw1961step2Labels := by
      have ha : raw1961step2 = raw1961step1 := by apply Matrix.ext; unfold raw1961step2 raw1961step1; decide +kernel
      have hl : raw1961step1Labels = labelEmbedding1 ∘ raw1961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1961step1 raw1961step1Labels raw1961step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3591 node3591Labels := by rfl

def raw1962 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw1962step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw1962step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1962 raw1962Labels = mixedMoment B node4974 node4974Labels := by
  calc
    mixedMoment B raw1962 raw1962Labels = mixedMoment B raw1962step0 raw1962step0Labels := by
      have ha : raw1962step0 = (fun i j => raw1962 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1962step0 raw1962; decide +kernel
      have hl : raw1962step0Labels = raw1962Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1962 raw1962Labels permutation32 permutation5
    mixedMoment B raw1962step0 raw1962step0Labels = mixedMoment B raw1962step1 raw1962step1Labels := by
      have ha : raw1962step1 = raw1962step0 := by apply Matrix.ext; unfold raw1962step1 raw1962step0; decide +kernel
      have hl : raw1962step0Labels = labelEmbedding8 ∘ raw1962step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1962step0 raw1962step0Labels raw1962step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4974 node4974Labels := by rfl

def raw1963 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1963 raw1963Labels = mixedMoment B node2818 node2818Labels := by
  calc
    mixedMoment B raw1963 raw1963Labels = mixedMoment B raw1963step0 raw1963step0Labels := by
      have ha : raw1963step0 = (fun i j => raw1963 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1963step0 raw1963; decide +kernel
      have hl : raw1963step0Labels = raw1963Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1963 raw1963Labels permutation32 permutation4
    _ = mixedMoment B node2818 node2818Labels := by rfl

def raw1964 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1964Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1964step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1964 raw1964Labels = mixedMoment B node3592 node3592Labels := by
  calc
    mixedMoment B raw1964 raw1964Labels = mixedMoment B raw1964step0 raw1964step0Labels := by
      have ha : raw1964step0 = (fun i j => raw1964 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1964step0 raw1964; decide +kernel
      have hl : raw1964step0Labels = raw1964Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1964 raw1964Labels permutation32 permutation3
    mixedMoment B raw1964step0 raw1964step0Labels = mixedMoment B raw1964step1 raw1964step1Labels := by
      have ha : raw1964step1 = -raw1964step0 := by apply Matrix.ext; change ∀ i j, raw1964step1 i j = -(raw1964step0 i j); unfold raw1964step1 raw1964step0; decide +kernel
      have hl : raw1964step1Labels = raw1964step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1964step1 raw1964step1Labels = mixedMoment B raw1964step2 raw1964step2Labels := by
      have ha : raw1964step2 = raw1964step1 := by apply Matrix.ext; unfold raw1964step2 raw1964step1; decide +kernel
      have hl : raw1964step1Labels = labelEmbedding1 ∘ raw1964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1964step1 raw1964step1Labels raw1964step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3592 node3592Labels := by rfl

def raw1965 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw1965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw1965step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw1965step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1965 raw1965Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw1965 raw1965Labels = mixedMoment B raw1965step0 raw1965step0Labels := by
      have ha : raw1965step0 = (fun i j => raw1965 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1965step0 raw1965; decide +kernel
      have hl : raw1965step0Labels = raw1965Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1965 raw1965Labels permutation32 permutation5
    mixedMoment B raw1965step0 raw1965step0Labels = mixedMoment B raw1965step1 raw1965step1Labels := by
      have ha : raw1965step1 = raw1965step0 := by apply Matrix.ext; unfold raw1965step1 raw1965step0; decide +kernel
      have hl : raw1965step0Labels = labelEmbedding8 ∘ raw1965step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1965step0 raw1965step0Labels raw1965step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

def raw1966 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw1966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1966 raw1966Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw1966 raw1966Labels = mixedMoment B raw1966step0 raw1966step0Labels := by
      have ha : raw1966step0 = (fun i j => raw1966 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1966step0 raw1966; decide +kernel
      have hl : raw1966step0Labels = raw1966Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1966 raw1966Labels permutation33 permutation4
    _ = mixedMoment B node2813 node2813Labels := by rfl

def raw1967 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw1967Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw1967step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw1967step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw1967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1967 raw1967Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw1967 raw1967Labels = mixedMoment B raw1967step0 raw1967step0Labels := by
      have ha : raw1967step0 = (fun i j => raw1967 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1967step0 raw1967; decide +kernel
      have hl : raw1967step0Labels = raw1967Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1967 raw1967Labels permutation34 permutation3
    mixedMoment B raw1967step0 raw1967step0Labels = mixedMoment B raw1967step1 raw1967step1Labels := by
      have ha : raw1967step1 = -raw1967step0 := by apply Matrix.ext; change ∀ i j, raw1967step1 i j = -(raw1967step0 i j); unfold raw1967step1 raw1967step0; decide +kernel
      have hl : raw1967step1Labels = raw1967step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1967step1 raw1967step1Labels = mixedMoment B raw1967step2 raw1967step2Labels := by
      have ha : raw1967step2 = raw1967step1 := by apply Matrix.ext; unfold raw1967step2 raw1967step1; decide +kernel
      have hl : raw1967step1Labels = labelEmbedding1 ∘ raw1967step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1967step1 raw1967step1Labels raw1967step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

def raw1968 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw1968step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw1968step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1968 raw1968Labels = mixedMoment B node4978 node4978Labels := by
  calc
    mixedMoment B raw1968 raw1968Labels = mixedMoment B raw1968step0 raw1968step0Labels := by
      have ha : raw1968step0 = (fun i j => raw1968 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1968step0 raw1968; decide +kernel
      have hl : raw1968step0Labels = raw1968Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1968 raw1968Labels permutation32 permutation5
    mixedMoment B raw1968step0 raw1968step0Labels = mixedMoment B raw1968step1 raw1968step1Labels := by
      have ha : raw1968step1 = raw1968step0 := by apply Matrix.ext; unfold raw1968step1 raw1968step0; decide +kernel
      have hl : raw1968step0Labels = labelEmbedding8 ∘ raw1968step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1968step0 raw1968step0Labels raw1968step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4978 node4978Labels := by rfl

def raw1969 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1969 raw1969Labels = mixedMoment B node2805 node2805Labels := by
  calc
    mixedMoment B raw1969 raw1969Labels = mixedMoment B raw1969step0 raw1969step0Labels := by
      have ha : raw1969step0 = (fun i j => raw1969 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1969step0 raw1969; decide +kernel
      have hl : raw1969step0Labels = raw1969Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1969 raw1969Labels permutation32 permutation4
    _ = mixedMoment B node2805 node2805Labels := by rfl

def raw1970 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1970Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![0, -2, 2], ![-2, 1, 1]]
def raw1970step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]
def raw1970step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]
def raw1970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1970 raw1970Labels = mixedMoment B node3594 node3594Labels := by
  calc
    mixedMoment B raw1970 raw1970Labels = mixedMoment B raw1970step0 raw1970step0Labels := by
      have ha : raw1970step0 = (fun i j => raw1970 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1970step0 raw1970; decide +kernel
      have hl : raw1970step0Labels = raw1970Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1970 raw1970Labels permutation35 permutation3
    mixedMoment B raw1970step0 raw1970step0Labels = mixedMoment B raw1970step1 raw1970step1Labels := by
      have ha : raw1970step1 = -raw1970step0 := by apply Matrix.ext; change ∀ i j, raw1970step1 i j = -(raw1970step0 i j); unfold raw1970step1 raw1970step0; decide +kernel
      have hl : raw1970step1Labels = raw1970step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1970step1 raw1970step1Labels = mixedMoment B raw1970step2 raw1970step2Labels := by
      have ha : raw1970step2 = raw1970step1 := by apply Matrix.ext; unfold raw1970step2 raw1970step1; decide +kernel
      have hl : raw1970step1Labels = labelEmbedding1 ∘ raw1970step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1970step1 raw1970step1Labels raw1970step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3594 node3594Labels := by rfl

def raw1971 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 2, -2], ![-2, 3, -1]]
def raw1971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1971step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw1971step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw1971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1971 raw1971Labels = mixedMoment B node4979 node4979Labels := by
  calc
    mixedMoment B raw1971 raw1971Labels = mixedMoment B raw1971step0 raw1971step0Labels := by
      have ha : raw1971step0 = (fun i j => raw1971 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1971step0 raw1971; decide +kernel
      have hl : raw1971step0Labels = raw1971Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1971 raw1971Labels permutation8 permutation5
    mixedMoment B raw1971step0 raw1971step0Labels = mixedMoment B raw1971step1 raw1971step1Labels := by
      have ha : raw1971step1 = raw1971step0 := by apply Matrix.ext; unfold raw1971step1 raw1971step0; decide +kernel
      have hl : raw1971step0Labels = labelEmbedding8 ∘ raw1971step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1971step0 raw1971step0Labels raw1971step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4979 node4979Labels := by rfl

def raw1972 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 2, -2], ![-2, 3, -1]]
def raw1972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1972step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw1972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1972 raw1972Labels = mixedMoment B node2820 node2820Labels := by
  calc
    mixedMoment B raw1972 raw1972Labels = mixedMoment B raw1972step0 raw1972step0Labels := by
      have ha : raw1972step0 = (fun i j => raw1972 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1972step0 raw1972; decide +kernel
      have hl : raw1972step0Labels = raw1972Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1972 raw1972Labels permutation8 permutation4
    _ = mixedMoment B node2820 node2820Labels := by rfl

def raw1973 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, -2, 2], ![0, 2, -2], ![-2, 3, -1]]
def raw1973Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1973step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw1973step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw1973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1973 raw1973Labels = mixedMoment B node3596 node3596Labels := by
  calc
    mixedMoment B raw1973 raw1973Labels = mixedMoment B raw1973step0 raw1973step0Labels := by
      have ha : raw1973step0 = (fun i j => raw1973 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1973step0 raw1973; decide +kernel
      have hl : raw1973step0Labels = raw1973Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1973 raw1973Labels permutation31 permutation3
    mixedMoment B raw1973step0 raw1973step0Labels = mixedMoment B raw1973step1 raw1973step1Labels := by
      have ha : raw1973step1 = raw1973step0 := by apply Matrix.ext; unfold raw1973step1 raw1973step0; decide +kernel
      have hl : raw1973step0Labels = labelEmbedding1 ∘ raw1973step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1973step0 raw1973step0Labels raw1973step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3596 node3596Labels := by rfl

def raw1974 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw1974step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw1974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1974 raw1974Labels = mixedMoment B node4980 node4980Labels := by
  calc
    mixedMoment B raw1974 raw1974Labels = mixedMoment B raw1974step0 raw1974step0Labels := by
      have ha : raw1974step0 = (fun i j => raw1974 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1974step0 raw1974; decide +kernel
      have hl : raw1974step0Labels = raw1974Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1974 raw1974Labels permutation152 permutation5
    mixedMoment B raw1974step0 raw1974step0Labels = mixedMoment B raw1974step1 raw1974step1Labels := by
      have ha : raw1974step1 = raw1974step0 := by apply Matrix.ext; unfold raw1974step1 raw1974step0; decide +kernel
      have hl : raw1974step0Labels = labelEmbedding8 ∘ raw1974step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1974step0 raw1974step0Labels raw1974step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4980 node4980Labels := by rfl

def raw1975 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1975 raw1975Labels = mixedMoment B node2793 node2793Labels := by
  calc
    mixedMoment B raw1975 raw1975Labels = mixedMoment B raw1975step0 raw1975step0Labels := by
      have ha : raw1975step0 = (fun i j => raw1975 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1975step0 raw1975; decide +kernel
      have hl : raw1975step0Labels = raw1975Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1975 raw1975Labels permutation152 permutation4
    _ = mixedMoment B node2793 node2793Labels := by rfl

def raw1976 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1976Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1976step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1976step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1976step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1976 raw1976Labels = mixedMoment B node2366 node2366Labels := by
  calc
    mixedMoment B raw1976 raw1976Labels = mixedMoment B raw1976step0 raw1976step0Labels := by
      have ha : raw1976step0 = (fun i j => raw1976 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1976step0 raw1976; decide +kernel
      have hl : raw1976step0Labels = raw1976Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1976 raw1976Labels permutation265 permutation6
    mixedMoment B raw1976step0 raw1976step0Labels = mixedMoment B raw1976step1 raw1976step1Labels := by
      have ha : raw1976step1 = -raw1976step0 := by apply Matrix.ext; change ∀ i j, raw1976step1 i j = -(raw1976step0 i j); unfold raw1976step1 raw1976step0; decide +kernel
      have hl : raw1976step1Labels = raw1976step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1976step1 raw1976step1Labels = mixedMoment B raw1976step2 raw1976step2Labels := by
      have ha : raw1976step2 = raw1976step1 := by apply Matrix.ext; unfold raw1976step2 raw1976step1; decide +kernel
      have hl : raw1976step1Labels = labelEmbedding1 ∘ raw1976step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1976step1 raw1976step1Labels raw1976step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2366 node2366Labels := by rfl

def raw1977 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw1977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw1977step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw1977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1977 raw1977Labels = mixedMoment B node4981 node4981Labels := by
  calc
    mixedMoment B raw1977 raw1977Labels = mixedMoment B raw1977step0 raw1977step0Labels := by
      have ha : raw1977step0 = (fun i j => raw1977 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1977step0 raw1977; decide +kernel
      have hl : raw1977step0Labels = raw1977Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1977 raw1977Labels permutation152 permutation5
    mixedMoment B raw1977step0 raw1977step0Labels = mixedMoment B raw1977step1 raw1977step1Labels := by
      have ha : raw1977step1 = raw1977step0 := by apply Matrix.ext; unfold raw1977step1 raw1977step0; decide +kernel
      have hl : raw1977step0Labels = labelEmbedding8 ∘ raw1977step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1977step0 raw1977step0Labels raw1977step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4981 node4981Labels := by rfl

def raw1978 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw1978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1978 raw1978Labels = mixedMoment B node2791 node2791Labels := by
  calc
    mixedMoment B raw1978 raw1978Labels = mixedMoment B raw1978step0 raw1978step0Labels := by
      have ha : raw1978step0 = (fun i j => raw1978 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1978step0 raw1978; decide +kernel
      have hl : raw1978step0Labels = raw1978Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1978 raw1978Labels permutation164 permutation4
    _ = mixedMoment B node2791 node2791Labels := by rfl

def raw1979 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw1979Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1979step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1979step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1979step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1979 raw1979Labels = mixedMoment B node2364 node2364Labels := by
  calc
    mixedMoment B raw1979 raw1979Labels = mixedMoment B raw1979step0 raw1979step0Labels := by
      have ha : raw1979step0 = (fun i j => raw1979 (permutation277 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1979step0 raw1979; decide +kernel
      have hl : raw1979step0Labels = raw1979Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1979 raw1979Labels permutation277 permutation6
    mixedMoment B raw1979step0 raw1979step0Labels = mixedMoment B raw1979step1 raw1979step1Labels := by
      have ha : raw1979step1 = -raw1979step0 := by apply Matrix.ext; change ∀ i j, raw1979step1 i j = -(raw1979step0 i j); unfold raw1979step1 raw1979step0; decide +kernel
      have hl : raw1979step1Labels = raw1979step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1979step1 raw1979step1Labels = mixedMoment B raw1979step2 raw1979step2Labels := by
      have ha : raw1979step2 = raw1979step1 := by apply Matrix.ext; unfold raw1979step2 raw1979step1; decide +kernel
      have hl : raw1979step1Labels = labelEmbedding1 ∘ raw1979step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1979step1 raw1979step1Labels raw1979step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2364 node2364Labels := by rfl

def raw1980 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw1980step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw1980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1980 raw1980Labels = mixedMoment B node4982 node4982Labels := by
  calc
    mixedMoment B raw1980 raw1980Labels = mixedMoment B raw1980step0 raw1980step0Labels := by
      have ha : raw1980step0 = (fun i j => raw1980 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1980step0 raw1980; decide +kernel
      have hl : raw1980step0Labels = raw1980Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1980 raw1980Labels permutation32 permutation5
    mixedMoment B raw1980step0 raw1980step0Labels = mixedMoment B raw1980step1 raw1980step1Labels := by
      have ha : raw1980step1 = raw1980step0 := by apply Matrix.ext; unfold raw1980step1 raw1980step0; decide +kernel
      have hl : raw1980step0Labels = labelEmbedding8 ∘ raw1980step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1980step0 raw1980step0Labels raw1980step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4982 node4982Labels := by rfl

def raw1981 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![-3, 2, 1]]
def raw1981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw1981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1981 raw1981Labels = mixedMoment B node2421 node2421Labels := by
  calc
    mixedMoment B raw1981 raw1981Labels = mixedMoment B raw1981step0 raw1981step0Labels := by
      have ha : raw1981step0 = (fun i j => raw1981 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1981step0 raw1981; decide +kernel
      have hl : raw1981step0Labels = raw1981Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1981 raw1981Labels permutation145 permutation4
    mixedMoment B raw1981step0 raw1981step0Labels = mixedMoment B raw1981step1 raw1981step1Labels := by
      have ha : raw1981step1 = -raw1981step0 := by apply Matrix.ext; change ∀ i j, raw1981step1 i j = -(raw1981step0 i j); unfold raw1981step1 raw1981step0; decide +kernel
      have hl : raw1981step1Labels = raw1981step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2421 node2421Labels := by rfl

def raw1982 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1982Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1982step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1982 raw1982Labels = mixedMoment B node2367 node2367Labels := by
  calc
    mixedMoment B raw1982 raw1982Labels = mixedMoment B raw1982step0 raw1982step0Labels := by
      have ha : raw1982step0 = (fun i j => raw1982 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1982step0 raw1982; decide +kernel
      have hl : raw1982step0Labels = raw1982Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1982 raw1982Labels permutation56 permutation6
    mixedMoment B raw1982step0 raw1982step0Labels = mixedMoment B raw1982step1 raw1982step1Labels := by
      have ha : raw1982step1 = -raw1982step0 := by apply Matrix.ext; change ∀ i j, raw1982step1 i j = -(raw1982step0 i j); unfold raw1982step1 raw1982step0; decide +kernel
      have hl : raw1982step1Labels = raw1982step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1982step1 raw1982step1Labels = mixedMoment B raw1982step2 raw1982step2Labels := by
      have ha : raw1982step2 = raw1982step1 := by apply Matrix.ext; unfold raw1982step2 raw1982step1; decide +kernel
      have hl : raw1982step1Labels = labelEmbedding1 ∘ raw1982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1982step1 raw1982step1Labels raw1982step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2367 node2367Labels := by rfl

def raw1983 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![-1, 2, -1]]
def raw1983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw1983step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw1983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1983 raw1983Labels = mixedMoment B node4983 node4983Labels := by
  calc
    mixedMoment B raw1983 raw1983Labels = mixedMoment B raw1983step0 raw1983step0Labels := by
      have ha : raw1983step0 = (fun i j => raw1983 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1983step0 raw1983; decide +kernel
      have hl : raw1983step0Labels = raw1983Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1983 raw1983Labels permutation32 permutation5
    mixedMoment B raw1983step0 raw1983step0Labels = mixedMoment B raw1983step1 raw1983step1Labels := by
      have ha : raw1983step1 = raw1983step0 := by apply Matrix.ext; unfold raw1983step1 raw1983step0; decide +kernel
      have hl : raw1983step0Labels = labelEmbedding8 ∘ raw1983step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1983step0 raw1983step0Labels raw1983step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4983 node4983Labels := by rfl

def raw1984 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![-1, 2, -1]]
def raw1984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1984 raw1984Labels = mixedMoment B node2794 node2794Labels := by
  calc
    mixedMoment B raw1984 raw1984Labels = mixedMoment B raw1984step0 raw1984step0Labels := by
      have ha : raw1984step0 = (fun i j => raw1984 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1984step0 raw1984; decide +kernel
      have hl : raw1984step0Labels = raw1984Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1984 raw1984Labels permutation33 permutation4
    _ = mixedMoment B node2794 node2794Labels := by rfl

def raw1985 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 2, -2], ![-1, 2, -1]]
def raw1985Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1985step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1985step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1985 raw1985Labels = mixedMoment B node2368 node2368Labels := by
  calc
    mixedMoment B raw1985 raw1985Labels = mixedMoment B raw1985step0 raw1985step0Labels := by
      have ha : raw1985step0 = (fun i j => raw1985 (permutation57 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1985step0 raw1985; decide +kernel
      have hl : raw1985step0Labels = raw1985Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1985 raw1985Labels permutation57 permutation6
    mixedMoment B raw1985step0 raw1985step0Labels = mixedMoment B raw1985step1 raw1985step1Labels := by
      have ha : raw1985step1 = -raw1985step0 := by apply Matrix.ext; change ∀ i j, raw1985step1 i j = -(raw1985step0 i j); unfold raw1985step1 raw1985step0; decide +kernel
      have hl : raw1985step1Labels = raw1985step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1985step1 raw1985step1Labels = mixedMoment B raw1985step2 raw1985step2Labels := by
      have ha : raw1985step2 = raw1985step1 := by apply Matrix.ext; unfold raw1985step2 raw1985step1; decide +kernel
      have hl : raw1985step1Labels = labelEmbedding1 ∘ raw1985step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1985step1 raw1985step1Labels raw1985step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2368 node2368Labels := by rfl

def raw1986 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw1986step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw1986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw1986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1986 raw1986Labels = mixedMoment B node4984 node4984Labels := by
  calc
    mixedMoment B raw1986 raw1986Labels = mixedMoment B raw1986step0 raw1986step0Labels := by
      have ha : raw1986step0 = (fun i j => raw1986 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1986step0 raw1986; decide +kernel
      have hl : raw1986step0Labels = raw1986Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1986 raw1986Labels permutation32 permutation5
    mixedMoment B raw1986step0 raw1986step0Labels = mixedMoment B raw1986step1 raw1986step1Labels := by
      have ha : raw1986step1 = raw1986step0 := by apply Matrix.ext; unfold raw1986step1 raw1986step0; decide +kernel
      have hl : raw1986step0Labels = labelEmbedding8 ∘ raw1986step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1986step0 raw1986step0Labels raw1986step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4984 node4984Labels := by rfl

def raw1987 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1987 raw1987Labels = mixedMoment B node2792 node2792Labels := by
  calc
    mixedMoment B raw1987 raw1987Labels = mixedMoment B raw1987step0 raw1987step0Labels := by
      have ha : raw1987step0 = (fun i j => raw1987 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1987step0 raw1987; decide +kernel
      have hl : raw1987step0Labels = raw1987Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1987 raw1987Labels permutation32 permutation4
    _ = mixedMoment B node2792 node2792Labels := by rfl

def raw1988 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -2, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1988Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 2, -3], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1988step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1988 raw1988Labels = mixedMoment B node2365 node2365Labels := by
  calc
    mixedMoment B raw1988 raw1988Labels = mixedMoment B raw1988step0 raw1988step0Labels := by
      have ha : raw1988step0 = (fun i j => raw1988 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1988step0 raw1988; decide +kernel
      have hl : raw1988step0Labels = raw1988Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1988 raw1988Labels permutation56 permutation6
    mixedMoment B raw1988step0 raw1988step0Labels = mixedMoment B raw1988step1 raw1988step1Labels := by
      have ha : raw1988step1 = -raw1988step0 := by apply Matrix.ext; change ∀ i j, raw1988step1 i j = -(raw1988step0 i j); unfold raw1988step1 raw1988step0; decide +kernel
      have hl : raw1988step1Labels = raw1988step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1988step1 raw1988step1Labels = mixedMoment B raw1988step2 raw1988step2Labels := by
      have ha : raw1988step2 = raw1988step1 := by apply Matrix.ext; unfold raw1988step2 raw1988step1; decide +kernel
      have hl : raw1988step1Labels = labelEmbedding1 ∘ raw1988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1988step1 raw1988step1Labels raw1988step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2365 node2365Labels := by rfl

def raw1989 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1989step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1989 raw1989Labels = mixedMoment B node4985 node4985Labels := by
  calc
    mixedMoment B raw1989 raw1989Labels = mixedMoment B raw1989step0 raw1989step0Labels := by
      have ha : raw1989step0 = (fun i j => raw1989 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1989step0 raw1989; decide +kernel
      have hl : raw1989step0Labels = raw1989Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1989 raw1989Labels permutation152 permutation4
    mixedMoment B raw1989step0 raw1989step0Labels = mixedMoment B raw1989step1 raw1989step1Labels := by
      have ha : raw1989step1 = raw1989step0 := by apply Matrix.ext; unfold raw1989step1 raw1989step0; decide +kernel
      have hl : raw1989step0Labels = labelEmbedding7 ∘ raw1989step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1989step0 raw1989step0Labels raw1989step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4985 node4985Labels := by rfl

def raw1990 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1990 raw1990Labels = mixedMoment B node2370 node2370Labels := by
  calc
    mixedMoment B raw1990 raw1990Labels = mixedMoment B raw1990step0 raw1990step0Labels := by
      have ha : raw1990step0 = (fun i j => raw1990 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1990step0 raw1990; decide +kernel
      have hl : raw1990step0Labels = raw1990Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1990 raw1990Labels permutation152 permutation4
    _ = mixedMoment B node2370 node2370Labels := by rfl

def raw1991 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1991Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1991step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1991step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1991 raw1991Labels = mixedMoment B node3334 node3334Labels := by
  calc
    mixedMoment B raw1991 raw1991Labels = mixedMoment B raw1991step0 raw1991step0Labels := by
      have ha : raw1991step0 = (fun i j => raw1991 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1991step0 raw1991; decide +kernel
      have hl : raw1991step0Labels = raw1991Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1991 raw1991Labels permutation152 permutation6
    mixedMoment B raw1991step0 raw1991step0Labels = mixedMoment B raw1991step1 raw1991step1Labels := by
      have ha : raw1991step1 = -raw1991step0 := by apply Matrix.ext; change ∀ i j, raw1991step1 i j = -(raw1991step0 i j); unfold raw1991step1 raw1991step0; decide +kernel
      have hl : raw1991step1Labels = raw1991step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1991step1 raw1991step1Labels = mixedMoment B raw1991step2 raw1991step2Labels := by
      have ha : raw1991step2 = raw1991step1 := by apply Matrix.ext; unfold raw1991step2 raw1991step1; decide +kernel
      have hl : raw1991step1Labels = labelEmbedding1 ∘ raw1991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1991step1 raw1991step1Labels raw1991step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3334 node3334Labels := by rfl

def raw1992 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1992step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1992 raw1992Labels = mixedMoment B node4986 node4986Labels := by
  calc
    mixedMoment B raw1992 raw1992Labels = mixedMoment B raw1992step0 raw1992step0Labels := by
      have ha : raw1992step0 = (fun i j => raw1992 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1992step0 raw1992; decide +kernel
      have hl : raw1992step0Labels = raw1992Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1992 raw1992Labels permutation152 permutation4
    mixedMoment B raw1992step0 raw1992step0Labels = mixedMoment B raw1992step1 raw1992step1Labels := by
      have ha : raw1992step1 = raw1992step0 := by apply Matrix.ext; unfold raw1992step1 raw1992step0; decide +kernel
      have hl : raw1992step0Labels = labelEmbedding7 ∘ raw1992step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1992step0 raw1992step0Labels raw1992step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4986 node4986Labels := by rfl

def raw1993 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1993step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1993 raw1993Labels = mixedMoment B node2371 node2371Labels := by
  calc
    mixedMoment B raw1993 raw1993Labels = mixedMoment B raw1993step0 raw1993step0Labels := by
      have ha : raw1993step0 = (fun i j => raw1993 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1993step0 raw1993; decide +kernel
      have hl : raw1993step0Labels = raw1993Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1993 raw1993Labels permutation152 permutation4
    _ = mixedMoment B node2371 node2371Labels := by rfl

def raw1994 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1994Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1994step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1994step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1994step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1994 raw1994Labels = mixedMoment B node3335 node3335Labels := by
  calc
    mixedMoment B raw1994 raw1994Labels = mixedMoment B raw1994step0 raw1994step0Labels := by
      have ha : raw1994step0 = (fun i j => raw1994 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1994step0 raw1994; decide +kernel
      have hl : raw1994step0Labels = raw1994Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1994 raw1994Labels permutation152 permutation6
    mixedMoment B raw1994step0 raw1994step0Labels = mixedMoment B raw1994step1 raw1994step1Labels := by
      have ha : raw1994step1 = -raw1994step0 := by apply Matrix.ext; change ∀ i j, raw1994step1 i j = -(raw1994step0 i j); unfold raw1994step1 raw1994step0; decide +kernel
      have hl : raw1994step1Labels = raw1994step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1994step1 raw1994step1Labels = mixedMoment B raw1994step2 raw1994step2Labels := by
      have ha : raw1994step2 = raw1994step1 := by apply Matrix.ext; unfold raw1994step2 raw1994step1; decide +kernel
      have hl : raw1994step1Labels = labelEmbedding1 ∘ raw1994step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1994step1 raw1994step1Labels raw1994step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3335 node3335Labels := by rfl

def raw1995 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1995step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1995step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1995step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1995 raw1995Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw1995 raw1995Labels = mixedMoment B raw1995step0 raw1995step0Labels := by
      have ha : raw1995step0 = (fun i j => raw1995 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1995step0 raw1995; decide +kernel
      have hl : raw1995step0Labels = raw1995Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1995 raw1995Labels permutation152 permutation4
    mixedMoment B raw1995step0 raw1995step0Labels = mixedMoment B raw1995step1 raw1995step1Labels := by
      have ha : raw1995step1 = raw1995step0 := by apply Matrix.ext; unfold raw1995step1 raw1995step0; decide +kernel
      have hl : raw1995step0Labels = labelEmbedding7 ∘ raw1995step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1995step0 raw1995step0Labels raw1995step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

def raw1996 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1996 raw1996Labels = mixedMoment B node2372 node2372Labels := by
  calc
    mixedMoment B raw1996 raw1996Labels = mixedMoment B raw1996step0 raw1996step0Labels := by
      have ha : raw1996step0 = (fun i j => raw1996 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1996step0 raw1996; decide +kernel
      have hl : raw1996step0Labels = raw1996Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1996 raw1996Labels permutation152 permutation4
    _ = mixedMoment B node2372 node2372Labels := by rfl

def raw1997 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1997Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1997step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1997step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1997 raw1997Labels = mixedMoment B node3336 node3336Labels := by
  calc
    mixedMoment B raw1997 raw1997Labels = mixedMoment B raw1997step0 raw1997step0Labels := by
      have ha : raw1997step0 = (fun i j => raw1997 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1997step0 raw1997; decide +kernel
      have hl : raw1997step0Labels = raw1997Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1997 raw1997Labels permutation152 permutation6
    mixedMoment B raw1997step0 raw1997step0Labels = mixedMoment B raw1997step1 raw1997step1Labels := by
      have ha : raw1997step1 = -raw1997step0 := by apply Matrix.ext; change ∀ i j, raw1997step1 i j = -(raw1997step0 i j); unfold raw1997step1 raw1997step0; decide +kernel
      have hl : raw1997step1Labels = raw1997step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1997step1 raw1997step1Labels = mixedMoment B raw1997step2 raw1997step2Labels := by
      have ha : raw1997step2 = raw1997step1 := by apply Matrix.ext; unfold raw1997step2 raw1997step1; decide +kernel
      have hl : raw1997step1Labels = labelEmbedding1 ∘ raw1997step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1997step1 raw1997step1Labels raw1997step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3336 node3336Labels := by rfl

def raw1998 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![0, 2, -2]]
def raw1998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1998step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1998 raw1998Labels = mixedMoment B node4988 node4988Labels := by
  calc
    mixedMoment B raw1998 raw1998Labels = mixedMoment B raw1998step0 raw1998step0Labels := by
      have ha : raw1998step0 = (fun i j => raw1998 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1998step0 raw1998; decide +kernel
      have hl : raw1998step0Labels = raw1998Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1998 raw1998Labels permutation152 permutation4
    mixedMoment B raw1998step0 raw1998step0Labels = mixedMoment B raw1998step1 raw1998step1Labels := by
      have ha : raw1998step1 = raw1998step0 := by apply Matrix.ext; unfold raw1998step1 raw1998step0; decide +kernel
      have hl : raw1998step0Labels = labelEmbedding7 ∘ raw1998step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1998step0 raw1998step0Labels raw1998step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4988 node4988Labels := by rfl

def raw1999 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![0, 2, -2]]
def raw1999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1999 raw1999Labels = mixedMoment B node2373 node2373Labels := by
  calc
    mixedMoment B raw1999 raw1999Labels = mixedMoment B raw1999step0 raw1999step0Labels := by
      have ha : raw1999step0 = (fun i j => raw1999 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1999step0 raw1999; decide +kernel
      have hl : raw1999step0Labels = raw1999Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1999 raw1999Labels permutation152 permutation4
    _ = mixedMoment B node2373 node2373Labels := by rfl

def raw2000 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![0, 2, -2]]
def raw2000Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw2000step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw2000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2000step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw2000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2000 raw2000Labels = mixedMoment B node3332 node3332Labels := by
  calc
    mixedMoment B raw2000 raw2000Labels = mixedMoment B raw2000step0 raw2000step0Labels := by
      have ha : raw2000step0 = (fun i j => raw2000 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2000step0 raw2000; decide +kernel
      have hl : raw2000step0Labels = raw2000Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2000 raw2000Labels permutation152 permutation6
    mixedMoment B raw2000step0 raw2000step0Labels = mixedMoment B raw2000step1 raw2000step1Labels := by
      have ha : raw2000step1 = -raw2000step0 := by apply Matrix.ext; change ∀ i j, raw2000step1 i j = -(raw2000step0 i j); unfold raw2000step1 raw2000step0; decide +kernel
      have hl : raw2000step1Labels = raw2000step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2000step1 raw2000step1Labels = mixedMoment B raw2000step2 raw2000step2Labels := by
      have ha : raw2000step2 = raw2000step1 := by apply Matrix.ext; unfold raw2000step2 raw2000step1; decide +kernel
      have hl : raw2000step1Labels = labelEmbedding1 ∘ raw2000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2000step1 raw2000step1Labels raw2000step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3332 node3332Labels := by rfl

def raw2001 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]
def raw2001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw2001step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw2001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2001 raw2001Labels = mixedMoment B node4989 node4989Labels := by
  calc
    mixedMoment B raw2001 raw2001Labels = mixedMoment B raw2001step0 raw2001step0Labels := by
      have ha : raw2001step0 = (fun i j => raw2001 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2001step0 raw2001; decide +kernel
      have hl : raw2001step0Labels = raw2001Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2001 raw2001Labels permutation152 permutation4
    mixedMoment B raw2001step0 raw2001step0Labels = mixedMoment B raw2001step1 raw2001step1Labels := by
      have ha : raw2001step1 = raw2001step0 := by apply Matrix.ext; unfold raw2001step1 raw2001step0; decide +kernel
      have hl : raw2001step0Labels = labelEmbedding7 ∘ raw2001step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2001step0 raw2001step0Labels raw2001step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4989 node4989Labels := by rfl

def raw2002 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]
def raw2002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw2002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2002 raw2002Labels = mixedMoment B node2374 node2374Labels := by
  calc
    mixedMoment B raw2002 raw2002Labels = mixedMoment B raw2002step0 raw2002step0Labels := by
      have ha : raw2002step0 = (fun i j => raw2002 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2002step0 raw2002; decide +kernel
      have hl : raw2002step0Labels = raw2002Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2002 raw2002Labels permutation152 permutation4
    _ = mixedMoment B node2374 node2374Labels := by rfl

def raw2003 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]
def raw2003Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw2003step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw2003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2003 raw2003Labels = mixedMoment B node2413 node2413Labels := by
  calc
    mixedMoment B raw2003 raw2003Labels = mixedMoment B raw2003step0 raw2003step0Labels := by
      have ha : raw2003step0 = (fun i j => raw2003 (permutation664 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2003step0 raw2003; decide +kernel
      have hl : raw2003step0Labels = raw2003Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2003 raw2003Labels permutation664 permutation6
    mixedMoment B raw2003step0 raw2003step0Labels = mixedMoment B raw2003step1 raw2003step1Labels := by
      have ha : raw2003step1 = raw2003step0 := by apply Matrix.ext; unfold raw2003step1 raw2003step0; decide +kernel
      have hl : raw2003step0Labels = labelEmbedding1 ∘ raw2003step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2003step0 raw2003step0Labels raw2003step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2413 node2413Labels := by rfl

def raw2004 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![0, 2, -2]]
def raw2004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2004step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2004step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2004 raw2004Labels = mixedMoment B node4990 node4990Labels := by
  calc
    mixedMoment B raw2004 raw2004Labels = mixedMoment B raw2004step0 raw2004step0Labels := by
      have ha : raw2004step0 = (fun i j => raw2004 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2004step0 raw2004; decide +kernel
      have hl : raw2004step0Labels = raw2004Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2004 raw2004Labels permutation152 permutation4
    mixedMoment B raw2004step0 raw2004step0Labels = mixedMoment B raw2004step1 raw2004step1Labels := by
      have ha : raw2004step1 = raw2004step0 := by apply Matrix.ext; unfold raw2004step1 raw2004step0; decide +kernel
      have hl : raw2004step0Labels = labelEmbedding7 ∘ raw2004step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2004step0 raw2004step0Labels raw2004step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4990 node4990Labels := by rfl

def raw2005 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![0, 2, -2]]
def raw2005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2005 raw2005Labels = mixedMoment B node2375 node2375Labels := by
  calc
    mixedMoment B raw2005 raw2005Labels = mixedMoment B raw2005step0 raw2005step0Labels := by
      have ha : raw2005step0 = (fun i j => raw2005 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2005step0 raw2005; decide +kernel
      have hl : raw2005step0Labels = raw2005Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2005 raw2005Labels permutation152 permutation4
    _ = mixedMoment B node2375 node2375Labels := by rfl

def raw2006 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![0, 2, -2]]
def raw2006Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw2006step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2006step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2006 raw2006Labels = mixedMoment B node3333 node3333Labels := by
  calc
    mixedMoment B raw2006 raw2006Labels = mixedMoment B raw2006step0 raw2006step0Labels := by
      have ha : raw2006step0 = (fun i j => raw2006 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2006step0 raw2006; decide +kernel
      have hl : raw2006step0Labels = raw2006Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2006 raw2006Labels permutation152 permutation6
    mixedMoment B raw2006step0 raw2006step0Labels = mixedMoment B raw2006step1 raw2006step1Labels := by
      have ha : raw2006step1 = -raw2006step0 := by apply Matrix.ext; change ∀ i j, raw2006step1 i j = -(raw2006step0 i j); unfold raw2006step1 raw2006step0; decide +kernel
      have hl : raw2006step1Labels = raw2006step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2006step1 raw2006step1Labels = mixedMoment B raw2006step2 raw2006step2Labels := by
      have ha : raw2006step2 = raw2006step1 := by apply Matrix.ext; unfold raw2006step2 raw2006step1; decide +kernel
      have hl : raw2006step1Labels = labelEmbedding1 ∘ raw2006step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2006step1 raw2006step1Labels raw2006step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3333 node3333Labels := by rfl

def raw2007 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2007step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2007 raw2007Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw2007 raw2007Labels = mixedMoment B raw2007step0 raw2007step0Labels := by
      have ha : raw2007step0 = (fun i j => raw2007 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2007step0 raw2007; decide +kernel
      have hl : raw2007step0Labels = raw2007Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2007 raw2007Labels permutation152 permutation4
    mixedMoment B raw2007step0 raw2007step0Labels = mixedMoment B raw2007step1 raw2007step1Labels := by
      have ha : raw2007step1 = raw2007step0 := by apply Matrix.ext; unfold raw2007step1 raw2007step0; decide +kernel
      have hl : raw2007step0Labels = labelEmbedding7 ∘ raw2007step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2007step0 raw2007step0Labels raw2007step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw2008 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2008 raw2008Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw2008 raw2008Labels = mixedMoment B raw2008step0 raw2008step0Labels := by
      have ha : raw2008step0 = (fun i j => raw2008 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2008step0 raw2008; decide +kernel
      have hl : raw2008step0Labels = raw2008Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2008 raw2008Labels permutation152 permutation4
    _ = mixedMoment B node2382 node2382Labels := by rfl

def raw2009 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2009Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw2009step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2009step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2009step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2009step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2009 raw2009Labels = mixedMoment B node3340 node3340Labels := by
  calc
    mixedMoment B raw2009 raw2009Labels = mixedMoment B raw2009step0 raw2009step0Labels := by
      have ha : raw2009step0 = (fun i j => raw2009 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2009step0 raw2009; decide +kernel
      have hl : raw2009step0Labels = raw2009Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2009 raw2009Labels permutation158 permutation6
    mixedMoment B raw2009step0 raw2009step0Labels = mixedMoment B raw2009step1 raw2009step1Labels := by
      have ha : raw2009step1 = -raw2009step0 := by apply Matrix.ext; change ∀ i j, raw2009step1 i j = -(raw2009step0 i j); unfold raw2009step1 raw2009step0; decide +kernel
      have hl : raw2009step1Labels = raw2009step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2009step1 raw2009step1Labels = mixedMoment B raw2009step2 raw2009step2Labels := by
      have ha : raw2009step2 = raw2009step1 := by apply Matrix.ext; unfold raw2009step2 raw2009step1; decide +kernel
      have hl : raw2009step1Labels = labelEmbedding1 ∘ raw2009step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2009step1 raw2009step1Labels raw2009step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3340 node3340Labels := by rfl

def raw2010 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2010step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2010step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2010 raw2010Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw2010 raw2010Labels = mixedMoment B raw2010step0 raw2010step0Labels := by
      have ha : raw2010step0 = (fun i j => raw2010 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2010step0 raw2010; decide +kernel
      have hl : raw2010step0Labels = raw2010Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2010 raw2010Labels permutation152 permutation4
    mixedMoment B raw2010step0 raw2010step0Labels = mixedMoment B raw2010step1 raw2010step1Labels := by
      have ha : raw2010step1 = raw2010step0 := by apply Matrix.ext; unfold raw2010step1 raw2010step0; decide +kernel
      have hl : raw2010step0Labels = labelEmbedding7 ∘ raw2010step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2010step0 raw2010step0Labels raw2010step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

def raw2011 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2011 raw2011Labels = mixedMoment B node2383 node2383Labels := by
  calc
    mixedMoment B raw2011 raw2011Labels = mixedMoment B raw2011step0 raw2011step0Labels := by
      have ha : raw2011step0 = (fun i j => raw2011 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2011step0 raw2011; decide +kernel
      have hl : raw2011step0Labels = raw2011Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2011 raw2011Labels permutation152 permutation4
    _ = mixedMoment B node2383 node2383Labels := by rfl

def raw2012 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2012Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2012step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2012step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2012 raw2012Labels = mixedMoment B node3352 node3352Labels := by
  calc
    mixedMoment B raw2012 raw2012Labels = mixedMoment B raw2012step0 raw2012step0Labels := by
      have ha : raw2012step0 = (fun i j => raw2012 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2012step0 raw2012; decide +kernel
      have hl : raw2012step0Labels = raw2012Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2012 raw2012Labels permutation152 permutation6
    mixedMoment B raw2012step0 raw2012step0Labels = mixedMoment B raw2012step1 raw2012step1Labels := by
      have ha : raw2012step1 = -raw2012step0 := by apply Matrix.ext; change ∀ i j, raw2012step1 i j = -(raw2012step0 i j); unfold raw2012step1 raw2012step0; decide +kernel
      have hl : raw2012step1Labels = raw2012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2012step1 raw2012step1Labels = mixedMoment B raw2012step2 raw2012step2Labels := by
      have ha : raw2012step2 = raw2012step1 := by apply Matrix.ext; unfold raw2012step2 raw2012step1; decide +kernel
      have hl : raw2012step1Labels = labelEmbedding1 ∘ raw2012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2012step1 raw2012step1Labels raw2012step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3352 node3352Labels := by rfl

def raw2013 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2013step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2013 raw2013Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw2013 raw2013Labels = mixedMoment B raw2013step0 raw2013step0Labels := by
      have ha : raw2013step0 = (fun i j => raw2013 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2013step0 raw2013; decide +kernel
      have hl : raw2013step0Labels = raw2013Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2013 raw2013Labels permutation32 permutation4
    mixedMoment B raw2013step0 raw2013step0Labels = mixedMoment B raw2013step1 raw2013step1Labels := by
      have ha : raw2013step1 = raw2013step0 := by apply Matrix.ext; unfold raw2013step1 raw2013step0; decide +kernel
      have hl : raw2013step0Labels = labelEmbedding7 ∘ raw2013step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2013step0 raw2013step0Labels raw2013step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw2014 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2014 raw2014Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw2014 raw2014Labels = mixedMoment B raw2014step0 raw2014step0Labels := by
      have ha : raw2014step0 = (fun i j => raw2014 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2014step0 raw2014; decide +kernel
      have hl : raw2014step0Labels = raw2014Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2014 raw2014Labels permutation32 permutation4
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw2015 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2015Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw2015step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2015step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2015 raw2015Labels = mixedMoment B node3353 node3353Labels := by
  calc
    mixedMoment B raw2015 raw2015Labels = mixedMoment B raw2015step0 raw2015step0Labels := by
      have ha : raw2015step0 = (fun i j => raw2015 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2015step0 raw2015; decide +kernel
      have hl : raw2015step0Labels = raw2015Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2015 raw2015Labels permutation32 permutation6
    mixedMoment B raw2015step0 raw2015step0Labels = mixedMoment B raw2015step1 raw2015step1Labels := by
      have ha : raw2015step1 = -raw2015step0 := by apply Matrix.ext; change ∀ i j, raw2015step1 i j = -(raw2015step0 i j); unfold raw2015step1 raw2015step0; decide +kernel
      have hl : raw2015step1Labels = raw2015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2015step1 raw2015step1Labels = mixedMoment B raw2015step2 raw2015step2Labels := by
      have ha : raw2015step2 = raw2015step1 := by apply Matrix.ext; unfold raw2015step2 raw2015step1; decide +kernel
      have hl : raw2015step1Labels = labelEmbedding1 ∘ raw2015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2015step1 raw2015step1Labels raw2015step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3353 node3353Labels := by rfl

def raw2016 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2016step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2016step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2016 raw2016Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw2016 raw2016Labels = mixedMoment B raw2016step0 raw2016step0Labels := by
      have ha : raw2016step0 = (fun i j => raw2016 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2016step0 raw2016; decide +kernel
      have hl : raw2016step0Labels = raw2016Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2016 raw2016Labels permutation32 permutation4
    mixedMoment B raw2016step0 raw2016step0Labels = mixedMoment B raw2016step1 raw2016step1Labels := by
      have ha : raw2016step1 = raw2016step0 := by apply Matrix.ext; unfold raw2016step1 raw2016step0; decide +kernel
      have hl : raw2016step0Labels = labelEmbedding7 ∘ raw2016step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2016step0 raw2016step0Labels raw2016step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw2017 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2017 raw2017Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw2017 raw2017Labels = mixedMoment B raw2017step0 raw2017step0Labels := by
      have ha : raw2017step0 = (fun i j => raw2017 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2017step0 raw2017; decide +kernel
      have hl : raw2017step0Labels = raw2017Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2017 raw2017Labels permutation32 permutation4
    _ = mixedMoment B node2388 node2388Labels := by rfl

def raw2018 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2018Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw2018step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2018step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2018 raw2018Labels = mixedMoment B node3354 node3354Labels := by
  calc
    mixedMoment B raw2018 raw2018Labels = mixedMoment B raw2018step0 raw2018step0Labels := by
      have ha : raw2018step0 = (fun i j => raw2018 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2018step0 raw2018; decide +kernel
      have hl : raw2018step0Labels = raw2018Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2018 raw2018Labels permutation32 permutation6
    mixedMoment B raw2018step0 raw2018step0Labels = mixedMoment B raw2018step1 raw2018step1Labels := by
      have ha : raw2018step1 = -raw2018step0 := by apply Matrix.ext; change ∀ i j, raw2018step1 i j = -(raw2018step0 i j); unfold raw2018step1 raw2018step0; decide +kernel
      have hl : raw2018step1Labels = raw2018step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2018step1 raw2018step1Labels = mixedMoment B raw2018step2 raw2018step2Labels := by
      have ha : raw2018step2 = raw2018step1 := by apply Matrix.ext; unfold raw2018step2 raw2018step1; decide +kernel
      have hl : raw2018step1Labels = labelEmbedding1 ∘ raw2018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2018step1 raw2018step1Labels raw2018step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3354 node3354Labels := by rfl

def raw2019 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2019step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2019 raw2019Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw2019 raw2019Labels = mixedMoment B raw2019step0 raw2019step0Labels := by
      have ha : raw2019step0 = (fun i j => raw2019 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2019step0 raw2019; decide +kernel
      have hl : raw2019step0Labels = raw2019Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2019 raw2019Labels permutation152 permutation4
    mixedMoment B raw2019step0 raw2019step0Labels = mixedMoment B raw2019step1 raw2019step1Labels := by
      have ha : raw2019step1 = raw2019step0 := by apply Matrix.ext; unfold raw2019step1 raw2019step0; decide +kernel
      have hl : raw2019step0Labels = labelEmbedding7 ∘ raw2019step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2019step0 raw2019step0Labels raw2019step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw2020 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2020 raw2020Labels = mixedMoment B node2398 node2398Labels := by
  calc
    mixedMoment B raw2020 raw2020Labels = mixedMoment B raw2020step0 raw2020step0Labels := by
      have ha : raw2020step0 = (fun i j => raw2020 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2020step0 raw2020; decide +kernel
      have hl : raw2020step0Labels = raw2020Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2020 raw2020Labels permutation152 permutation4
    _ = mixedMoment B node2398 node2398Labels := by rfl

def raw2021 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2021Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2021step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2021step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2021step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2021step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2021step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2021 raw2021Labels = mixedMoment B node3341 node3341Labels := by
  calc
    mixedMoment B raw2021 raw2021Labels = mixedMoment B raw2021step0 raw2021step0Labels := by
      have ha : raw2021step0 = (fun i j => raw2021 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2021step0 raw2021; decide +kernel
      have hl : raw2021step0Labels = raw2021Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2021 raw2021Labels permutation152 permutation6
    mixedMoment B raw2021step0 raw2021step0Labels = mixedMoment B raw2021step1 raw2021step1Labels := by
      have ha : raw2021step1 = -raw2021step0 := by apply Matrix.ext; change ∀ i j, raw2021step1 i j = -(raw2021step0 i j); unfold raw2021step1 raw2021step0; decide +kernel
      have hl : raw2021step1Labels = raw2021step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2021step1 raw2021step1Labels = mixedMoment B raw2021step2 raw2021step2Labels := by
      have ha : raw2021step2 = raw2021step1 := by apply Matrix.ext; unfold raw2021step2 raw2021step1; decide +kernel
      have hl : raw2021step1Labels = labelEmbedding1 ∘ raw2021step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2021step1 raw2021step1Labels raw2021step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3341 node3341Labels := by rfl

def raw2022 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2022step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2022step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2022 raw2022Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw2022 raw2022Labels = mixedMoment B raw2022step0 raw2022step0Labels := by
      have ha : raw2022step0 = (fun i j => raw2022 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2022step0 raw2022; decide +kernel
      have hl : raw2022step0Labels = raw2022Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2022 raw2022Labels permutation32 permutation4
    mixedMoment B raw2022step0 raw2022step0Labels = mixedMoment B raw2022step1 raw2022step1Labels := by
      have ha : raw2022step1 = raw2022step0 := by apply Matrix.ext; unfold raw2022step1 raw2022step0; decide +kernel
      have hl : raw2022step0Labels = labelEmbedding7 ∘ raw2022step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2022step0 raw2022step0Labels raw2022step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw2023 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2023 raw2023Labels = mixedMoment B node2399 node2399Labels := by
  calc
    mixedMoment B raw2023 raw2023Labels = mixedMoment B raw2023step0 raw2023step0Labels := by
      have ha : raw2023step0 = (fun i j => raw2023 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2023step0 raw2023; decide +kernel
      have hl : raw2023step0Labels = raw2023Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2023 raw2023Labels permutation32 permutation4
    _ = mixedMoment B node2399 node2399Labels := by rfl

def raw2024 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2024Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw2024step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw2024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2024 raw2024Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw2024 raw2024Labels = mixedMoment B raw2024step0 raw2024step0Labels := by
      have ha : raw2024step0 = (fun i j => raw2024 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2024step0 raw2024; decide +kernel
      have hl : raw2024step0Labels = raw2024Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2024 raw2024Labels permutation151 permutation6
    mixedMoment B raw2024step0 raw2024step0Labels = mixedMoment B raw2024step1 raw2024step1Labels := by
      have ha : raw2024step1 = raw2024step0 := by apply Matrix.ext; unfold raw2024step1 raw2024step0; decide +kernel
      have hl : raw2024step0Labels = labelEmbedding1 ∘ raw2024step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2024step0 raw2024step0Labels raw2024step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2467 node2467Labels := by rfl

def raw2025 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2025step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2025 raw2025Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw2025 raw2025Labels = mixedMoment B raw2025step0 raw2025step0Labels := by
      have ha : raw2025step0 = (fun i j => raw2025 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2025step0 raw2025; decide +kernel
      have hl : raw2025step0Labels = raw2025Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2025 raw2025Labels permutation32 permutation4
    mixedMoment B raw2025step0 raw2025step0Labels = mixedMoment B raw2025step1 raw2025step1Labels := by
      have ha : raw2025step1 = raw2025step0 := by apply Matrix.ext; unfold raw2025step1 raw2025step0; decide +kernel
      have hl : raw2025step0Labels = labelEmbedding7 ∘ raw2025step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2025step0 raw2025step0Labels raw2025step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw2026 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2026 raw2026Labels = mixedMoment B node2400 node2400Labels := by
  calc
    mixedMoment B raw2026 raw2026Labels = mixedMoment B raw2026step0 raw2026step0Labels := by
      have ha : raw2026step0 = (fun i j => raw2026 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2026step0 raw2026; decide +kernel
      have hl : raw2026step0Labels = raw2026Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2026 raw2026Labels permutation32 permutation4
    _ = mixedMoment B node2400 node2400Labels := by rfl

def raw2027 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2027Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw2027step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2027step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2027 raw2027Labels = mixedMoment B node3344 node3344Labels := by
  calc
    mixedMoment B raw2027 raw2027Labels = mixedMoment B raw2027step0 raw2027step0Labels := by
      have ha : raw2027step0 = (fun i j => raw2027 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2027step0 raw2027; decide +kernel
      have hl : raw2027step0Labels = raw2027Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2027 raw2027Labels permutation32 permutation6
    mixedMoment B raw2027step0 raw2027step0Labels = mixedMoment B raw2027step1 raw2027step1Labels := by
      have ha : raw2027step1 = -raw2027step0 := by apply Matrix.ext; change ∀ i j, raw2027step1 i j = -(raw2027step0 i j); unfold raw2027step1 raw2027step0; decide +kernel
      have hl : raw2027step1Labels = raw2027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2027step1 raw2027step1Labels = mixedMoment B raw2027step2 raw2027step2Labels := by
      have ha : raw2027step2 = raw2027step1 := by apply Matrix.ext; unfold raw2027step2 raw2027step1; decide +kernel
      have hl : raw2027step1Labels = labelEmbedding1 ∘ raw2027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2027step1 raw2027step1Labels raw2027step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3344 node3344Labels := by rfl

def raw2028 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2028step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2028step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2028 raw2028Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw2028 raw2028Labels = mixedMoment B raw2028step0 raw2028step0Labels := by
      have ha : raw2028step0 = (fun i j => raw2028 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2028step0 raw2028; decide +kernel
      have hl : raw2028step0Labels = raw2028Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2028 raw2028Labels permutation32 permutation4
    mixedMoment B raw2028step0 raw2028step0Labels = mixedMoment B raw2028step1 raw2028step1Labels := by
      have ha : raw2028step1 = raw2028step0 := by apply Matrix.ext; unfold raw2028step1 raw2028step0; decide +kernel
      have hl : raw2028step0Labels = labelEmbedding7 ∘ raw2028step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2028step0 raw2028step0Labels raw2028step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw2029 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2029 raw2029Labels = mixedMoment B node2404 node2404Labels := by
  calc
    mixedMoment B raw2029 raw2029Labels = mixedMoment B raw2029step0 raw2029step0Labels := by
      have ha : raw2029step0 = (fun i j => raw2029 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2029step0 raw2029; decide +kernel
      have hl : raw2029step0Labels = raw2029Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2029 raw2029Labels permutation32 permutation4
    _ = mixedMoment B node2404 node2404Labels := by rfl

def raw2030 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2030Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2030step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2030step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2030 raw2030Labels = mixedMoment B node3357 node3357Labels := by
  calc
    mixedMoment B raw2030 raw2030Labels = mixedMoment B raw2030step0 raw2030step0Labels := by
      have ha : raw2030step0 = (fun i j => raw2030 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2030step0 raw2030; decide +kernel
      have hl : raw2030step0Labels = raw2030Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2030 raw2030Labels permutation33 permutation6
    mixedMoment B raw2030step0 raw2030step0Labels = mixedMoment B raw2030step1 raw2030step1Labels := by
      have ha : raw2030step1 = -raw2030step0 := by apply Matrix.ext; change ∀ i j, raw2030step1 i j = -(raw2030step0 i j); unfold raw2030step1 raw2030step0; decide +kernel
      have hl : raw2030step1Labels = raw2030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2030step1 raw2030step1Labels = mixedMoment B raw2030step2 raw2030step2Labels := by
      have ha : raw2030step2 = raw2030step1 := by apply Matrix.ext; unfold raw2030step2 raw2030step1; decide +kernel
      have hl : raw2030step1Labels = labelEmbedding1 ∘ raw2030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2030step1 raw2030step1Labels raw2030step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3357 node3357Labels := by rfl

def raw2031 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 1, -2], ![-1, 3, -2]]
def raw2031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2031step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw2031step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw2031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2031 raw2031Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw2031 raw2031Labels = mixedMoment B raw2031step0 raw2031step0Labels := by
      have ha : raw2031step0 = (fun i j => raw2031 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2031step0 raw2031; decide +kernel
      have hl : raw2031step0Labels = raw2031Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2031 raw2031Labels permutation8 permutation4
    mixedMoment B raw2031step0 raw2031step0Labels = mixedMoment B raw2031step1 raw2031step1Labels := by
      have ha : raw2031step1 = raw2031step0 := by apply Matrix.ext; unfold raw2031step1 raw2031step0; decide +kernel
      have hl : raw2031step0Labels = labelEmbedding7 ∘ raw2031step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2031step0 raw2031step0Labels raw2031step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5021 node5021Labels := by rfl

def raw2032 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 1, -2], ![-1, 3, -2]]
def raw2032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2032step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw2032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2032 raw2032Labels = mixedMoment B node2407 node2407Labels := by
  calc
    mixedMoment B raw2032 raw2032Labels = mixedMoment B raw2032step0 raw2032step0Labels := by
      have ha : raw2032step0 = (fun i j => raw2032 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2032step0 raw2032; decide +kernel
      have hl : raw2032step0Labels = raw2032Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2032 raw2032Labels permutation8 permutation4
    _ = mixedMoment B node2407 node2407Labels := by rfl

def raw2033 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![1, 1, -2], ![-1, 3, -2]]
def raw2033Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2033step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw2033step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw2033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2033 raw2033Labels = mixedMoment B node3360 node3360Labels := by
  calc
    mixedMoment B raw2033 raw2033Labels = mixedMoment B raw2033step0 raw2033step0Labels := by
      have ha : raw2033step0 = (fun i j => raw2033 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2033step0 raw2033; decide +kernel
      have hl : raw2033step0Labels = raw2033Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2033 raw2033Labels permutation31 permutation6
    mixedMoment B raw2033step0 raw2033step0Labels = mixedMoment B raw2033step1 raw2033step1Labels := by
      have ha : raw2033step1 = raw2033step0 := by apply Matrix.ext; unfold raw2033step1 raw2033step0; decide +kernel
      have hl : raw2033step0Labels = labelEmbedding1 ∘ raw2033step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2033step0 raw2033step0Labels raw2033step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3360 node3360Labels := by rfl

def raw2034 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 2, -3]]
def raw2034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2034step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw2034step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw2034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2034 raw2034Labels = mixedMoment B node5023 node5023Labels := by
  calc
    mixedMoment B raw2034 raw2034Labels = mixedMoment B raw2034step0 raw2034step0Labels := by
      have ha : raw2034step0 = (fun i j => raw2034 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2034step0 raw2034; decide +kernel
      have hl : raw2034step0Labels = raw2034Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2034 raw2034Labels permutation8 permutation4
    mixedMoment B raw2034step0 raw2034step0Labels = mixedMoment B raw2034step1 raw2034step1Labels := by
      have ha : raw2034step1 = raw2034step0 := by apply Matrix.ext; unfold raw2034step1 raw2034step0; decide +kernel
      have hl : raw2034step0Labels = labelEmbedding7 ∘ raw2034step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2034step0 raw2034step0Labels raw2034step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5023 node5023Labels := by rfl

def raw2035 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 2, -3]]
def raw2035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2035step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw2035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2035 raw2035Labels = mixedMoment B node2410 node2410Labels := by
  calc
    mixedMoment B raw2035 raw2035Labels = mixedMoment B raw2035step0 raw2035step0Labels := by
      have ha : raw2035step0 = (fun i j => raw2035 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2035step0 raw2035; decide +kernel
      have hl : raw2035step0Labels = raw2035Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2035 raw2035Labels permutation8 permutation4
    _ = mixedMoment B node2410 node2410Labels := by rfl

def raw2036 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 2, -3]]
def raw2036Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2036step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw2036step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw2036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2036 raw2036Labels = mixedMoment B node2410 node2410Labels := by
  calc
    mixedMoment B raw2036 raw2036Labels = mixedMoment B raw2036step0 raw2036step0Labels := by
      have ha : raw2036step0 = (fun i j => raw2036 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2036step0 raw2036; decide +kernel
      have hl : raw2036step0Labels = raw2036Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2036 raw2036Labels permutation31 permutation6
    mixedMoment B raw2036step0 raw2036step0Labels = mixedMoment B raw2036step1 raw2036step1Labels := by
      have ha : raw2036step1 = raw2036step0 := by apply Matrix.ext; unfold raw2036step1 raw2036step0; decide +kernel
      have hl : raw2036step0Labels = labelEmbedding1 ∘ raw2036step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2036step0 raw2036step0Labels raw2036step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2410 node2410Labels := by rfl

def raw2037 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw2037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw2037step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw2037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2037 raw2037Labels = mixedMoment B node5027 node5027Labels := by
  calc
    mixedMoment B raw2037 raw2037Labels = mixedMoment B raw2037step0 raw2037step0Labels := by
      have ha : raw2037step0 = (fun i j => raw2037 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2037step0 raw2037; decide +kernel
      have hl : raw2037step0Labels = raw2037Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2037 raw2037Labels permutation152 permutation4
    mixedMoment B raw2037step0 raw2037step0Labels = mixedMoment B raw2037step1 raw2037step1Labels := by
      have ha : raw2037step1 = raw2037step0 := by apply Matrix.ext; unfold raw2037step1 raw2037step0; decide +kernel
      have hl : raw2037step0Labels = labelEmbedding7 ∘ raw2037step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2037step0 raw2037step0Labels raw2037step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5027 node5027Labels := by rfl

def raw2038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw2038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw2038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2038 raw2038Labels = mixedMoment B node2416 node2416Labels := by
  calc
    mixedMoment B raw2038 raw2038Labels = mixedMoment B raw2038step0 raw2038step0Labels := by
      have ha : raw2038step0 = (fun i j => raw2038 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2038step0 raw2038; decide +kernel
      have hl : raw2038step0Labels = raw2038Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2038 raw2038Labels permutation152 permutation4
    _ = mixedMoment B node2416 node2416Labels := by rfl

def raw2039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw2039Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw2039step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw2039step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2039step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw2039step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2039 raw2039Labels = mixedMoment B node3427 node3427Labels := by
  calc
    mixedMoment B raw2039 raw2039Labels = mixedMoment B raw2039step0 raw2039step0Labels := by
      have ha : raw2039step0 = (fun i j => raw2039 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2039step0 raw2039; decide +kernel
      have hl : raw2039step0Labels = raw2039Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2039 raw2039Labels permutation153 permutation6
    mixedMoment B raw2039step0 raw2039step0Labels = mixedMoment B raw2039step1 raw2039step1Labels := by
      have ha : raw2039step1 = -raw2039step0 := by apply Matrix.ext; change ∀ i j, raw2039step1 i j = -(raw2039step0 i j); unfold raw2039step1 raw2039step0; decide +kernel
      have hl : raw2039step1Labels = raw2039step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2039step1 raw2039step1Labels = mixedMoment B raw2039step2 raw2039step2Labels := by
      have ha : raw2039step2 = raw2039step1 := by apply Matrix.ext; unfold raw2039step2 raw2039step1; decide +kernel
      have hl : raw2039step1Labels = labelEmbedding1 ∘ raw2039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2039step1 raw2039step1Labels raw2039step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3427 node3427Labels := by rfl

def raw2040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw2040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw2040step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw2040step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2040 raw2040Labels = mixedMoment B node5028 node5028Labels := by
  calc
    mixedMoment B raw2040 raw2040Labels = mixedMoment B raw2040step0 raw2040step0Labels := by
      have ha : raw2040step0 = (fun i j => raw2040 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2040step0 raw2040; decide +kernel
      have hl : raw2040step0Labels = raw2040Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2040 raw2040Labels permutation152 permutation4
    mixedMoment B raw2040step0 raw2040step0Labels = mixedMoment B raw2040step1 raw2040step1Labels := by
      have ha : raw2040step1 = raw2040step0 := by apply Matrix.ext; unfold raw2040step1 raw2040step0; decide +kernel
      have hl : raw2040step0Labels = labelEmbedding7 ∘ raw2040step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2040step0 raw2040step0Labels raw2040step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5028 node5028Labels := by rfl

def raw2041 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw2041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw2041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2041 raw2041Labels = mixedMoment B node2417 node2417Labels := by
  calc
    mixedMoment B raw2041 raw2041Labels = mixedMoment B raw2041step0 raw2041step0Labels := by
      have ha : raw2041step0 = (fun i j => raw2041 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2041step0 raw2041; decide +kernel
      have hl : raw2041step0Labels = raw2041Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2041 raw2041Labels permutation152 permutation4
    _ = mixedMoment B node2417 node2417Labels := by rfl

def raw2042 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw2042Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw2042step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw2042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2042 raw2042Labels = mixedMoment B node2445 node2445Labels := by
  calc
    mixedMoment B raw2042 raw2042Labels = mixedMoment B raw2042step0 raw2042step0Labels := by
      have ha : raw2042step0 = (fun i j => raw2042 (permutation662 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2042step0 raw2042; decide +kernel
      have hl : raw2042step0Labels = raw2042Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2042 raw2042Labels permutation662 permutation6
    mixedMoment B raw2042step0 raw2042step0Labels = mixedMoment B raw2042step1 raw2042step1Labels := by
      have ha : raw2042step1 = raw2042step0 := by apply Matrix.ext; unfold raw2042step1 raw2042step0; decide +kernel
      have hl : raw2042step0Labels = labelEmbedding1 ∘ raw2042step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2042step0 raw2042step0Labels raw2042step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2445 node2445Labels := by rfl

def raw2043 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2043step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2043step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2043 raw2043Labels = mixedMoment B node5030 node5030Labels := by
  calc
    mixedMoment B raw2043 raw2043Labels = mixedMoment B raw2043step0 raw2043step0Labels := by
      have ha : raw2043step0 = (fun i j => raw2043 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2043step0 raw2043; decide +kernel
      have hl : raw2043step0Labels = raw2043Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2043 raw2043Labels permutation152 permutation4
    mixedMoment B raw2043step0 raw2043step0Labels = mixedMoment B raw2043step1 raw2043step1Labels := by
      have ha : raw2043step1 = raw2043step0 := by apply Matrix.ext; unfold raw2043step1 raw2043step0; decide +kernel
      have hl : raw2043step0Labels = labelEmbedding7 ∘ raw2043step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2043step0 raw2043step0Labels raw2043step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5030 node5030Labels := by rfl

def raw2044 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2044 raw2044Labels = mixedMoment B node2419 node2419Labels := by
  calc
    mixedMoment B raw2044 raw2044Labels = mixedMoment B raw2044step0 raw2044step0Labels := by
      have ha : raw2044step0 = (fun i j => raw2044 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2044step0 raw2044; decide +kernel
      have hl : raw2044step0Labels = raw2044Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2044 raw2044Labels permutation152 permutation4
    _ = mixedMoment B node2419 node2419Labels := by rfl

def raw2045 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2045Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw2045step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw2045step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2045step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw2045step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2045 raw2045Labels = mixedMoment B node3425 node3425Labels := by
  calc
    mixedMoment B raw2045 raw2045Labels = mixedMoment B raw2045step0 raw2045step0Labels := by
      have ha : raw2045step0 = (fun i j => raw2045 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2045step0 raw2045; decide +kernel
      have hl : raw2045step0Labels = raw2045Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2045 raw2045Labels permutation154 permutation6
    mixedMoment B raw2045step0 raw2045step0Labels = mixedMoment B raw2045step1 raw2045step1Labels := by
      have ha : raw2045step1 = -raw2045step0 := by apply Matrix.ext; change ∀ i j, raw2045step1 i j = -(raw2045step0 i j); unfold raw2045step1 raw2045step0; decide +kernel
      have hl : raw2045step1Labels = raw2045step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2045step1 raw2045step1Labels = mixedMoment B raw2045step2 raw2045step2Labels := by
      have ha : raw2045step2 = raw2045step1 := by apply Matrix.ext; unfold raw2045step2 raw2045step1; decide +kernel
      have hl : raw2045step1Labels = labelEmbedding1 ∘ raw2045step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2045step1 raw2045step1Labels raw2045step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3425 node3425Labels := by rfl

def raw2046 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2046step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2046 raw2046Labels = mixedMoment B node5031 node5031Labels := by
  calc
    mixedMoment B raw2046 raw2046Labels = mixedMoment B raw2046step0 raw2046step0Labels := by
      have ha : raw2046step0 = (fun i j => raw2046 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2046step0 raw2046; decide +kernel
      have hl : raw2046step0Labels = raw2046Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2046 raw2046Labels permutation152 permutation4
    mixedMoment B raw2046step0 raw2046step0Labels = mixedMoment B raw2046step1 raw2046step1Labels := by
      have ha : raw2046step1 = raw2046step0 := by apply Matrix.ext; unfold raw2046step1 raw2046step0; decide +kernel
      have hl : raw2046step0Labels = labelEmbedding7 ∘ raw2046step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2046step0 raw2046step0Labels raw2046step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5031 node5031Labels := by rfl

def raw2047 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2047 raw2047Labels = mixedMoment B node2420 node2420Labels := by
  calc
    mixedMoment B raw2047 raw2047Labels = mixedMoment B raw2047step0 raw2047step0Labels := by
      have ha : raw2047step0 = (fun i j => raw2047 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2047step0 raw2047; decide +kernel
      have hl : raw2047step0Labels = raw2047Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2047 raw2047Labels permutation152 permutation4
    _ = mixedMoment B node2420 node2420Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
