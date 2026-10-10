import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33920 raw33920Labels = mixedMoment B node3135 node3135Labels := by
  calc
    mixedMoment B raw33920 raw33920Labels = mixedMoment B raw33920step0 raw33920step0Labels := by
      have ha : raw33920step0 = (fun i j => raw33920 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33920step0 raw33920; decide +kernel
      have hl : raw33920step0Labels = raw33920Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33920 raw33920Labels permutation154 permutation3
    _ = mixedMoment B node3135 node3135Labels := by rfl

def raw33921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33921 raw33921Labels = mixedMoment B node3164 node3164Labels := by
  calc
    mixedMoment B raw33921 raw33921Labels = mixedMoment B raw33921step0 raw33921step0Labels := by
      have ha : raw33921step0 = (fun i j => raw33921 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33921step0 raw33921; decide +kernel
      have hl : raw33921step0Labels = raw33921Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33921 raw33921Labels permutation178 permutation3
    _ = mixedMoment B node3164 node3164Labels := by rfl

def raw33922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33922step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw33922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33922 raw33922Labels = mixedMoment B node3207 node3207Labels := by
  calc
    mixedMoment B raw33922 raw33922Labels = mixedMoment B raw33922step0 raw33922step0Labels := by
      have hz : ∀ j, raw33922 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33922step0 = (fun i j => raw33922 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33922step0 raw33922; decide +kernel
      have hl : raw33922step0Labels = raw33922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33922 raw33922Labels permutation520 hz
    mixedMoment B raw33922step0 raw33922step0Labels = mixedMoment B raw33922step1 raw33922step1Labels := by
      have ha : raw33922step1 = (fun i j => raw33922step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33922step1 raw33922step0; decide +kernel
      have hl : raw33922step1Labels = raw33922step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33922step0 raw33922step0Labels permutation32 permutation3
    _ = mixedMoment B node3207 node3207Labels := by rfl

def raw33923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33923 raw33923Labels = mixedMoment B node3204 node3204Labels := by
  calc
    mixedMoment B raw33923 raw33923Labels = mixedMoment B raw33923step0 raw33923step0Labels := by
      have ha : raw33923step0 = (fun i j => raw33923 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33923step0 raw33923; decide +kernel
      have hl : raw33923step0Labels = raw33923Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33923 raw33923Labels permutation157 permutation3
    _ = mixedMoment B node3204 node3204Labels := by rfl

def raw33924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33924 raw33924Labels = mixedMoment B node1328 node1328Labels := by
  calc
    mixedMoment B raw33924 raw33924Labels = mixedMoment B raw33924step0 raw33924step0Labels := by
      have ha : raw33924step0 = (fun i j => raw33924 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33924step0 raw33924; decide +kernel
      have hl : raw33924step0Labels = raw33924Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33924 raw33924Labels permutation153 permutation3
    _ = mixedMoment B node1328 node1328Labels := by rfl

def raw33925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33925 raw33925Labels = mixedMoment B node3133 node3133Labels := by
  calc
    mixedMoment B raw33925 raw33925Labels = mixedMoment B raw33925step0 raw33925step0Labels := by
      have ha : raw33925step0 = (fun i j => raw33925 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33925step0 raw33925; decide +kernel
      have hl : raw33925step0Labels = raw33925Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33925 raw33925Labels permutation153 permutation3
    _ = mixedMoment B node3133 node3133Labels := by rfl

def raw33926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33926 raw33926Labels = mixedMoment B node3162 node3162Labels := by
  calc
    mixedMoment B raw33926 raw33926Labels = mixedMoment B raw33926step0 raw33926step0Labels := by
      have ha : raw33926step0 = (fun i j => raw33926 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33926step0 raw33926; decide +kernel
      have hl : raw33926step0Labels = raw33926Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33926 raw33926Labels permutation177 permutation3
    _ = mixedMoment B node3162 node3162Labels := by rfl

def raw33927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw33927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33927 raw33927Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw33927 raw33927Labels = mixedMoment B raw33927step0 raw33927step0Labels := by
      have ha : raw33927step0 = (fun i j => raw33927 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33927step0 raw33927; decide +kernel
      have hl : raw33927step0Labels = raw33927Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33927 raw33927Labels permutation153 permutation3
    _ = mixedMoment B node3199 node3199Labels := by rfl

def raw33928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33928 raw33928Labels = mixedMoment B node3203 node3203Labels := by
  calc
    mixedMoment B raw33928 raw33928Labels = mixedMoment B raw33928step0 raw33928step0Labels := by
      have ha : raw33928step0 = (fun i j => raw33928 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33928step0 raw33928; decide +kernel
      have hl : raw33928step0Labels = raw33928Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33928 raw33928Labels permutation153 permutation3
    _ = mixedMoment B node3203 node3203Labels := by rfl

def raw33929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33929 raw33929Labels = mixedMoment B node1327 node1327Labels := by
  calc
    mixedMoment B raw33929 raw33929Labels = mixedMoment B raw33929step0 raw33929step0Labels := by
      have ha : raw33929step0 = (fun i j => raw33929 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33929step0 raw33929; decide +kernel
      have hl : raw33929step0Labels = raw33929Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33929 raw33929Labels permutation152 permutation3
    _ = mixedMoment B node1327 node1327Labels := by rfl

def raw33930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw33930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw33930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33930 raw33930Labels = mixedMoment B node2423 node2423Labels := by
  calc
    mixedMoment B raw33930 raw33930Labels = mixedMoment B raw33930step0 raw33930step0Labels := by
      have ha : raw33930step0 = (fun i j => raw33930 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33930step0 raw33930; decide +kernel
      have hl : raw33930step0Labels = raw33930Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33930 raw33930Labels permutation688 permutation3
    mixedMoment B raw33930step0 raw33930step0Labels = mixedMoment B raw33930step1 raw33930step1Labels := by
      have ha : raw33930step1 = -raw33930step0 := by apply Matrix.ext; change ∀ i j, raw33930step1 i j = -(raw33930step0 i j); unfold raw33930step1 raw33930step0; decide +kernel
      have hl : raw33930step1Labels = raw33930step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2423 node2423Labels := by rfl

def raw33931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33931step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33931 raw33931Labels = mixedMoment B node2430 node2430Labels := by
  calc
    mixedMoment B raw33931 raw33931Labels = mixedMoment B raw33931step0 raw33931step0Labels := by
      have ha : raw33931step0 = (fun i j => raw33931 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33931step0 raw33931; decide +kernel
      have hl : raw33931step0Labels = raw33931Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33931 raw33931Labels permutation686 permutation3
    mixedMoment B raw33931step0 raw33931step0Labels = mixedMoment B raw33931step1 raw33931step1Labels := by
      have ha : raw33931step1 = -raw33931step0 := by apply Matrix.ext; change ∀ i j, raw33931step1 i j = -(raw33931step0 i j); unfold raw33931step1 raw33931step0; decide +kernel
      have hl : raw33931step1Labels = raw33931step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2430 node2430Labels := by rfl

def raw33932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw33932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33932 raw33932Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw33932 raw33932Labels = mixedMoment B raw33932step0 raw33932step0Labels := by
      have ha : raw33932step0 = (fun i j => raw33932 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33932step0 raw33932; decide +kernel
      have hl : raw33932step0Labels = raw33932Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33932 raw33932Labels permutation682 permutation3
    mixedMoment B raw33932step0 raw33932step0Labels = mixedMoment B raw33932step1 raw33932step1Labels := by
      have ha : raw33932step1 = -raw33932step0 := by apply Matrix.ext; change ∀ i j, raw33932step1 i j = -(raw33932step0 i j); unfold raw33932step1 raw33932step0; decide +kernel
      have hl : raw33932step1Labels = raw33932step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw33933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw33933step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33933step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33933 raw33933Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw33933 raw33933Labels = mixedMoment B raw33933step0 raw33933step0Labels := by
      have hz : ∀ j, raw33933 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33933step0 = (fun i j => raw33933 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33933step0 raw33933; decide +kernel
      have hl : raw33933step0Labels = raw33933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33933 raw33933Labels permutation520 hz
    mixedMoment B raw33933step0 raw33933step0Labels = mixedMoment B raw33933step1 raw33933step1Labels := by
      have ha : raw33933step1 = (fun i j => raw33933step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33933step1 raw33933step0; decide +kernel
      have hl : raw33933step1Labels = raw33933step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33933step0 raw33933step0Labels permutation151 permutation3
    mixedMoment B raw33933step1 raw33933step1Labels = mixedMoment B raw33933step2 raw33933step2Labels := by
      have ha : raw33933step2 = -raw33933step1 := by apply Matrix.ext; change ∀ i j, raw33933step2 i j = -(raw33933step1 i j); unfold raw33933step2 raw33933step1; decide +kernel
      have hl : raw33933step2Labels = raw33933step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw33934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33934Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33934step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33934step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33934step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33934 raw33934Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw33934 raw33934Labels = mixedMoment B raw33934step0 raw33934step0Labels := by
      have ha : raw33934step0 = (fun i j => raw33934 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33934step0 raw33934; decide +kernel
      have hl : raw33934step0Labels = raw33934Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33934 raw33934Labels permutation164 permutation7
    mixedMoment B raw33934step0 raw33934step0Labels = mixedMoment B raw33934step1 raw33934step1Labels := by
      have ha : raw33934step1 = -raw33934step0 := by apply Matrix.ext; change ∀ i j, raw33934step1 i j = -(raw33934step0 i j); unfold raw33934step1 raw33934step0; decide +kernel
      have hl : raw33934step1Labels = raw33934step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33934step1 raw33934step1Labels = mixedMoment B raw33934step2 raw33934step2Labels := by
      have ha : raw33934step2 = raw33934step1 := by apply Matrix.ext; unfold raw33934step2 raw33934step1; decide +kernel
      have hl : raw33934step1Labels = labelEmbedding1 ∘ raw33934step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33934step1 raw33934step1Labels raw33934step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw33935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33935Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33935step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33935step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33935step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33935step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33935 raw33935Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw33935 raw33935Labels = mixedMoment B raw33935step0 raw33935step0Labels := by
      have ha : raw33935step0 = (fun i j => raw33935 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33935step0 raw33935; decide +kernel
      have hl : raw33935step0Labels = raw33935Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33935 raw33935Labels permutation164 permutation7
    mixedMoment B raw33935step0 raw33935step0Labels = mixedMoment B raw33935step1 raw33935step1Labels := by
      have ha : raw33935step1 = -raw33935step0 := by apply Matrix.ext; change ∀ i j, raw33935step1 i j = -(raw33935step0 i j); unfold raw33935step1 raw33935step0; decide +kernel
      have hl : raw33935step1Labels = raw33935step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33935step1 raw33935step1Labels = mixedMoment B raw33935step2 raw33935step2Labels := by
      have ha : raw33935step2 = raw33935step1 := by apply Matrix.ext; unfold raw33935step2 raw33935step1; decide +kernel
      have hl : raw33935step1Labels = labelEmbedding1 ∘ raw33935step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33935step1 raw33935step1Labels raw33935step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw33936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33936Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33936step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33936step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33936step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33936step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33936 raw33936Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw33936 raw33936Labels = mixedMoment B raw33936step0 raw33936step0Labels := by
      have ha : raw33936step0 = (fun i j => raw33936 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33936step0 raw33936; decide +kernel
      have hl : raw33936step0Labels = raw33936Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33936 raw33936Labels permutation164 permutation7
    mixedMoment B raw33936step0 raw33936step0Labels = mixedMoment B raw33936step1 raw33936step1Labels := by
      have ha : raw33936step1 = -raw33936step0 := by apply Matrix.ext; change ∀ i j, raw33936step1 i j = -(raw33936step0 i j); unfold raw33936step1 raw33936step0; decide +kernel
      have hl : raw33936step1Labels = raw33936step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33936step1 raw33936step1Labels = mixedMoment B raw33936step2 raw33936step2Labels := by
      have ha : raw33936step2 = raw33936step1 := by apply Matrix.ext; unfold raw33936step2 raw33936step1; decide +kernel
      have hl : raw33936step1Labels = labelEmbedding1 ∘ raw33936step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33936step1 raw33936step1Labels raw33936step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2720 node2720Labels := by rfl

def raw33937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33937Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33937step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33937step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33937step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33937step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33937step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33937 raw33937Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw33937 raw33937Labels = mixedMoment B raw33937step0 raw33937step0Labels := by
      have hz : ∀ j, raw33937 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33937step0 = (fun i j => raw33937 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33937step0 raw33937; decide +kernel
      have hl : raw33937step0Labels = raw33937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33937 raw33937Labels permutation520 hz
    mixedMoment B raw33937step0 raw33937step0Labels = mixedMoment B raw33937step1 raw33937step1Labels := by
      have ha : raw33937step1 = (fun i j => raw33937step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33937step1 raw33937step0; decide +kernel
      have hl : raw33937step1Labels = raw33937step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33937step0 raw33937step0Labels permutation32 permutation7
    mixedMoment B raw33937step1 raw33937step1Labels = mixedMoment B raw33937step2 raw33937step2Labels := by
      have ha : raw33937step2 = -raw33937step1 := by apply Matrix.ext; change ∀ i j, raw33937step2 i j = -(raw33937step1 i j); unfold raw33937step2 raw33937step1; decide +kernel
      have hl : raw33937step2Labels = raw33937step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33937step2 raw33937step2Labels = mixedMoment B raw33937step3 raw33937step3Labels := by
      have ha : raw33937step3 = raw33937step2 := by apply Matrix.ext; unfold raw33937step3 raw33937step2; decide +kernel
      have hl : raw33937step2Labels = labelEmbedding1 ∘ raw33937step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33937step2 raw33937step2Labels raw33937step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw33938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33938Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33938step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33938step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33938 raw33938Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw33938 raw33938Labels = mixedMoment B raw33938step0 raw33938step0Labels := by
      have ha : raw33938step0 = (fun i j => raw33938 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33938step0 raw33938; decide +kernel
      have hl : raw33938step0Labels = raw33938Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33938 raw33938Labels permutation164 permutation7
    mixedMoment B raw33938step0 raw33938step0Labels = mixedMoment B raw33938step1 raw33938step1Labels := by
      have ha : raw33938step1 = -raw33938step0 := by apply Matrix.ext; change ∀ i j, raw33938step1 i j = -(raw33938step0 i j); unfold raw33938step1 raw33938step0; decide +kernel
      have hl : raw33938step1Labels = raw33938step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33938step1 raw33938step1Labels = mixedMoment B raw33938step2 raw33938step2Labels := by
      have ha : raw33938step2 = raw33938step1 := by apply Matrix.ext; unfold raw33938step2 raw33938step1; decide +kernel
      have hl : raw33938step1Labels = labelEmbedding1 ∘ raw33938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33938step1 raw33938step1Labels raw33938step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw33939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33939step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33939step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33939 raw33939Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw33939 raw33939Labels = mixedMoment B raw33939step0 raw33939step0Labels := by
      have hz : ∀ j, raw33939 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33939step0 = (fun i j => raw33939 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33939step0 raw33939; decide +kernel
      have hl : raw33939step0Labels = raw33939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33939 raw33939Labels permutation265 hz
    mixedMoment B raw33939step0 raw33939step0Labels = mixedMoment B raw33939step1 raw33939step1Labels := by
      have ha : raw33939step1 = (fun i j => raw33939step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33939step1 raw33939step0; decide +kernel
      have hl : raw33939step1Labels = raw33939step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33939step0 raw33939step0Labels permutation44 permutation7
    mixedMoment B raw33939step1 raw33939step1Labels = mixedMoment B raw33939step2 raw33939step2Labels := by
      have ha : raw33939step2 = -raw33939step1 := by apply Matrix.ext; change ∀ i j, raw33939step2 i j = -(raw33939step1 i j); unfold raw33939step2 raw33939step1; decide +kernel
      have hl : raw33939step2Labels = raw33939step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33939step2 raw33939step2Labels = mixedMoment B raw33939step3 raw33939step3Labels := by
      have ha : raw33939step3 = raw33939step2 := by apply Matrix.ext; unfold raw33939step3 raw33939step2; decide +kernel
      have hl : raw33939step2Labels = labelEmbedding1 ∘ raw33939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33939step2 raw33939step2Labels raw33939step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw33940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33940step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33940step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33940step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33940step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33940 raw33940Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw33940 raw33940Labels = mixedMoment B raw33940step0 raw33940step0Labels := by
      have hz : ∀ j, raw33940 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33940step0 = (fun i j => raw33940 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33940step0 raw33940; decide +kernel
      have hl : raw33940step0Labels = raw33940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33940 raw33940Labels permutation265 hz
    mixedMoment B raw33940step0 raw33940step0Labels = mixedMoment B raw33940step1 raw33940step1Labels := by
      have ha : raw33940step1 = (fun i j => raw33940step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33940step1 raw33940step0; decide +kernel
      have hl : raw33940step1Labels = raw33940step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33940step0 raw33940step0Labels permutation44 permutation7
    mixedMoment B raw33940step1 raw33940step1Labels = mixedMoment B raw33940step2 raw33940step2Labels := by
      have ha : raw33940step2 = -raw33940step1 := by apply Matrix.ext; change ∀ i j, raw33940step2 i j = -(raw33940step1 i j); unfold raw33940step2 raw33940step1; decide +kernel
      have hl : raw33940step2Labels = raw33940step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33940step2 raw33940step2Labels = mixedMoment B raw33940step3 raw33940step3Labels := by
      have ha : raw33940step3 = raw33940step2 := by apply Matrix.ext; unfold raw33940step3 raw33940step2; decide +kernel
      have hl : raw33940step2Labels = labelEmbedding1 ∘ raw33940step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33940step2 raw33940step2Labels raw33940step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw33941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33941step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33941step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33941step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33941step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33941step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33941 raw33941Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw33941 raw33941Labels = mixedMoment B raw33941step0 raw33941step0Labels := by
      have hz : ∀ j, raw33941 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33941step0 = (fun i j => raw33941 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33941step0 raw33941; decide +kernel
      have hl : raw33941step0Labels = raw33941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33941 raw33941Labels permutation265 hz
    mixedMoment B raw33941step0 raw33941step0Labels = mixedMoment B raw33941step1 raw33941step1Labels := by
      have ha : raw33941step1 = (fun i j => raw33941step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33941step1 raw33941step0; decide +kernel
      have hl : raw33941step1Labels = raw33941step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33941step0 raw33941step0Labels permutation44 permutation7
    mixedMoment B raw33941step1 raw33941step1Labels = mixedMoment B raw33941step2 raw33941step2Labels := by
      have ha : raw33941step2 = -raw33941step1 := by apply Matrix.ext; change ∀ i j, raw33941step2 i j = -(raw33941step1 i j); unfold raw33941step2 raw33941step1; decide +kernel
      have hl : raw33941step2Labels = raw33941step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33941step2 raw33941step2Labels = mixedMoment B raw33941step3 raw33941step3Labels := by
      have ha : raw33941step3 = raw33941step2 := by apply Matrix.ext; unfold raw33941step3 raw33941step2; decide +kernel
      have hl : raw33941step2Labels = labelEmbedding1 ∘ raw33941step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33941step2 raw33941step2Labels raw33941step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw33942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33942step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33942step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33942step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33942step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33942step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33942 raw33942Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw33942 raw33942Labels = mixedMoment B raw33942step0 raw33942step0Labels := by
      have hz : ∀ j, raw33942 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33942step0 = (fun i j => raw33942 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33942step0 raw33942; decide +kernel
      have hl : raw33942step0Labels = raw33942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33942 raw33942Labels permutation520 hz
    mixedMoment B raw33942step0 raw33942step0Labels = mixedMoment B raw33942step1 raw33942step1Labels := by
      have hz : ∀ j, raw33942step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw33942step1 = (fun i j => raw33942step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw33942step1 raw33942step0; decide +kernel
      have hl : raw33942step1Labels = raw33942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33942step0 raw33942step0Labels permutation56 hz
    mixedMoment B raw33942step1 raw33942step1Labels = mixedMoment B raw33942step2 raw33942step2Labels := by
      have ha : raw33942step2 = (fun i j => raw33942step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33942step2 raw33942step1; decide +kernel
      have hl : raw33942step2Labels = raw33942step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33942step1 raw33942step1Labels permutation8 permutation7
    mixedMoment B raw33942step2 raw33942step2Labels = mixedMoment B raw33942step3 raw33942step3Labels := by
      have ha : raw33942step3 = -raw33942step2 := by apply Matrix.ext; change ∀ i j, raw33942step3 i j = -(raw33942step2 i j); unfold raw33942step3 raw33942step2; decide +kernel
      have hl : raw33942step3Labels = raw33942step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33942step3 raw33942step3Labels = mixedMoment B raw33942step4 raw33942step4Labels := by
      have ha : raw33942step4 = raw33942step3 := by apply Matrix.ext; unfold raw33942step4 raw33942step3; decide +kernel
      have hl : raw33942step3Labels = labelEmbedding1 ∘ raw33942step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33942step3 raw33942step3Labels raw33942step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw33943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33943step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33943step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33943step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33943 raw33943Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw33943 raw33943Labels = mixedMoment B raw33943step0 raw33943step0Labels := by
      have hz : ∀ j, raw33943 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33943step0 = (fun i j => raw33943 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33943step0 raw33943; decide +kernel
      have hl : raw33943step0Labels = raw33943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33943 raw33943Labels permutation265 hz
    mixedMoment B raw33943step0 raw33943step0Labels = mixedMoment B raw33943step1 raw33943step1Labels := by
      have ha : raw33943step1 = (fun i j => raw33943step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33943step1 raw33943step0; decide +kernel
      have hl : raw33943step1Labels = raw33943step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33943step0 raw33943step0Labels permutation44 permutation7
    mixedMoment B raw33943step1 raw33943step1Labels = mixedMoment B raw33943step2 raw33943step2Labels := by
      have ha : raw33943step2 = -raw33943step1 := by apply Matrix.ext; change ∀ i j, raw33943step2 i j = -(raw33943step1 i j); unfold raw33943step2 raw33943step1; decide +kernel
      have hl : raw33943step2Labels = raw33943step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33943step2 raw33943step2Labels = mixedMoment B raw33943step3 raw33943step3Labels := by
      have ha : raw33943step3 = raw33943step2 := by apply Matrix.ext; unfold raw33943step3 raw33943step2; decide +kernel
      have hl : raw33943step2Labels = labelEmbedding1 ∘ raw33943step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33943step2 raw33943step2Labels raw33943step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw33944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33944step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33944 raw33944Labels = mixedMoment B node1673 node1673Labels := by
  calc
    mixedMoment B raw33944 raw33944Labels = mixedMoment B raw33944step0 raw33944step0Labels := by
      have ha : raw33944step0 = (fun i j => raw33944 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33944step0 raw33944; decide +kernel
      have hl : raw33944step0Labels = raw33944Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33944 raw33944Labels permutation164 permutation7
    mixedMoment B raw33944step0 raw33944step0Labels = mixedMoment B raw33944step1 raw33944step1Labels := by
      have ha : raw33944step1 = -raw33944step0 := by apply Matrix.ext; change ∀ i j, raw33944step1 i j = -(raw33944step0 i j); unfold raw33944step1 raw33944step0; decide +kernel
      have hl : raw33944step1Labels = raw33944step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33944step1 raw33944step1Labels = mixedMoment B raw33944step2 raw33944step2Labels := by
      have ha : raw33944step2 = raw33944step1 := by apply Matrix.ext; unfold raw33944step2 raw33944step1; decide +kernel
      have hl : raw33944step1Labels = labelEmbedding1 ∘ raw33944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33944step1 raw33944step1Labels raw33944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1673 node1673Labels := by rfl

def raw33945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33945step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33945step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33945step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33945 raw33945Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw33945 raw33945Labels = mixedMoment B raw33945step0 raw33945step0Labels := by
      have ha : raw33945step0 = (fun i j => raw33945 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33945step0 raw33945; decide +kernel
      have hl : raw33945step0Labels = raw33945Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33945 raw33945Labels permutation164 permutation7
    mixedMoment B raw33945step0 raw33945step0Labels = mixedMoment B raw33945step1 raw33945step1Labels := by
      have ha : raw33945step1 = -raw33945step0 := by apply Matrix.ext; change ∀ i j, raw33945step1 i j = -(raw33945step0 i j); unfold raw33945step1 raw33945step0; decide +kernel
      have hl : raw33945step1Labels = raw33945step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33945step1 raw33945step1Labels = mixedMoment B raw33945step2 raw33945step2Labels := by
      have ha : raw33945step2 = raw33945step1 := by apply Matrix.ext; unfold raw33945step2 raw33945step1; decide +kernel
      have hl : raw33945step1Labels = labelEmbedding1 ∘ raw33945step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33945step1 raw33945step1Labels raw33945step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

def raw33946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33946 raw33946Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw33946 raw33946Labels = mixedMoment B raw33946step0 raw33946step0Labels := by
      have ha : raw33946step0 = (fun i j => raw33946 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33946step0 raw33946; decide +kernel
      have hl : raw33946step0Labels = raw33946Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33946 raw33946Labels permutation166 permutation7
    mixedMoment B raw33946step0 raw33946step0Labels = mixedMoment B raw33946step1 raw33946step1Labels := by
      have ha : raw33946step1 = -raw33946step0 := by apply Matrix.ext; change ∀ i j, raw33946step1 i j = -(raw33946step0 i j); unfold raw33946step1 raw33946step0; decide +kernel
      have hl : raw33946step1Labels = raw33946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33946step1 raw33946step1Labels = mixedMoment B raw33946step2 raw33946step2Labels := by
      have ha : raw33946step2 = raw33946step1 := by apply Matrix.ext; unfold raw33946step2 raw33946step1; decide +kernel
      have hl : raw33946step1Labels = labelEmbedding1 ∘ raw33946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33946step1 raw33946step1Labels raw33946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw33947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33947step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33947step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33947step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33947 raw33947Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw33947 raw33947Labels = mixedMoment B raw33947step0 raw33947step0Labels := by
      have hz : ∀ j, raw33947 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33947step0 = (fun i j => raw33947 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33947step0 raw33947; decide +kernel
      have hl : raw33947step0Labels = raw33947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33947 raw33947Labels permutation520 hz
    mixedMoment B raw33947step0 raw33947step0Labels = mixedMoment B raw33947step1 raw33947step1Labels := by
      have ha : raw33947step1 = (fun i j => raw33947step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33947step1 raw33947step0; decide +kernel
      have hl : raw33947step1Labels = raw33947step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33947step0 raw33947step0Labels permutation32 permutation7
    mixedMoment B raw33947step1 raw33947step1Labels = mixedMoment B raw33947step2 raw33947step2Labels := by
      have ha : raw33947step2 = -raw33947step1 := by apply Matrix.ext; change ∀ i j, raw33947step2 i j = -(raw33947step1 i j); unfold raw33947step2 raw33947step1; decide +kernel
      have hl : raw33947step2Labels = raw33947step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33947step2 raw33947step2Labels = mixedMoment B raw33947step3 raw33947step3Labels := by
      have ha : raw33947step3 = raw33947step2 := by apply Matrix.ext; unfold raw33947step3 raw33947step2; decide +kernel
      have hl : raw33947step2Labels = labelEmbedding1 ∘ raw33947step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33947step2 raw33947step2Labels raw33947step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2227 node2227Labels := by rfl

def raw33948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33948step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33948step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33948 raw33948Labels = mixedMoment B node2204 node2204Labels := by
  calc
    mixedMoment B raw33948 raw33948Labels = mixedMoment B raw33948step0 raw33948step0Labels := by
      have ha : raw33948step0 = (fun i j => raw33948 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33948step0 raw33948; decide +kernel
      have hl : raw33948step0Labels = raw33948Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33948 raw33948Labels permutation164 permutation7
    mixedMoment B raw33948step0 raw33948step0Labels = mixedMoment B raw33948step1 raw33948step1Labels := by
      have ha : raw33948step1 = -raw33948step0 := by apply Matrix.ext; change ∀ i j, raw33948step1 i j = -(raw33948step0 i j); unfold raw33948step1 raw33948step0; decide +kernel
      have hl : raw33948step1Labels = raw33948step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33948step1 raw33948step1Labels = mixedMoment B raw33948step2 raw33948step2Labels := by
      have ha : raw33948step2 = raw33948step1 := by apply Matrix.ext; unfold raw33948step2 raw33948step1; decide +kernel
      have hl : raw33948step1Labels = labelEmbedding1 ∘ raw33948step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33948step1 raw33948step1Labels raw33948step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2204 node2204Labels := by rfl

def raw33949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33949step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33949 raw33949Labels = mixedMoment B node1671 node1671Labels := by
  calc
    mixedMoment B raw33949 raw33949Labels = mixedMoment B raw33949step0 raw33949step0Labels := by
      have ha : raw33949step0 = (fun i j => raw33949 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33949step0 raw33949; decide +kernel
      have hl : raw33949step0Labels = raw33949Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33949 raw33949Labels permutation164 permutation7
    mixedMoment B raw33949step0 raw33949step0Labels = mixedMoment B raw33949step1 raw33949step1Labels := by
      have ha : raw33949step1 = -raw33949step0 := by apply Matrix.ext; change ∀ i j, raw33949step1 i j = -(raw33949step0 i j); unfold raw33949step1 raw33949step0; decide +kernel
      have hl : raw33949step1Labels = raw33949step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33949step1 raw33949step1Labels = mixedMoment B raw33949step2 raw33949step2Labels := by
      have ha : raw33949step2 = raw33949step1 := by apply Matrix.ext; unfold raw33949step2 raw33949step1; decide +kernel
      have hl : raw33949step1Labels = labelEmbedding1 ∘ raw33949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33949step1 raw33949step1Labels raw33949step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1671 node1671Labels := by rfl

def raw33950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33950step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33950 raw33950Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw33950 raw33950Labels = mixedMoment B raw33950step0 raw33950step0Labels := by
      have ha : raw33950step0 = (fun i j => raw33950 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33950step0 raw33950; decide +kernel
      have hl : raw33950step0Labels = raw33950Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33950 raw33950Labels permutation164 permutation7
    mixedMoment B raw33950step0 raw33950step0Labels = mixedMoment B raw33950step1 raw33950step1Labels := by
      have ha : raw33950step1 = -raw33950step0 := by apply Matrix.ext; change ∀ i j, raw33950step1 i j = -(raw33950step0 i j); unfold raw33950step1 raw33950step0; decide +kernel
      have hl : raw33950step1Labels = raw33950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33950step1 raw33950step1Labels = mixedMoment B raw33950step2 raw33950step2Labels := by
      have ha : raw33950step2 = raw33950step1 := by apply Matrix.ext; unfold raw33950step2 raw33950step1; decide +kernel
      have hl : raw33950step1Labels = labelEmbedding1 ∘ raw33950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33950step1 raw33950step1Labels raw33950step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2148 node2148Labels := by rfl

def raw33951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw33951step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33951step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33951step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33951 raw33951Labels = mixedMoment B node2199 node2199Labels := by
  calc
    mixedMoment B raw33951 raw33951Labels = mixedMoment B raw33951step0 raw33951step0Labels := by
      have ha : raw33951step0 = (fun i j => raw33951 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33951step0 raw33951; decide +kernel
      have hl : raw33951step0Labels = raw33951Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33951 raw33951Labels permutation164 permutation7
    mixedMoment B raw33951step0 raw33951step0Labels = mixedMoment B raw33951step1 raw33951step1Labels := by
      have ha : raw33951step1 = -raw33951step0 := by apply Matrix.ext; change ∀ i j, raw33951step1 i j = -(raw33951step0 i j); unfold raw33951step1 raw33951step0; decide +kernel
      have hl : raw33951step1Labels = raw33951step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33951step1 raw33951step1Labels = mixedMoment B raw33951step2 raw33951step2Labels := by
      have ha : raw33951step2 = raw33951step1 := by apply Matrix.ext; unfold raw33951step2 raw33951step1; decide +kernel
      have hl : raw33951step1Labels = labelEmbedding1 ∘ raw33951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33951step1 raw33951step1Labels raw33951step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2199 node2199Labels := by rfl

def raw33952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33952step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33952step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33952step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33952 raw33952Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw33952 raw33952Labels = mixedMoment B raw33952step0 raw33952step0Labels := by
      have hz : ∀ j, raw33952 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33952step0 = (fun i j => raw33952 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33952step0 raw33952; decide +kernel
      have hl : raw33952step0Labels = raw33952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33952 raw33952Labels permutation520 hz
    mixedMoment B raw33952step0 raw33952step0Labels = mixedMoment B raw33952step1 raw33952step1Labels := by
      have ha : raw33952step1 = (fun i j => raw33952step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33952step1 raw33952step0; decide +kernel
      have hl : raw33952step1Labels = raw33952step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33952step0 raw33952step0Labels permutation32 permutation7
    mixedMoment B raw33952step1 raw33952step1Labels = mixedMoment B raw33952step2 raw33952step2Labels := by
      have ha : raw33952step2 = -raw33952step1 := by apply Matrix.ext; change ∀ i j, raw33952step2 i j = -(raw33952step1 i j); unfold raw33952step2 raw33952step1; decide +kernel
      have hl : raw33952step2Labels = raw33952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33952step2 raw33952step2Labels = mixedMoment B raw33952step3 raw33952step3Labels := by
      have ha : raw33952step3 = raw33952step2 := by apply Matrix.ext; unfold raw33952step3 raw33952step2; decide +kernel
      have hl : raw33952step2Labels = labelEmbedding1 ∘ raw33952step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33952step2 raw33952step2Labels raw33952step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw33953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33953step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33953step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33953 raw33953Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw33953 raw33953Labels = mixedMoment B raw33953step0 raw33953step0Labels := by
      have ha : raw33953step0 = (fun i j => raw33953 (permutation165 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33953step0 raw33953; decide +kernel
      have hl : raw33953step0Labels = raw33953Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33953 raw33953Labels permutation165 permutation7
    mixedMoment B raw33953step0 raw33953step0Labels = mixedMoment B raw33953step1 raw33953step1Labels := by
      have ha : raw33953step1 = -raw33953step0 := by apply Matrix.ext; change ∀ i j, raw33953step1 i j = -(raw33953step0 i j); unfold raw33953step1 raw33953step0; decide +kernel
      have hl : raw33953step1Labels = raw33953step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33953step1 raw33953step1Labels = mixedMoment B raw33953step2 raw33953step2Labels := by
      have ha : raw33953step2 = raw33953step1 := by apply Matrix.ext; unfold raw33953step2 raw33953step1; decide +kernel
      have hl : raw33953step1Labels = labelEmbedding1 ∘ raw33953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33953step1 raw33953step1Labels raw33953step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw33954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33954step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33954 raw33954Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw33954 raw33954Labels = mixedMoment B raw33954step0 raw33954step0Labels := by
      have ha : raw33954step0 = (fun i j => raw33954 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33954step0 raw33954; decide +kernel
      have hl : raw33954step0Labels = raw33954Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33954 raw33954Labels permutation164 permutation7
    mixedMoment B raw33954step0 raw33954step0Labels = mixedMoment B raw33954step1 raw33954step1Labels := by
      have ha : raw33954step1 = -raw33954step0 := by apply Matrix.ext; change ∀ i j, raw33954step1 i j = -(raw33954step0 i j); unfold raw33954step1 raw33954step0; decide +kernel
      have hl : raw33954step1Labels = raw33954step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33954step1 raw33954step1Labels = mixedMoment B raw33954step2 raw33954step2Labels := by
      have ha : raw33954step2 = raw33954step1 := by apply Matrix.ext; unfold raw33954step2 raw33954step1; decide +kernel
      have hl : raw33954step1Labels = labelEmbedding1 ∘ raw33954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33954step1 raw33954step1Labels raw33954step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

def raw33955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33955step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33955 raw33955Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw33955 raw33955Labels = mixedMoment B raw33955step0 raw33955step0Labels := by
      have ha : raw33955step0 = (fun i j => raw33955 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33955step0 raw33955; decide +kernel
      have hl : raw33955step0Labels = raw33955Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33955 raw33955Labels permutation164 permutation7
    mixedMoment B raw33955step0 raw33955step0Labels = mixedMoment B raw33955step1 raw33955step1Labels := by
      have ha : raw33955step1 = -raw33955step0 := by apply Matrix.ext; change ∀ i j, raw33955step1 i j = -(raw33955step0 i j); unfold raw33955step1 raw33955step0; decide +kernel
      have hl : raw33955step1Labels = raw33955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33955step1 raw33955step1Labels = mixedMoment B raw33955step2 raw33955step2Labels := by
      have ha : raw33955step2 = raw33955step1 := by apply Matrix.ext; unfold raw33955step2 raw33955step1; decide +kernel
      have hl : raw33955step1Labels = labelEmbedding1 ∘ raw33955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33955step1 raw33955step1Labels raw33955step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

def raw33956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33956step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33956step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33956 raw33956Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw33956 raw33956Labels = mixedMoment B raw33956step0 raw33956step0Labels := by
      have ha : raw33956step0 = (fun i j => raw33956 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33956step0 raw33956; decide +kernel
      have hl : raw33956step0Labels = raw33956Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33956 raw33956Labels permutation164 permutation7
    mixedMoment B raw33956step0 raw33956step0Labels = mixedMoment B raw33956step1 raw33956step1Labels := by
      have ha : raw33956step1 = -raw33956step0 := by apply Matrix.ext; change ∀ i j, raw33956step1 i j = -(raw33956step0 i j); unfold raw33956step1 raw33956step0; decide +kernel
      have hl : raw33956step1Labels = raw33956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33956step1 raw33956step1Labels = mixedMoment B raw33956step2 raw33956step2Labels := by
      have ha : raw33956step2 = raw33956step1 := by apply Matrix.ext; unfold raw33956step2 raw33956step1; decide +kernel
      have hl : raw33956step1Labels = labelEmbedding1 ∘ raw33956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33956step1 raw33956step1Labels raw33956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

def raw33957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33957step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33957step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33957 raw33957Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw33957 raw33957Labels = mixedMoment B raw33957step0 raw33957step0Labels := by
      have ha : raw33957step0 = (fun i j => raw33957 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33957step0 raw33957; decide +kernel
      have hl : raw33957step0Labels = raw33957Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33957 raw33957Labels permutation164 permutation7
    mixedMoment B raw33957step0 raw33957step0Labels = mixedMoment B raw33957step1 raw33957step1Labels := by
      have ha : raw33957step1 = -raw33957step0 := by apply Matrix.ext; change ∀ i j, raw33957step1 i j = -(raw33957step0 i j); unfold raw33957step1 raw33957step0; decide +kernel
      have hl : raw33957step1Labels = raw33957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33957step1 raw33957step1Labels = mixedMoment B raw33957step2 raw33957step2Labels := by
      have ha : raw33957step2 = raw33957step1 := by apply Matrix.ext; unfold raw33957step2 raw33957step1; decide +kernel
      have hl : raw33957step1Labels = labelEmbedding1 ∘ raw33957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33957step1 raw33957step1Labels raw33957step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw33958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33958step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33958step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33958step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33958 raw33958Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw33958 raw33958Labels = mixedMoment B raw33958step0 raw33958step0Labels := by
      have ha : raw33958step0 = (fun i j => raw33958 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33958step0 raw33958; decide +kernel
      have hl : raw33958step0Labels = raw33958Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33958 raw33958Labels permutation164 permutation7
    mixedMoment B raw33958step0 raw33958step0Labels = mixedMoment B raw33958step1 raw33958step1Labels := by
      have ha : raw33958step1 = -raw33958step0 := by apply Matrix.ext; change ∀ i j, raw33958step1 i j = -(raw33958step0 i j); unfold raw33958step1 raw33958step0; decide +kernel
      have hl : raw33958step1Labels = raw33958step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33958step1 raw33958step1Labels = mixedMoment B raw33958step2 raw33958step2Labels := by
      have ha : raw33958step2 = raw33958step1 := by apply Matrix.ext; unfold raw33958step2 raw33958step1; decide +kernel
      have hl : raw33958step1Labels = labelEmbedding1 ∘ raw33958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33958step1 raw33958step1Labels raw33958step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw33959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33959 raw33959Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw33959 raw33959Labels = mixedMoment B raw33959step0 raw33959step0Labels := by
      have ha : raw33959step0 = (fun i j => raw33959 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33959step0 raw33959; decide +kernel
      have hl : raw33959step0Labels = raw33959Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33959 raw33959Labels permutation164 permutation7
    mixedMoment B raw33959step0 raw33959step0Labels = mixedMoment B raw33959step1 raw33959step1Labels := by
      have ha : raw33959step1 = -raw33959step0 := by apply Matrix.ext; change ∀ i j, raw33959step1 i j = -(raw33959step0 i j); unfold raw33959step1 raw33959step0; decide +kernel
      have hl : raw33959step1Labels = raw33959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33959step1 raw33959step1Labels = mixedMoment B raw33959step2 raw33959step2Labels := by
      have ha : raw33959step2 = raw33959step1 := by apply Matrix.ext; unfold raw33959step2 raw33959step1; decide +kernel
      have hl : raw33959step1Labels = labelEmbedding1 ∘ raw33959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33959step1 raw33959step1Labels raw33959step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

def raw33960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33960step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33960step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33960 raw33960Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw33960 raw33960Labels = mixedMoment B raw33960step0 raw33960step0Labels := by
      have ha : raw33960step0 = (fun i j => raw33960 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33960step0 raw33960; decide +kernel
      have hl : raw33960step0Labels = raw33960Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33960 raw33960Labels permutation164 permutation7
    mixedMoment B raw33960step0 raw33960step0Labels = mixedMoment B raw33960step1 raw33960step1Labels := by
      have ha : raw33960step1 = -raw33960step0 := by apply Matrix.ext; change ∀ i j, raw33960step1 i j = -(raw33960step0 i j); unfold raw33960step1 raw33960step0; decide +kernel
      have hl : raw33960step1Labels = raw33960step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33960step1 raw33960step1Labels = mixedMoment B raw33960step2 raw33960step2Labels := by
      have ha : raw33960step2 = raw33960step1 := by apply Matrix.ext; unfold raw33960step2 raw33960step1; decide +kernel
      have hl : raw33960step1Labels = labelEmbedding1 ∘ raw33960step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33960step1 raw33960step1Labels raw33960step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2147 node2147Labels := by rfl

def raw33961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw33961step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33961step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33961 raw33961Labels = mixedMoment B node2198 node2198Labels := by
  calc
    mixedMoment B raw33961 raw33961Labels = mixedMoment B raw33961step0 raw33961step0Labels := by
      have ha : raw33961step0 = (fun i j => raw33961 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33961step0 raw33961; decide +kernel
      have hl : raw33961step0Labels = raw33961Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33961 raw33961Labels permutation164 permutation7
    mixedMoment B raw33961step0 raw33961step0Labels = mixedMoment B raw33961step1 raw33961step1Labels := by
      have ha : raw33961step1 = -raw33961step0 := by apply Matrix.ext; change ∀ i j, raw33961step1 i j = -(raw33961step0 i j); unfold raw33961step1 raw33961step0; decide +kernel
      have hl : raw33961step1Labels = raw33961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33961step1 raw33961step1Labels = mixedMoment B raw33961step2 raw33961step2Labels := by
      have ha : raw33961step2 = raw33961step1 := by apply Matrix.ext; unfold raw33961step2 raw33961step1; decide +kernel
      have hl : raw33961step1Labels = labelEmbedding1 ∘ raw33961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33961step1 raw33961step1Labels raw33961step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2198 node2198Labels := by rfl

def raw33962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw33962step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33962step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33962 raw33962Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw33962 raw33962Labels = mixedMoment B raw33962step0 raw33962step0Labels := by
      have ha : raw33962step0 = (fun i j => raw33962 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33962step0 raw33962; decide +kernel
      have hl : raw33962step0Labels = raw33962Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33962 raw33962Labels permutation164 permutation7
    mixedMoment B raw33962step0 raw33962step0Labels = mixedMoment B raw33962step1 raw33962step1Labels := by
      have ha : raw33962step1 = -raw33962step0 := by apply Matrix.ext; change ∀ i j, raw33962step1 i j = -(raw33962step0 i j); unfold raw33962step1 raw33962step0; decide +kernel
      have hl : raw33962step1Labels = raw33962step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33962step1 raw33962step1Labels = mixedMoment B raw33962step2 raw33962step2Labels := by
      have ha : raw33962step2 = raw33962step1 := by apply Matrix.ext; unfold raw33962step2 raw33962step1; decide +kernel
      have hl : raw33962step1Labels = labelEmbedding1 ∘ raw33962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33962step1 raw33962step1Labels raw33962step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw33963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33963step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33963step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33963step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33963step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33963step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33963 raw33963Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw33963 raw33963Labels = mixedMoment B raw33963step0 raw33963step0Labels := by
      have hz : ∀ j, raw33963 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33963step0 = (fun i j => raw33963 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33963step0 raw33963; decide +kernel
      have hl : raw33963step0Labels = raw33963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33963 raw33963Labels permutation520 hz
    mixedMoment B raw33963step0 raw33963step0Labels = mixedMoment B raw33963step1 raw33963step1Labels := by
      have ha : raw33963step1 = (fun i j => raw33963step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33963step1 raw33963step0; decide +kernel
      have hl : raw33963step1Labels = raw33963step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33963step0 raw33963step0Labels permutation32 permutation7
    mixedMoment B raw33963step1 raw33963step1Labels = mixedMoment B raw33963step2 raw33963step2Labels := by
      have ha : raw33963step2 = -raw33963step1 := by apply Matrix.ext; change ∀ i j, raw33963step2 i j = -(raw33963step1 i j); unfold raw33963step2 raw33963step1; decide +kernel
      have hl : raw33963step2Labels = raw33963step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33963step2 raw33963step2Labels = mixedMoment B raw33963step3 raw33963step3Labels := by
      have ha : raw33963step3 = raw33963step2 := by apply Matrix.ext; unfold raw33963step3 raw33963step2; decide +kernel
      have hl : raw33963step2Labels = labelEmbedding1 ∘ raw33963step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33963step2 raw33963step2Labels raw33963step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw33964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33964 raw33964Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw33964 raw33964Labels = mixedMoment B raw33964step0 raw33964step0Labels := by
      have ha : raw33964step0 = (fun i j => raw33964 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33964step0 raw33964; decide +kernel
      have hl : raw33964step0Labels = raw33964Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33964 raw33964Labels permutation154 permutation2
    _ = mixedMoment B node3376 node3376Labels := by rfl

def raw33965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33965 raw33965Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw33965 raw33965Labels = mixedMoment B raw33965step0 raw33965step0Labels := by
      have ha : raw33965step0 = (fun i j => raw33965 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33965step0 raw33965; decide +kernel
      have hl : raw33965step0Labels = raw33965Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33965 raw33965Labels permutation154 permutation2
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw33966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33966 raw33966Labels = mixedMoment B node1805 node1805Labels := by
  calc
    mixedMoment B raw33966 raw33966Labels = mixedMoment B raw33966step0 raw33966step0Labels := by
      have ha : raw33966step0 = (fun i j => raw33966 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33966step0 raw33966; decide +kernel
      have hl : raw33966step0Labels = raw33966Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33966 raw33966Labels permutation164 permutation2
    _ = mixedMoment B node1805 node1805Labels := by rfl

def raw33967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33967 raw33967Labels = mixedMoment B node1792 node1792Labels := by
  calc
    mixedMoment B raw33967 raw33967Labels = mixedMoment B raw33967step0 raw33967step0Labels := by
      have ha : raw33967step0 = (fun i j => raw33967 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33967step0 raw33967; decide +kernel
      have hl : raw33967step0Labels = raw33967Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33967 raw33967Labels permutation154 permutation2
    _ = mixedMoment B node1792 node1792Labels := by rfl

def raw33968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33968 raw33968Labels = mixedMoment B node1794 node1794Labels := by
  calc
    _ = mixedMoment B node1794 node1794Labels := by rfl

def raw33969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33969 raw33969Labels = mixedMoment B node1790 node1790Labels := by
  calc
    mixedMoment B raw33969 raw33969Labels = mixedMoment B raw33969step0 raw33969step0Labels := by
      have ha : raw33969step0 = (fun i j => raw33969 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33969step0 raw33969; decide +kernel
      have hl : raw33969step0Labels = raw33969Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33969 raw33969Labels permutation154 permutation2
    _ = mixedMoment B node1790 node1790Labels := by rfl

def raw33970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33970step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33970step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33970step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33970 raw33970Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw33970 raw33970Labels = mixedMoment B raw33970step0 raw33970step0Labels := by
      have ha : raw33970step0 = (fun i j => raw33970 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33970step0 raw33970; decide +kernel
      have hl : raw33970step0Labels = raw33970Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33970 raw33970Labels permutation154 permutation3
    mixedMoment B raw33970step0 raw33970step0Labels = mixedMoment B raw33970step1 raw33970step1Labels := by
      have ha : raw33970step1 = raw33970step0 := by apply Matrix.ext; unfold raw33970step1 raw33970step0; decide +kernel
      have hl : raw33970step0Labels = labelEmbedding6 ∘ raw33970step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33970step0 raw33970step0Labels raw33970step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw33971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33971step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33971 raw33971Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw33971 raw33971Labels = mixedMoment B raw33971step0 raw33971step0Labels := by
      have ha : raw33971step0 = (fun i j => raw33971 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33971step0 raw33971; decide +kernel
      have hl : raw33971step0Labels = raw33971Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33971 raw33971Labels permutation154 permutation3
    mixedMoment B raw33971step0 raw33971step0Labels = mixedMoment B raw33971step1 raw33971step1Labels := by
      have ha : raw33971step1 = raw33971step0 := by apply Matrix.ext; unfold raw33971step1 raw33971step0; decide +kernel
      have hl : raw33971step0Labels = labelEmbedding6 ∘ raw33971step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33971step0 raw33971step0Labels raw33971step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw33972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33972step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33972 raw33972Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw33972 raw33972Labels = mixedMoment B raw33972step0 raw33972step0Labels := by
      have ha : raw33972step0 = (fun i j => raw33972 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33972step0 raw33972; decide +kernel
      have hl : raw33972step0Labels = raw33972Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33972 raw33972Labels permutation164 permutation3
    mixedMoment B raw33972step0 raw33972step0Labels = mixedMoment B raw33972step1 raw33972step1Labels := by
      have ha : raw33972step1 = raw33972step0 := by apply Matrix.ext; unfold raw33972step1 raw33972step0; decide +kernel
      have hl : raw33972step0Labels = labelEmbedding6 ∘ raw33972step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33972step0 raw33972step0Labels raw33972step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw33973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33973step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33973step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33973step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33973 raw33973Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw33973 raw33973Labels = mixedMoment B raw33973step0 raw33973step0Labels := by
      have ha : raw33973step0 = (fun i j => raw33973 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33973step0 raw33973; decide +kernel
      have hl : raw33973step0Labels = raw33973Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33973 raw33973Labels permutation166 permutation3
    mixedMoment B raw33973step0 raw33973step0Labels = mixedMoment B raw33973step1 raw33973step1Labels := by
      have ha : raw33973step1 = raw33973step0 := by apply Matrix.ext; unfold raw33973step1 raw33973step0; decide +kernel
      have hl : raw33973step0Labels = labelEmbedding6 ∘ raw33973step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33973step0 raw33973step0Labels raw33973step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4210 node4210Labels := by rfl

def raw33974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33974step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33974 raw33974Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw33974 raw33974Labels = mixedMoment B raw33974step0 raw33974step0Labels := by
      have ha : raw33974step0 = (fun i j => raw33974 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33974step0 raw33974; decide +kernel
      have hl : raw33974step0Labels = raw33974Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33974 raw33974Labels permutation166 permutation3
    mixedMoment B raw33974step0 raw33974step0Labels = mixedMoment B raw33974step1 raw33974step1Labels := by
      have ha : raw33974step1 = raw33974step0 := by apply Matrix.ext; unfold raw33974step1 raw33974step0; decide +kernel
      have hl : raw33974step0Labels = labelEmbedding6 ∘ raw33974step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33974step0 raw33974step0Labels raw33974step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

def raw33975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33975step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33975 raw33975Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw33975 raw33975Labels = mixedMoment B raw33975step0 raw33975step0Labels := by
      have ha : raw33975step0 = (fun i j => raw33975 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33975step0 raw33975; decide +kernel
      have hl : raw33975step0Labels = raw33975Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33975 raw33975Labels permutation166 permutation3
    mixedMoment B raw33975step0 raw33975step0Labels = mixedMoment B raw33975step1 raw33975step1Labels := by
      have ha : raw33975step1 = raw33975step0 := by apply Matrix.ext; unfold raw33975step1 raw33975step0; decide +kernel
      have hl : raw33975step0Labels = labelEmbedding6 ∘ raw33975step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33975step0 raw33975step0Labels raw33975step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

def raw33976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33976step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33976 raw33976Labels = mixedMoment B node4197 node4197Labels := by
  calc
    mixedMoment B raw33976 raw33976Labels = mixedMoment B raw33976step0 raw33976step0Labels := by
      have ha : raw33976step0 = (fun i j => raw33976 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33976step0 raw33976; decide +kernel
      have hl : raw33976step0Labels = raw33976Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33976 raw33976Labels permutation155 permutation3
    mixedMoment B raw33976step0 raw33976step0Labels = mixedMoment B raw33976step1 raw33976step1Labels := by
      have ha : raw33976step1 = raw33976step0 := by apply Matrix.ext; unfold raw33976step1 raw33976step0; decide +kernel
      have hl : raw33976step0Labels = labelEmbedding6 ∘ raw33976step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33976step0 raw33976step0Labels raw33976step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4197 node4197Labels := by rfl

def raw33977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33977step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33977 raw33977Labels = mixedMoment B node4632 node4632Labels := by
  calc
    mixedMoment B raw33977 raw33977Labels = mixedMoment B raw33977step0 raw33977step0Labels := by
      have ha : raw33977step0 = (fun i j => raw33977 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33977step0 raw33977; decide +kernel
      have hl : raw33977step0Labels = raw33977Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33977 raw33977Labels permutation155 permutation3
    mixedMoment B raw33977step0 raw33977step0Labels = mixedMoment B raw33977step1 raw33977step1Labels := by
      have ha : raw33977step1 = raw33977step0 := by apply Matrix.ext; unfold raw33977step1 raw33977step0; decide +kernel
      have hl : raw33977step0Labels = labelEmbedding6 ∘ raw33977step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33977step0 raw33977step0Labels raw33977step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4632 node4632Labels := by rfl

def raw33978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33978step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33978 raw33978Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw33978 raw33978Labels = mixedMoment B raw33978step0 raw33978step0Labels := by
      have ha : raw33978step0 = (fun i j => raw33978 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33978step0 raw33978; decide +kernel
      have hl : raw33978step0Labels = raw33978Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33978 raw33978Labels permutation155 permutation3
    mixedMoment B raw33978step0 raw33978step0Labels = mixedMoment B raw33978step1 raw33978step1Labels := by
      have ha : raw33978step1 = raw33978step0 := by apply Matrix.ext; unfold raw33978step1 raw33978step0; decide +kernel
      have hl : raw33978step0Labels = labelEmbedding6 ∘ raw33978step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33978step0 raw33978step0Labels raw33978step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

def raw33979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33979step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33979 raw33979Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw33979 raw33979Labels = mixedMoment B raw33979step0 raw33979step0Labels := by
      have ha : raw33979step0 = (fun i j => raw33979 (permutation165 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33979step0 raw33979; decide +kernel
      have hl : raw33979step0Labels = raw33979Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33979 raw33979Labels permutation165 permutation3
    mixedMoment B raw33979step0 raw33979step0Labels = mixedMoment B raw33979step1 raw33979step1Labels := by
      have ha : raw33979step1 = raw33979step0 := by apply Matrix.ext; unfold raw33979step1 raw33979step0; decide +kernel
      have hl : raw33979step0Labels = labelEmbedding6 ∘ raw33979step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33979step0 raw33979step0Labels raw33979step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw33980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33980step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33980step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33980 raw33980Labels = mixedMoment B node4196 node4196Labels := by
  calc
    mixedMoment B raw33980 raw33980Labels = mixedMoment B raw33980step0 raw33980step0Labels := by
      have ha : raw33980step0 = (fun i j => raw33980 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33980step0 raw33980; decide +kernel
      have hl : raw33980step0Labels = raw33980Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33980 raw33980Labels permutation154 permutation3
    mixedMoment B raw33980step0 raw33980step0Labels = mixedMoment B raw33980step1 raw33980step1Labels := by
      have ha : raw33980step1 = raw33980step0 := by apply Matrix.ext; unfold raw33980step1 raw33980step0; decide +kernel
      have hl : raw33980step0Labels = labelEmbedding6 ∘ raw33980step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33980step0 raw33980step0Labels raw33980step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4196 node4196Labels := by rfl

def raw33981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33981step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33981 raw33981Labels = mixedMoment B node4631 node4631Labels := by
  calc
    mixedMoment B raw33981 raw33981Labels = mixedMoment B raw33981step0 raw33981step0Labels := by
      have ha : raw33981step0 = (fun i j => raw33981 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33981step0 raw33981; decide +kernel
      have hl : raw33981step0Labels = raw33981Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33981 raw33981Labels permutation154 permutation3
    mixedMoment B raw33981step0 raw33981step0Labels = mixedMoment B raw33981step1 raw33981step1Labels := by
      have ha : raw33981step1 = raw33981step0 := by apply Matrix.ext; unfold raw33981step1 raw33981step0; decide +kernel
      have hl : raw33981step0Labels = labelEmbedding6 ∘ raw33981step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33981step0 raw33981step0Labels raw33981step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4631 node4631Labels := by rfl

def raw33982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33982step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33982 raw33982Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw33982 raw33982Labels = mixedMoment B raw33982step0 raw33982step0Labels := by
      have ha : raw33982step0 = (fun i j => raw33982 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33982step0 raw33982; decide +kernel
      have hl : raw33982step0Labels = raw33982Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33982 raw33982Labels permutation154 permutation3
    mixedMoment B raw33982step0 raw33982step0Labels = mixedMoment B raw33982step1 raw33982step1Labels := by
      have ha : raw33982step1 = raw33982step0 := by apply Matrix.ext; unfold raw33982step1 raw33982step0; decide +kernel
      have hl : raw33982step0Labels = labelEmbedding6 ∘ raw33982step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33982step0 raw33982step0Labels raw33982step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4760 node4760Labels := by rfl

def raw33983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw33983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33983step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33983 raw33983Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw33983 raw33983Labels = mixedMoment B raw33983step0 raw33983step0Labels := by
      have ha : raw33983step0 = (fun i j => raw33983 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33983step0 raw33983; decide +kernel
      have hl : raw33983step0Labels = raw33983Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33983 raw33983Labels permutation164 permutation3
    mixedMoment B raw33983step0 raw33983step0Labels = mixedMoment B raw33983step1 raw33983step1Labels := by
      have ha : raw33983step1 = raw33983step0 := by apply Matrix.ext; unfold raw33983step1 raw33983step0; decide +kernel
      have hl : raw33983step0Labels = labelEmbedding6 ∘ raw33983step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33983step0 raw33983step0Labels raw33983step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

def raw33984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw33984step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33984step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33984step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33984 raw33984Labels = mixedMoment B node4400 node4400Labels := by
  calc
    mixedMoment B raw33984 raw33984Labels = mixedMoment B raw33984step0 raw33984step0Labels := by
      have ha : raw33984step0 = (fun i j => raw33984 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33984step0 raw33984; decide +kernel
      have hl : raw33984step0Labels = raw33984Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33984 raw33984Labels permutation167 permutation4
    mixedMoment B raw33984step0 raw33984step0Labels = mixedMoment B raw33984step1 raw33984step1Labels := by
      have ha : raw33984step1 = -raw33984step0 := by apply Matrix.ext; change ∀ i j, raw33984step1 i j = -(raw33984step0 i j); unfold raw33984step1 raw33984step0; decide +kernel
      have hl : raw33984step1Labels = raw33984step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33984step1 raw33984step1Labels = mixedMoment B raw33984step2 raw33984step2Labels := by
      have ha : raw33984step2 = raw33984step1 := by apply Matrix.ext; unfold raw33984step2 raw33984step1; decide +kernel
      have hl : raw33984step1Labels = labelEmbedding7 ∘ raw33984step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33984step1 raw33984step1Labels raw33984step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4400 node4400Labels := by rfl

def raw33985 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33985step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33985 raw33985Labels = mixedMoment B node4813 node4813Labels := by
  calc
    mixedMoment B raw33985 raw33985Labels = mixedMoment B raw33985step0 raw33985step0Labels := by
      have ha : raw33985step0 = (fun i j => raw33985 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33985step0 raw33985; decide +kernel
      have hl : raw33985step0Labels = raw33985Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33985 raw33985Labels permutation154 permutation6
    mixedMoment B raw33985step0 raw33985step0Labels = mixedMoment B raw33985step1 raw33985step1Labels := by
      have ha : raw33985step1 = raw33985step0 := by apply Matrix.ext; unfold raw33985step1 raw33985step0; decide +kernel
      have hl : raw33985step0Labels = labelEmbedding9 ∘ raw33985step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33985step0 raw33985step0Labels raw33985step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4813 node4813Labels := by rfl

def raw33986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw33986step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33986step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33986step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33986step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33986 raw33986Labels = mixedMoment B node4397 node4397Labels := by
  calc
    mixedMoment B raw33986 raw33986Labels = mixedMoment B raw33986step0 raw33986step0Labels := by
      have ha : raw33986step0 = (fun i j => raw33986 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33986step0 raw33986; decide +kernel
      have hl : raw33986step0Labels = raw33986Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33986 raw33986Labels permutation165 permutation4
    mixedMoment B raw33986step0 raw33986step0Labels = mixedMoment B raw33986step1 raw33986step1Labels := by
      have ha : raw33986step1 = -raw33986step0 := by apply Matrix.ext; change ∀ i j, raw33986step1 i j = -(raw33986step0 i j); unfold raw33986step1 raw33986step0; decide +kernel
      have hl : raw33986step1Labels = raw33986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33986step1 raw33986step1Labels = mixedMoment B raw33986step2 raw33986step2Labels := by
      have ha : raw33986step2 = raw33986step1 := by apply Matrix.ext; unfold raw33986step2 raw33986step1; decide +kernel
      have hl : raw33986step1Labels = labelEmbedding7 ∘ raw33986step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33986step1 raw33986step1Labels raw33986step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4397 node4397Labels := by rfl

def raw33987 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33987step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33987 raw33987Labels = mixedMoment B node4799 node4799Labels := by
  calc
    mixedMoment B raw33987 raw33987Labels = mixedMoment B raw33987step0 raw33987step0Labels := by
      have ha : raw33987step0 = (fun i j => raw33987 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33987step0 raw33987; decide +kernel
      have hl : raw33987step0Labels = raw33987Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33987 raw33987Labels permutation154 permutation6
    mixedMoment B raw33987step0 raw33987step0Labels = mixedMoment B raw33987step1 raw33987step1Labels := by
      have ha : raw33987step1 = raw33987step0 := by apply Matrix.ext; unfold raw33987step1 raw33987step0; decide +kernel
      have hl : raw33987step0Labels = labelEmbedding9 ∘ raw33987step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33987step0 raw33987step0Labels raw33987step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4799 node4799Labels := by rfl

def raw33988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33988step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33988step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33988step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33988 raw33988Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw33988 raw33988Labels = mixedMoment B raw33988step0 raw33988step0Labels := by
      have ha : raw33988step0 = (fun i j => raw33988 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33988step0 raw33988; decide +kernel
      have hl : raw33988step0Labels = raw33988Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33988 raw33988Labels permutation164 permutation4
    mixedMoment B raw33988step0 raw33988step0Labels = mixedMoment B raw33988step1 raw33988step1Labels := by
      have ha : raw33988step1 = -raw33988step0 := by apply Matrix.ext; change ∀ i j, raw33988step1 i j = -(raw33988step0 i j); unfold raw33988step1 raw33988step0; decide +kernel
      have hl : raw33988step1Labels = raw33988step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33988step1 raw33988step1Labels = mixedMoment B raw33988step2 raw33988step2Labels := by
      have ha : raw33988step2 = raw33988step1 := by apply Matrix.ext; unfold raw33988step2 raw33988step1; decide +kernel
      have hl : raw33988step1Labels = labelEmbedding7 ∘ raw33988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33988step1 raw33988step1Labels raw33988step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw33989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33989step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33989step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33989step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33989step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33989 raw33989Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw33989 raw33989Labels = mixedMoment B raw33989step0 raw33989step0Labels := by
      have ha : raw33989step0 = (fun i j => raw33989 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33989step0 raw33989; decide +kernel
      have hl : raw33989step0Labels = raw33989Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33989 raw33989Labels permutation160 permutation7
    mixedMoment B raw33989step0 raw33989step0Labels = mixedMoment B raw33989step1 raw33989step1Labels := by
      have ha : raw33989step1 = -raw33989step0 := by apply Matrix.ext; change ∀ i j, raw33989step1 i j = -(raw33989step0 i j); unfold raw33989step1 raw33989step0; decide +kernel
      have hl : raw33989step1Labels = raw33989step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33989step1 raw33989step1Labels = mixedMoment B raw33989step2 raw33989step2Labels := by
      have ha : raw33989step2 = raw33989step1 := by apply Matrix.ext; unfold raw33989step2 raw33989step1; decide +kernel
      have hl : raw33989step1Labels = labelEmbedding10 ∘ raw33989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33989step1 raw33989step1Labels raw33989step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

def raw33990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33990step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33990step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33990step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33990step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33990 raw33990Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw33990 raw33990Labels = mixedMoment B raw33990step0 raw33990step0Labels := by
      have ha : raw33990step0 = (fun i j => raw33990 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33990step0 raw33990; decide +kernel
      have hl : raw33990step0Labels = raw33990Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33990 raw33990Labels permutation160 permutation7
    mixedMoment B raw33990step0 raw33990step0Labels = mixedMoment B raw33990step1 raw33990step1Labels := by
      have ha : raw33990step1 = -raw33990step0 := by apply Matrix.ext; change ∀ i j, raw33990step1 i j = -(raw33990step0 i j); unfold raw33990step1 raw33990step0; decide +kernel
      have hl : raw33990step1Labels = raw33990step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33990step1 raw33990step1Labels = mixedMoment B raw33990step2 raw33990step2Labels := by
      have ha : raw33990step2 = raw33990step1 := by apply Matrix.ext; unfold raw33990step2 raw33990step1; decide +kernel
      have hl : raw33990step1Labels = labelEmbedding10 ∘ raw33990step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33990step1 raw33990step1Labels raw33990step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

def raw33991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33991step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33991step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33991step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33991 raw33991Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw33991 raw33991Labels = mixedMoment B raw33991step0 raw33991step0Labels := by
      have hz : ∀ j, raw33991 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33991step0 = (fun i j => raw33991 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33991step0 raw33991; decide +kernel
      have hl : raw33991step0Labels = raw33991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33991 raw33991Labels permutation434 hz
    mixedMoment B raw33991step0 raw33991step0Labels = mixedMoment B raw33991step1 raw33991step1Labels := by
      have ha : raw33991step1 = (fun i j => raw33991step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33991step1 raw33991step0; decide +kernel
      have hl : raw33991step1Labels = raw33991step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33991step0 raw33991step0Labels permutation34 permutation7
    mixedMoment B raw33991step1 raw33991step1Labels = mixedMoment B raw33991step2 raw33991step2Labels := by
      have ha : raw33991step2 = -raw33991step1 := by apply Matrix.ext; change ∀ i j, raw33991step2 i j = -(raw33991step1 i j); unfold raw33991step2 raw33991step1; decide +kernel
      have hl : raw33991step2Labels = raw33991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33991step2 raw33991step2Labels = mixedMoment B raw33991step3 raw33991step3Labels := by
      have ha : raw33991step3 = raw33991step2 := by apply Matrix.ext; unfold raw33991step3 raw33991step2; decide +kernel
      have hl : raw33991step2Labels = labelEmbedding10 ∘ raw33991step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33991step2 raw33991step2Labels raw33991step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw33992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33992step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33992step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33992step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33992 raw33992Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw33992 raw33992Labels = mixedMoment B raw33992step0 raw33992step0Labels := by
      have hz : ∀ j, raw33992 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33992step0 = (fun i j => raw33992 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33992step0 raw33992; decide +kernel
      have hl : raw33992step0Labels = raw33992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33992 raw33992Labels permutation520 hz
    mixedMoment B raw33992step0 raw33992step0Labels = mixedMoment B raw33992step1 raw33992step1Labels := by
      have ha : raw33992step1 = (fun i j => raw33992step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33992step1 raw33992step0; decide +kernel
      have hl : raw33992step1Labels = raw33992step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33992step0 raw33992step0Labels permutation34 permutation7
    mixedMoment B raw33992step1 raw33992step1Labels = mixedMoment B raw33992step2 raw33992step2Labels := by
      have ha : raw33992step2 = -raw33992step1 := by apply Matrix.ext; change ∀ i j, raw33992step2 i j = -(raw33992step1 i j); unfold raw33992step2 raw33992step1; decide +kernel
      have hl : raw33992step2Labels = raw33992step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33992step2 raw33992step2Labels = mixedMoment B raw33992step3 raw33992step3Labels := by
      have ha : raw33992step3 = raw33992step2 := by apply Matrix.ext; unfold raw33992step3 raw33992step2; decide +kernel
      have hl : raw33992step2Labels = labelEmbedding10 ∘ raw33992step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33992step2 raw33992step2Labels raw33992step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw33993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw33993step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33993step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33993step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33993 raw33993Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw33993 raw33993Labels = mixedMoment B raw33993step0 raw33993step0Labels := by
      have ha : raw33993step0 = (fun i j => raw33993 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33993step0 raw33993; decide +kernel
      have hl : raw33993step0Labels = raw33993Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33993 raw33993Labels permutation160 permutation7
    mixedMoment B raw33993step0 raw33993step0Labels = mixedMoment B raw33993step1 raw33993step1Labels := by
      have ha : raw33993step1 = -raw33993step0 := by apply Matrix.ext; change ∀ i j, raw33993step1 i j = -(raw33993step0 i j); unfold raw33993step1 raw33993step0; decide +kernel
      have hl : raw33993step1Labels = raw33993step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33993step1 raw33993step1Labels = mixedMoment B raw33993step2 raw33993step2Labels := by
      have ha : raw33993step2 = raw33993step1 := by apply Matrix.ext; unfold raw33993step2 raw33993step1; decide +kernel
      have hl : raw33993step1Labels = labelEmbedding10 ∘ raw33993step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33993step1 raw33993step1Labels raw33993step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw33994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33994 raw33994Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw33994 raw33994Labels = mixedMoment B raw33994step0 raw33994step0Labels := by
      have hz : ∀ j, raw33994 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33994step0 = (fun i j => raw33994 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33994step0 raw33994; decide +kernel
      have hl : raw33994step0Labels = raw33994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33994 raw33994Labels permutation265 hz
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw33995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33995 raw33995Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw33995 raw33995Labels = mixedMoment B raw33995step0 raw33995step0Labels := by
      have hz : ∀ j, raw33995 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33995step0 = (fun i j => raw33995 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33995step0 raw33995; decide +kernel
      have hl : raw33995step0Labels = raw33995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33995 raw33995Labels permutation265 hz
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw33996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33996step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33996 raw33996Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw33996 raw33996Labels = mixedMoment B raw33996step0 raw33996step0Labels := by
      have hz : ∀ j, raw33996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33996step0 = (fun i j => raw33996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33996step0 raw33996; decide +kernel
      have hl : raw33996step0Labels = raw33996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33996 raw33996Labels permutation434 hz
    mixedMoment B raw33996step0 raw33996step0Labels = mixedMoment B raw33996step1 raw33996step1Labels := by
      have hz : ∀ j, raw33996step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw33996step1 = (fun i j => raw33996step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw33996step1 raw33996step0; decide +kernel
      have hl : raw33996step1Labels = raw33996step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33996step0 raw33996step0Labels permutation56 hz
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw33997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33997 raw33997Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw33997 raw33997Labels = mixedMoment B raw33997step0 raw33997step0Labels := by
      have hz : ∀ j, raw33997 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33997step0 = (fun i j => raw33997 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33997step0 raw33997; decide +kernel
      have hl : raw33997step0Labels = raw33997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33997 raw33997Labels permutation520 hz
    mixedMoment B raw33997step0 raw33997step0Labels = mixedMoment B raw33997step1 raw33997step1Labels := by
      have hz : ∀ j, raw33997step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw33997step1 = (fun i j => raw33997step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw33997step1 raw33997step0; decide +kernel
      have hl : raw33997step1Labels = raw33997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33997step0 raw33997step0Labels permutation56 hz
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw33998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw33998step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33998step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33998step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33998step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33998 raw33998Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw33998 raw33998Labels = mixedMoment B raw33998step0 raw33998step0Labels := by
      have hz : ∀ j, raw33998 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33998step0 = (fun i j => raw33998 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33998step0 raw33998; decide +kernel
      have hl : raw33998step0Labels = raw33998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33998 raw33998Labels permutation265 hz
    mixedMoment B raw33998step0 raw33998step0Labels = mixedMoment B raw33998step1 raw33998step1Labels := by
      have ha : raw33998step1 = (fun i j => raw33998step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33998step1 raw33998step0; decide +kernel
      have hl : raw33998step1Labels = raw33998step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33998step0 raw33998step0Labels permutation40 permutation7
    mixedMoment B raw33998step1 raw33998step1Labels = mixedMoment B raw33998step2 raw33998step2Labels := by
      have ha : raw33998step2 = -raw33998step1 := by apply Matrix.ext; change ∀ i j, raw33998step2 i j = -(raw33998step1 i j); unfold raw33998step2 raw33998step1; decide +kernel
      have hl : raw33998step2Labels = raw33998step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33998step2 raw33998step2Labels = mixedMoment B raw33998step3 raw33998step3Labels := by
      have ha : raw33998step3 = raw33998step2 := by apply Matrix.ext; unfold raw33998step3 raw33998step2; decide +kernel
      have hl : raw33998step2Labels = labelEmbedding10 ∘ raw33998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33998step2 raw33998step2Labels raw33998step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw33999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33999 raw33999Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw33999 raw33999Labels = mixedMoment B raw33999step0 raw33999step0Labels := by
      have ha : raw33999step0 = (fun i j => raw33999 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33999step0 raw33999; decide +kernel
      have hl : raw33999step0Labels = raw33999Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33999 raw33999Labels permutation160 permutation2
    _ = mixedMoment B node4341 node4341Labels := by rfl

def raw34000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34000 raw34000Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw34000 raw34000Labels = mixedMoment B raw34000step0 raw34000step0Labels := by
      have ha : raw34000step0 = (fun i j => raw34000 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34000step0 raw34000; decide +kernel
      have hl : raw34000step0Labels = raw34000Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34000 raw34000Labels permutation160 permutation2
    _ = mixedMoment B node4676 node4676Labels := by rfl

def raw34001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34001 raw34001Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw34001 raw34001Labels = mixedMoment B raw34001step0 raw34001step0Labels := by
      have hz : ∀ j, raw34001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34001step0 = (fun i j => raw34001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34001step0 raw34001; decide +kernel
      have hl : raw34001step0Labels = raw34001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34001 raw34001Labels permutation434 hz
    mixedMoment B raw34001step0 raw34001step0Labels = mixedMoment B raw34001step1 raw34001step1Labels := by
      have ha : raw34001step1 = (fun i j => raw34001step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34001step1 raw34001step0; decide +kernel
      have hl : raw34001step1Labels = raw34001step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34001step0 raw34001step0Labels permutation34 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw34002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34002step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34002 raw34002Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw34002 raw34002Labels = mixedMoment B raw34002step0 raw34002step0Labels := by
      have hz : ∀ j, raw34002 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34002step0 = (fun i j => raw34002 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34002step0 raw34002; decide +kernel
      have hl : raw34002step0Labels = raw34002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34002 raw34002Labels permutation520 hz
    mixedMoment B raw34002step0 raw34002step0Labels = mixedMoment B raw34002step1 raw34002step1Labels := by
      have ha : raw34002step1 = (fun i j => raw34002step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34002step1 raw34002step0; decide +kernel
      have hl : raw34002step1Labels = raw34002step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34002step0 raw34002step0Labels permutation34 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw34003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34003 raw34003Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw34003 raw34003Labels = mixedMoment B raw34003step0 raw34003step0Labels := by
      have ha : raw34003step0 = (fun i j => raw34003 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34003step0 raw34003; decide +kernel
      have hl : raw34003step0Labels = raw34003Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34003 raw34003Labels permutation160 permutation2
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw34004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34004 raw34004Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw34004 raw34004Labels = mixedMoment B raw34004step0 raw34004step0Labels := by
      have ha : raw34004step0 = (fun i j => raw34004 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34004step0 raw34004; decide +kernel
      have hl : raw34004step0Labels = raw34004Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34004 raw34004Labels permutation154 permutation2
    _ = mixedMoment B node4328 node4328Labels := by rfl

def raw34005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34005 raw34005Labels = mixedMoment B node4665 node4665Labels := by
  calc
    mixedMoment B raw34005 raw34005Labels = mixedMoment B raw34005step0 raw34005step0Labels := by
      have ha : raw34005step0 = (fun i j => raw34005 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34005step0 raw34005; decide +kernel
      have hl : raw34005step0Labels = raw34005Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34005 raw34005Labels permutation154 permutation2
    _ = mixedMoment B node4665 node4665Labels := by rfl

def raw34006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34006 raw34006Labels = mixedMoment B node4773 node4773Labels := by
  calc
    mixedMoment B raw34006 raw34006Labels = mixedMoment B raw34006step0 raw34006step0Labels := by
      have ha : raw34006step0 = (fun i j => raw34006 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34006step0 raw34006; decide +kernel
      have hl : raw34006step0Labels = raw34006Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34006 raw34006Labels permutation154 permutation2
    _ = mixedMoment B node4773 node4773Labels := by rfl

def raw34007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34007 raw34007Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw34007 raw34007Labels = mixedMoment B raw34007step0 raw34007step0Labels := by
      have hz : ∀ j, raw34007 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34007step0 = (fun i j => raw34007 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34007step0 raw34007; decide +kernel
      have hl : raw34007step0Labels = raw34007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34007 raw34007Labels permutation520 hz
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw34008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34008step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34008 raw34008Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw34008 raw34008Labels = mixedMoment B raw34008step0 raw34008step0Labels := by
      have ha : raw34008step0 = (fun i j => raw34008 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34008step0 raw34008; decide +kernel
      have hl : raw34008step0Labels = raw34008Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34008 raw34008Labels permutation155 permutation2
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw34009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34009 raw34009Labels = mixedMoment B node4328 node4328Labels := by
  calc
    _ = mixedMoment B node4328 node4328Labels := by rfl

def raw34010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34010 raw34010Labels = mixedMoment B node4665 node4665Labels := by
  calc
    _ = mixedMoment B node4665 node4665Labels := by rfl

def raw34011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34011 raw34011Labels = mixedMoment B node4773 node4773Labels := by
  calc
    _ = mixedMoment B node4773 node4773Labels := by rfl

def raw34012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34012 raw34012Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw34012 raw34012Labels = mixedMoment B raw34012step0 raw34012step0Labels := by
      have hz : ∀ j, raw34012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34012step0 = (fun i j => raw34012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34012step0 raw34012; decide +kernel
      have hl : raw34012step0Labels = raw34012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34012 raw34012Labels permutation434 hz
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw34013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34013 raw34013Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw34013 raw34013Labels = mixedMoment B raw34013step0 raw34013step0Labels := by
      have ha : raw34013step0 = (fun i j => raw34013 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34013step0 raw34013; decide +kernel
      have hl : raw34013step0Labels = raw34013Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34013 raw34013Labels permutation153 permutation2
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw34014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34014 raw34014Labels = mixedMoment B node4326 node4326Labels := by
  calc
    _ = mixedMoment B node4326 node4326Labels := by rfl

def raw34015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34015 raw34015Labels = mixedMoment B node4663 node4663Labels := by
  calc
    _ = mixedMoment B node4663 node4663Labels := by rfl

def raw34016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34016 raw34016Labels = mixedMoment B node4771 node4771Labels := by
  calc
    _ = mixedMoment B node4771 node4771Labels := by rfl

def raw34017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34017 raw34017Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw34017 raw34017Labels = mixedMoment B raw34017step0 raw34017step0Labels := by
      have hz : ∀ j, raw34017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34017step0 = (fun i j => raw34017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34017step0 raw34017; decide +kernel
      have hl : raw34017step0Labels = raw34017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34017 raw34017Labels permutation434 hz
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw34018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw34018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34018 raw34018Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw34018 raw34018Labels = mixedMoment B raw34018step0 raw34018step0Labels := by
      have hz : ∀ j, raw34018 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34018step0 = (fun i j => raw34018 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34018step0 raw34018; decide +kernel
      have hl : raw34018step0Labels = raw34018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34018 raw34018Labels permutation520 hz
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw34019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34019 raw34019Labels = mixedMoment B node3069 node3069Labels := by
  calc
    mixedMoment B raw34019 raw34019Labels = mixedMoment B raw34019step0 raw34019step0Labels := by
      have ha : raw34019step0 = (fun i j => raw34019 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34019step0 raw34019; decide +kernel
      have hl : raw34019step0Labels = raw34019Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34019 raw34019Labels permutation212 permutation6
    mixedMoment B raw34019step0 raw34019step0Labels = mixedMoment B raw34019step1 raw34019step1Labels := by
      have ha : raw34019step1 = -raw34019step0 := by apply Matrix.ext; change ∀ i j, raw34019step1 i j = -(raw34019step0 i j); unfold raw34019step1 raw34019step0; decide +kernel
      have hl : raw34019step1Labels = raw34019step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3069 node3069Labels := by rfl

def raw34020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34020 raw34020Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw34020 raw34020Labels = mixedMoment B raw34020step0 raw34020step0Labels := by
      have ha : raw34020step0 = (fun i j => raw34020 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34020step0 raw34020; decide +kernel
      have hl : raw34020step0Labels = raw34020Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34020 raw34020Labels permutation212 permutation6
    mixedMoment B raw34020step0 raw34020step0Labels = mixedMoment B raw34020step1 raw34020step1Labels := by
      have ha : raw34020step1 = -raw34020step0 := by apply Matrix.ext; change ∀ i j, raw34020step1 i j = -(raw34020step0 i j); unfold raw34020step1 raw34020step0; decide +kernel
      have hl : raw34020step1Labels = raw34020step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3066 node3066Labels := by rfl

def raw34021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34021step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34021step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34021 raw34021Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw34021 raw34021Labels = mixedMoment B raw34021step0 raw34021step0Labels := by
      have hz : ∀ j, raw34021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34021step0 = (fun i j => raw34021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34021step0 raw34021; decide +kernel
      have hl : raw34021step0Labels = raw34021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34021 raw34021Labels permutation434 hz
    mixedMoment B raw34021step0 raw34021step0Labels = mixedMoment B raw34021step1 raw34021step1Labels := by
      have ha : raw34021step1 = (fun i j => raw34021step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34021step1 raw34021step0; decide +kernel
      have hl : raw34021step1Labels = raw34021step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34021step0 raw34021step0Labels permutation44 permutation6
    mixedMoment B raw34021step1 raw34021step1Labels = mixedMoment B raw34021step2 raw34021step2Labels := by
      have ha : raw34021step2 = -raw34021step1 := by apply Matrix.ext; change ∀ i j, raw34021step2 i j = -(raw34021step1 i j); unfold raw34021step2 raw34021step1; decide +kernel
      have hl : raw34021step2Labels = raw34021step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw34022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34022Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34022step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34022step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34022 raw34022Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw34022 raw34022Labels = mixedMoment B raw34022step0 raw34022step0Labels := by
      have hz : ∀ j, raw34022 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34022step0 = (fun i j => raw34022 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34022step0 raw34022; decide +kernel
      have hl : raw34022step0Labels = raw34022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34022 raw34022Labels permutation520 hz
    mixedMoment B raw34022step0 raw34022step0Labels = mixedMoment B raw34022step1 raw34022step1Labels := by
      have ha : raw34022step1 = (fun i j => raw34022step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34022step1 raw34022step0; decide +kernel
      have hl : raw34022step1Labels = raw34022step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34022step0 raw34022step0Labels permutation44 permutation6
    mixedMoment B raw34022step1 raw34022step1Labels = mixedMoment B raw34022step2 raw34022step2Labels := by
      have ha : raw34022step2 = -raw34022step1 := by apply Matrix.ext; change ∀ i j, raw34022step2 i j = -(raw34022step1 i j); unfold raw34022step2 raw34022step1; decide +kernel
      have hl : raw34022step2Labels = raw34022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw34023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34023Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34023 raw34023Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw34023 raw34023Labels = mixedMoment B raw34023step0 raw34023step0Labels := by
      have ha : raw34023step0 = (fun i j => raw34023 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34023step0 raw34023; decide +kernel
      have hl : raw34023step0Labels = raw34023Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34023 raw34023Labels permutation212 permutation6
    mixedMoment B raw34023step0 raw34023step0Labels = mixedMoment B raw34023step1 raw34023step1Labels := by
      have ha : raw34023step1 = -raw34023step0 := by apply Matrix.ext; change ∀ i j, raw34023step1 i j = -(raw34023step0 i j); unfold raw34023step1 raw34023step0; decide +kernel
      have hl : raw34023step1Labels = raw34023step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw34024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34024Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34024step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34024 raw34024Labels = mixedMoment B node1414 node1414Labels := by
  calc
    mixedMoment B raw34024 raw34024Labels = mixedMoment B raw34024step0 raw34024step0Labels := by
      have hz : ∀ j, raw34024 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34024step0 = (fun i j => raw34024 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34024step0 raw34024; decide +kernel
      have hl : raw34024step0Labels = raw34024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34024 raw34024Labels permutation265 hz
    mixedMoment B raw34024step0 raw34024step0Labels = mixedMoment B raw34024step1 raw34024step1Labels := by
      have ha : raw34024step1 = (fun i j => raw34024step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34024step1 raw34024step0; decide +kernel
      have hl : raw34024step1Labels = raw34024step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34024step0 raw34024step0Labels permutation32 permutation3
    _ = mixedMoment B node1414 node1414Labels := by rfl

def raw34025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34025Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34025step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34025 raw34025Labels = mixedMoment B node3185 node3185Labels := by
  calc
    mixedMoment B raw34025 raw34025Labels = mixedMoment B raw34025step0 raw34025step0Labels := by
      have hz : ∀ j, raw34025 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34025step0 = (fun i j => raw34025 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34025step0 raw34025; decide +kernel
      have hl : raw34025step0Labels = raw34025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34025 raw34025Labels permutation265 hz
    mixedMoment B raw34025step0 raw34025step0Labels = mixedMoment B raw34025step1 raw34025step1Labels := by
      have ha : raw34025step1 = (fun i j => raw34025step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34025step1 raw34025step0; decide +kernel
      have hl : raw34025step1Labels = raw34025step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34025step0 raw34025step0Labels permutation32 permutation3
    _ = mixedMoment B node3185 node3185Labels := by rfl

def raw34026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34026Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34026step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34026step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw34026step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34026 raw34026Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw34026 raw34026Labels = mixedMoment B raw34026step0 raw34026step0Labels := by
      have hz : ∀ j, raw34026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34026step0 = (fun i j => raw34026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34026step0 raw34026; decide +kernel
      have hl : raw34026step0Labels = raw34026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34026 raw34026Labels permutation434 hz
    mixedMoment B raw34026step0 raw34026step0Labels = mixedMoment B raw34026step1 raw34026step1Labels := by
      have hz : ∀ j, raw34026step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34026step1 = (fun i j => raw34026step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34026step1 raw34026step0; decide +kernel
      have hl : raw34026step1Labels = raw34026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34026step0 raw34026step0Labels permutation56 hz
    mixedMoment B raw34026step1 raw34026step1Labels = mixedMoment B raw34026step2 raw34026step2Labels := by
      have ha : raw34026step2 = (fun i j => raw34026step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34026step2 raw34026step1; decide +kernel
      have hl : raw34026step2Labels = raw34026step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34026step1 raw34026step1Labels permutation8 permutation3
    _ = mixedMoment B node3230 node3230Labels := by rfl

def raw34027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34027Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34027step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34027step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw34027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34027 raw34027Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw34027 raw34027Labels = mixedMoment B raw34027step0 raw34027step0Labels := by
      have hz : ∀ j, raw34027 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34027step0 = (fun i j => raw34027 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34027step0 raw34027; decide +kernel
      have hl : raw34027step0Labels = raw34027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34027 raw34027Labels permutation520 hz
    mixedMoment B raw34027step0 raw34027step0Labels = mixedMoment B raw34027step1 raw34027step1Labels := by
      have hz : ∀ j, raw34027step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34027step1 = (fun i j => raw34027step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34027step1 raw34027step0; decide +kernel
      have hl : raw34027step1Labels = raw34027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34027step0 raw34027step0Labels permutation56 hz
    mixedMoment B raw34027step1 raw34027step1Labels = mixedMoment B raw34027step2 raw34027step2Labels := by
      have ha : raw34027step2 = (fun i j => raw34027step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34027step2 raw34027step1; decide +kernel
      have hl : raw34027step2Labels = raw34027step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34027step1 raw34027step1Labels permutation8 permutation3
    _ = mixedMoment B node3230 node3230Labels := by rfl

def raw34028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34028Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34028step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34028 raw34028Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw34028 raw34028Labels = mixedMoment B raw34028step0 raw34028step0Labels := by
      have hz : ∀ j, raw34028 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34028step0 = (fun i j => raw34028 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34028step0 raw34028; decide +kernel
      have hl : raw34028step0Labels = raw34028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34028 raw34028Labels permutation265 hz
    mixedMoment B raw34028step0 raw34028step0Labels = mixedMoment B raw34028step1 raw34028step1Labels := by
      have ha : raw34028step1 = (fun i j => raw34028step0 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34028step1 raw34028step0; decide +kernel
      have hl : raw34028step1Labels = raw34028step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34028step0 raw34028step0Labels permutation40 permutation6
    mixedMoment B raw34028step1 raw34028step1Labels = mixedMoment B raw34028step2 raw34028step2Labels := by
      have ha : raw34028step2 = -raw34028step1 := by apply Matrix.ext; change ∀ i j, raw34028step2 i j = -(raw34028step1 i j); unfold raw34028step2 raw34028step1; decide +kernel
      have hl : raw34028step2Labels = raw34028step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw34029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34029Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34029 raw34029Labels = mixedMoment B node1341 node1341Labels := by
  calc
    mixedMoment B raw34029 raw34029Labels = mixedMoment B raw34029step0 raw34029step0Labels := by
      have ha : raw34029step0 = (fun i j => raw34029 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34029step0 raw34029; decide +kernel
      have hl : raw34029step0Labels = raw34029Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34029 raw34029Labels permutation152 permutation3
    _ = mixedMoment B node1341 node1341Labels := by rfl

def raw34030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34030Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34030 raw34030Labels = mixedMoment B node3140 node3140Labels := by
  calc
    mixedMoment B raw34030 raw34030Labels = mixedMoment B raw34030step0 raw34030step0Labels := by
      have ha : raw34030step0 = (fun i j => raw34030 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34030step0 raw34030; decide +kernel
      have hl : raw34030step0Labels = raw34030Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34030 raw34030Labels permutation152 permutation3
    _ = mixedMoment B node3140 node3140Labels := by rfl

def raw34031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34031Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34031step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34031 raw34031Labels = mixedMoment B node3214 node3214Labels := by
  calc
    mixedMoment B raw34031 raw34031Labels = mixedMoment B raw34031step0 raw34031step0Labels := by
      have hz : ∀ j, raw34031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34031step0 = (fun i j => raw34031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34031step0 raw34031; decide +kernel
      have hl : raw34031step0Labels = raw34031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34031 raw34031Labels permutation434 hz
    mixedMoment B raw34031step0 raw34031step0Labels = mixedMoment B raw34031step1 raw34031step1Labels := by
      have ha : raw34031step1 = (fun i j => raw34031step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34031step1 raw34031step0; decide +kernel
      have hl : raw34031step1Labels = raw34031step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34031step0 raw34031step0Labels permutation32 permutation3
    _ = mixedMoment B node3214 node3214Labels := by rfl

def raw34032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34032Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34032step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34032 raw34032Labels = mixedMoment B node3214 node3214Labels := by
  calc
    mixedMoment B raw34032 raw34032Labels = mixedMoment B raw34032step0 raw34032step0Labels := by
      have hz : ∀ j, raw34032 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34032step0 = (fun i j => raw34032 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34032step0 raw34032; decide +kernel
      have hl : raw34032step0Labels = raw34032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34032 raw34032Labels permutation520 hz
    mixedMoment B raw34032step0 raw34032step0Labels = mixedMoment B raw34032step1 raw34032step1Labels := by
      have ha : raw34032step1 = (fun i j => raw34032step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34032step1 raw34032step0; decide +kernel
      have hl : raw34032step1Labels = raw34032step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34032step0 raw34032step0Labels permutation32 permutation3
    _ = mixedMoment B node3214 node3214Labels := by rfl

def raw34033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34033 raw34033Labels = mixedMoment B node3209 node3209Labels := by
  calc
    mixedMoment B raw34033 raw34033Labels = mixedMoment B raw34033step0 raw34033step0Labels := by
      have ha : raw34033step0 = (fun i j => raw34033 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34033step0 raw34033; decide +kernel
      have hl : raw34033step0Labels = raw34033Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34033 raw34033Labels permutation170 permutation3
    _ = mixedMoment B node3209 node3209Labels := by rfl

def raw34034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34034 raw34034Labels = mixedMoment B node1330 node1330Labels := by
  calc
    mixedMoment B raw34034 raw34034Labels = mixedMoment B raw34034step0 raw34034step0Labels := by
      have ha : raw34034step0 = (fun i j => raw34034 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34034step0 raw34034; decide +kernel
      have hl : raw34034step0Labels = raw34034Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34034 raw34034Labels permutation155 permutation3
    _ = mixedMoment B node1330 node1330Labels := by rfl

def raw34035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34035 raw34035Labels = mixedMoment B node3134 node3134Labels := by
  calc
    mixedMoment B raw34035 raw34035Labels = mixedMoment B raw34035step0 raw34035step0Labels := by
      have ha : raw34035step0 = (fun i j => raw34035 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34035step0 raw34035; decide +kernel
      have hl : raw34035step0Labels = raw34035Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34035 raw34035Labels permutation155 permutation3
    _ = mixedMoment B node3134 node3134Labels := by rfl

def raw34036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34036 raw34036Labels = mixedMoment B node3163 node3163Labels := by
  calc
    mixedMoment B raw34036 raw34036Labels = mixedMoment B raw34036step0 raw34036step0Labels := by
      have ha : raw34036step0 = (fun i j => raw34036 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34036step0 raw34036; decide +kernel
      have hl : raw34036step0Labels = raw34036Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34036 raw34036Labels permutation179 permutation3
    _ = mixedMoment B node3163 node3163Labels := by rfl

def raw34037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34037step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34037 raw34037Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw34037 raw34037Labels = mixedMoment B raw34037step0 raw34037step0Labels := by
      have hz : ∀ j, raw34037 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34037step0 = (fun i j => raw34037 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34037step0 raw34037; decide +kernel
      have hl : raw34037step0Labels = raw34037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34037 raw34037Labels permutation520 hz
    mixedMoment B raw34037step0 raw34037step0Labels = mixedMoment B raw34037step1 raw34037step1Labels := by
      have ha : raw34037step1 = (fun i j => raw34037step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34037step1 raw34037step0; decide +kernel
      have hl : raw34037step1Labels = raw34037step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34037step0 raw34037step0Labels permutation33 permutation3
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw34038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34038 raw34038Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw34038 raw34038Labels = mixedMoment B raw34038step0 raw34038step0Labels := by
      have ha : raw34038step0 = (fun i j => raw34038 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34038step0 raw34038; decide +kernel
      have hl : raw34038step0Labels = raw34038Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34038 raw34038Labels permutation157 permutation3
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw34039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34039 raw34039Labels = mixedMoment B node1330 node1330Labels := by
  calc
    mixedMoment B raw34039 raw34039Labels = mixedMoment B raw34039step0 raw34039step0Labels := by
      have ha : raw34039step0 = (fun i j => raw34039 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34039step0 raw34039; decide +kernel
      have hl : raw34039step0Labels = raw34039Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34039 raw34039Labels permutation153 permutation3
    _ = mixedMoment B node1330 node1330Labels := by rfl

def raw34040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34040 raw34040Labels = mixedMoment B node3134 node3134Labels := by
  calc
    mixedMoment B raw34040 raw34040Labels = mixedMoment B raw34040step0 raw34040step0Labels := by
      have ha : raw34040step0 = (fun i j => raw34040 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34040step0 raw34040; decide +kernel
      have hl : raw34040step0Labels = raw34040Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34040 raw34040Labels permutation153 permutation3
    _ = mixedMoment B node3134 node3134Labels := by rfl

def raw34041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34041 raw34041Labels = mixedMoment B node3163 node3163Labels := by
  calc
    mixedMoment B raw34041 raw34041Labels = mixedMoment B raw34041step0 raw34041step0Labels := by
      have ha : raw34041step0 = (fun i j => raw34041 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34041step0 raw34041; decide +kernel
      have hl : raw34041step0Labels = raw34041Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34041 raw34041Labels permutation177 permutation3
    _ = mixedMoment B node3163 node3163Labels := by rfl

def raw34042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34042 raw34042Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw34042 raw34042Labels = mixedMoment B raw34042step0 raw34042step0Labels := by
      have hz : ∀ j, raw34042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34042step0 = (fun i j => raw34042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34042step0 raw34042; decide +kernel
      have hl : raw34042step0Labels = raw34042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34042 raw34042Labels permutation434 hz
    mixedMoment B raw34042step0 raw34042step0Labels = mixedMoment B raw34042step1 raw34042step1Labels := by
      have ha : raw34042step1 = (fun i j => raw34042step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34042step1 raw34042step0; decide +kernel
      have hl : raw34042step1Labels = raw34042step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34042step0 raw34042step0Labels permutation33 permutation3
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw34043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34043 raw34043Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw34043 raw34043Labels = mixedMoment B raw34043step0 raw34043step0Labels := by
      have ha : raw34043step0 = (fun i j => raw34043 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34043step0 raw34043; decide +kernel
      have hl : raw34043step0Labels = raw34043Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34043 raw34043Labels permutation156 permutation3
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw34044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34044 raw34044Labels = mixedMoment B node1329 node1329Labels := by
  calc
    mixedMoment B raw34044 raw34044Labels = mixedMoment B raw34044step0 raw34044step0Labels := by
      have ha : raw34044step0 = (fun i j => raw34044 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34044step0 raw34044; decide +kernel
      have hl : raw34044step0Labels = raw34044Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34044 raw34044Labels permutation152 permutation3
    _ = mixedMoment B node1329 node1329Labels := by rfl

def raw34045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw34045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw34045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34045 raw34045Labels = mixedMoment B node2890 node2890Labels := by
  calc
    mixedMoment B raw34045 raw34045Labels = mixedMoment B raw34045step0 raw34045step0Labels := by
      have ha : raw34045step0 = (fun i j => raw34045 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34045step0 raw34045; decide +kernel
      have hl : raw34045step0Labels = raw34045Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34045 raw34045Labels permutation664 permutation3
    mixedMoment B raw34045step0 raw34045step0Labels = mixedMoment B raw34045step1 raw34045step1Labels := by
      have ha : raw34045step1 = -raw34045step0 := by apply Matrix.ext; change ∀ i j, raw34045step1 i j = -(raw34045step0 i j); unfold raw34045step1 raw34045step0; decide +kernel
      have hl : raw34045step1Labels = raw34045step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2890 node2890Labels := by rfl

def raw34046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw34046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34046 raw34046Labels = mixedMoment B node2895 node2895Labels := by
  calc
    mixedMoment B raw34046 raw34046Labels = mixedMoment B raw34046step0 raw34046step0Labels := by
      have ha : raw34046step0 = (fun i j => raw34046 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34046step0 raw34046; decide +kernel
      have hl : raw34046step0Labels = raw34046Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34046 raw34046Labels permutation662 permutation3
    mixedMoment B raw34046step0 raw34046step0Labels = mixedMoment B raw34046step1 raw34046step1Labels := by
      have ha : raw34046step1 = -raw34046step0 := by apply Matrix.ext; change ∀ i j, raw34046step1 i j = -(raw34046step0 i j); unfold raw34046step1 raw34046step0; decide +kernel
      have hl : raw34046step1Labels = raw34046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2895 node2895Labels := by rfl

def raw34047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw34047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34047 raw34047Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw34047 raw34047Labels = mixedMoment B raw34047step0 raw34047step0Labels := by
      have hz : ∀ j, raw34047 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34047step0 = (fun i j => raw34047 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34047step0 raw34047; decide +kernel
      have hl : raw34047step0Labels = raw34047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34047 raw34047Labels permutation434 hz
    mixedMoment B raw34047step0 raw34047step0Labels = mixedMoment B raw34047step1 raw34047step1Labels := by
      have ha : raw34047step1 = (fun i j => raw34047step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34047step1 raw34047step0; decide +kernel
      have hl : raw34047step1Labels = raw34047step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34047step0 raw34047step0Labels permutation151 permutation3
    mixedMoment B raw34047step1 raw34047step1Labels = mixedMoment B raw34047step2 raw34047step2Labels := by
      have ha : raw34047step2 = -raw34047step1 := by apply Matrix.ext; change ∀ i j, raw34047step2 i j = -(raw34047step1 i j); unfold raw34047step2 raw34047step1; decide +kernel
      have hl : raw34047step2Labels = raw34047step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2941 node2941Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
