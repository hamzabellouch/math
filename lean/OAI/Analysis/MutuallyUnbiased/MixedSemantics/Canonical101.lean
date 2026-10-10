import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12928 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw12928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12928step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12928 raw12928Labels = mixedMoment B node3551 node3551Labels := by
  calc
    mixedMoment B raw12928 raw12928Labels = mixedMoment B raw12928step0 raw12928step0Labels := by
      have ha : raw12928step0 = (fun i j => raw12928 (permutation213 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12928step0 raw12928; decide +kernel
      have hl : raw12928step0Labels = raw12928Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12928 raw12928Labels permutation213 permutation4
    mixedMoment B raw12928step0 raw12928step0Labels = mixedMoment B raw12928step1 raw12928step1Labels := by
      have ha : raw12928step1 = -raw12928step0 := by apply Matrix.ext; change ∀ i j, raw12928step1 i j = -(raw12928step0 i j); unfold raw12928step1 raw12928step0; decide +kernel
      have hl : raw12928step1Labels = raw12928step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3551 node3551Labels := by rfl

def raw12929 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw12929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12929step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12929 raw12929Labels = mixedMoment B node3567 node3567Labels := by
  calc
    mixedMoment B raw12929 raw12929Labels = mixedMoment B raw12929step0 raw12929step0Labels := by
      have ha : raw12929step0 = (fun i j => raw12929 (permutation216 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12929step0 raw12929; decide +kernel
      have hl : raw12929step0Labels = raw12929Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12929 raw12929Labels permutation216 permutation4
    mixedMoment B raw12929step0 raw12929step0Labels = mixedMoment B raw12929step1 raw12929step1Labels := by
      have ha : raw12929step1 = -raw12929step0 := by apply Matrix.ext; change ∀ i j, raw12929step1 i j = -(raw12929step0 i j); unfold raw12929step1 raw12929step0; decide +kernel
      have hl : raw12929step1Labels = raw12929step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3567 node3567Labels := by rfl

def raw12930 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw12930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw12930step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12930 raw12930Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw12930 raw12930Labels = mixedMoment B raw12930step0 raw12930step0Labels := by
      have hz : ∀ j, raw12930 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12930step0 = (fun i j => raw12930 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12930step0 raw12930; decide +kernel
      have hl : raw12930step0Labels = raw12930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12930 raw12930Labels permutation265 hz
    mixedMoment B raw12930step0 raw12930step0Labels = mixedMoment B raw12930step1 raw12930step1Labels := by
      have ha : raw12930step1 = (fun i j => raw12930step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12930step1 raw12930step0; decide +kernel
      have hl : raw12930step1Labels = raw12930step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12930step0 raw12930step0Labels permutation41 permutation4
    mixedMoment B raw12930step1 raw12930step1Labels = mixedMoment B raw12930step2 raw12930step2Labels := by
      have ha : raw12930step2 = -raw12930step1 := by apply Matrix.ext; change ∀ i j, raw12930step2 i j = -(raw12930step1 i j); unfold raw12930step2 raw12930step1; decide +kernel
      have hl : raw12930step2Labels = raw12930step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw12931 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw12931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12931 raw12931Labels = mixedMoment B node2929 node2929Labels := by
  calc
    mixedMoment B raw12931 raw12931Labels = mixedMoment B raw12931step0 raw12931step0Labels := by
      have hz : ∀ j, raw12931 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12931step0 = (fun i j => raw12931 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12931step0 raw12931; decide +kernel
      have hl : raw12931step0Labels = raw12931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12931 raw12931Labels permutation265 hz
    mixedMoment B raw12931step0 raw12931step0Labels = mixedMoment B raw12931step1 raw12931step1Labels := by
      have ha : raw12931step1 = (fun i j => raw12931step0 (permutation96 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12931step1 raw12931step0; decide +kernel
      have hl : raw12931step1Labels = raw12931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12931step0 raw12931step0Labels permutation96 permutation2
    _ = mixedMoment B node2929 node2929Labels := by rfl

def raw12932 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12932step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12932 raw12932Labels = mixedMoment B node3152 node3152Labels := by
  calc
    mixedMoment B raw12932 raw12932Labels = mixedMoment B raw12932step0 raw12932step0Labels := by
      have hz : ∀ j, raw12932 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12932step0 = (fun i j => raw12932 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12932step0 raw12932; decide +kernel
      have hl : raw12932step0Labels = raw12932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12932 raw12932Labels permutation265 hz
    mixedMoment B raw12932step0 raw12932step0Labels = mixedMoment B raw12932step1 raw12932step1Labels := by
      have ha : raw12932step1 = (fun i j => raw12932step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12932step1 raw12932step0; decide +kernel
      have hl : raw12932step1Labels = raw12932step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12932step0 raw12932step0Labels permutation60 permutation2
    mixedMoment B raw12932step1 raw12932step1Labels = mixedMoment B raw12932step2 raw12932step2Labels := by
      have ha : raw12932step2 = -raw12932step1 := by apply Matrix.ext; change ∀ i j, raw12932step2 i j = -(raw12932step1 i j); unfold raw12932step2 raw12932step1; decide +kernel
      have hl : raw12932step2Labels = raw12932step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3152 node3152Labels := by rfl

def raw12933 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12933step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12933step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12933 raw12933Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw12933 raw12933Labels = mixedMoment B raw12933step0 raw12933step0Labels := by
      have hz : ∀ j, raw12933 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12933step0 = (fun i j => raw12933 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12933step0 raw12933; decide +kernel
      have hl : raw12933step0Labels = raw12933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12933 raw12933Labels permutation265 hz
    mixedMoment B raw12933step0 raw12933step0Labels = mixedMoment B raw12933step1 raw12933step1Labels := by
      have ha : raw12933step1 = (fun i j => raw12933step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12933step1 raw12933step0; decide +kernel
      have hl : raw12933step1Labels = raw12933step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12933step0 raw12933step0Labels permutation59 permutation2
    mixedMoment B raw12933step1 raw12933step1Labels = mixedMoment B raw12933step2 raw12933step2Labels := by
      have ha : raw12933step2 = -raw12933step1 := by apply Matrix.ext; change ∀ i j, raw12933step2 i j = -(raw12933step1 i j); unfold raw12933step2 raw12933step1; decide +kernel
      have hl : raw12933step2Labels = raw12933step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3158 node3158Labels := by rfl

def raw12934 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw12934step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12934 raw12934Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw12934 raw12934Labels = mixedMoment B raw12934step0 raw12934step0Labels := by
      have hz : ∀ j, raw12934 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12934step0 = (fun i j => raw12934 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12934step0 raw12934; decide +kernel
      have hl : raw12934step0Labels = raw12934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12934 raw12934Labels permutation265 hz
    mixedMoment B raw12934step0 raw12934step0Labels = mixedMoment B raw12934step1 raw12934step1Labels := by
      have ha : raw12934step1 = (fun i j => raw12934step0 (permutation96 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12934step1 raw12934step0; decide +kernel
      have hl : raw12934step1Labels = raw12934step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12934step0 raw12934step0Labels permutation96 permutation2
    _ = mixedMoment B node3079 node3079Labels := by rfl

def raw12935 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12935step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12935 raw12935Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw12935 raw12935Labels = mixedMoment B raw12935step0 raw12935step0Labels := by
      have hz : ∀ j, raw12935 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12935step0 = (fun i j => raw12935 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12935step0 raw12935; decide +kernel
      have hl : raw12935step0Labels = raw12935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12935 raw12935Labels permutation265 hz
    mixedMoment B raw12935step0 raw12935step0Labels = mixedMoment B raw12935step1 raw12935step1Labels := by
      have ha : raw12935step1 = (fun i j => raw12935step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12935step1 raw12935step0; decide +kernel
      have hl : raw12935step1Labels = raw12935step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12935step0 raw12935step0Labels permutation41 permutation4
    mixedMoment B raw12935step1 raw12935step1Labels = mixedMoment B raw12935step2 raw12935step2Labels := by
      have ha : raw12935step2 = -raw12935step1 := by apply Matrix.ext; change ∀ i j, raw12935step2 i j = -(raw12935step1 i j); unfold raw12935step2 raw12935step1; decide +kernel
      have hl : raw12935step2Labels = raw12935step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw12936 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12936 raw12936Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw12936 raw12936Labels = mixedMoment B raw12936step0 raw12936step0Labels := by
      have hz : ∀ j, raw12936 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12936step0 = (fun i j => raw12936 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12936step0 raw12936; decide +kernel
      have hl : raw12936step0Labels = raw12936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12936 raw12936Labels permutation265 hz
    mixedMoment B raw12936step0 raw12936step0Labels = mixedMoment B raw12936step1 raw12936step1Labels := by
      have ha : raw12936step1 = (fun i j => raw12936step0 (permutation43 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12936step1 raw12936step0; decide +kernel
      have hl : raw12936step1Labels = raw12936step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12936step0 raw12936step0Labels permutation43 permutation4
    mixedMoment B raw12936step1 raw12936step1Labels = mixedMoment B raw12936step2 raw12936step2Labels := by
      have ha : raw12936step2 = -raw12936step1 := by apply Matrix.ext; change ∀ i j, raw12936step2 i j = -(raw12936step1 i j); unfold raw12936step2 raw12936step1; decide +kernel
      have hl : raw12936step2Labels = raw12936step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw12937 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12937 raw12937Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw12937 raw12937Labels = mixedMoment B raw12937step0 raw12937step0Labels := by
      have hz : ∀ j, raw12937 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12937step0 = (fun i j => raw12937 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12937step0 raw12937; decide +kernel
      have hl : raw12937step0Labels = raw12937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12937 raw12937Labels permutation265 hz
    mixedMoment B raw12937step0 raw12937step0Labels = mixedMoment B raw12937step1 raw12937step1Labels := by
      have ha : raw12937step1 = (fun i j => raw12937step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12937step1 raw12937step0; decide +kernel
      have hl : raw12937step1Labels = raw12937step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12937step0 raw12937step0Labels permutation47 permutation4
    mixedMoment B raw12937step1 raw12937step1Labels = mixedMoment B raw12937step2 raw12937step2Labels := by
      have ha : raw12937step2 = -raw12937step1 := by apply Matrix.ext; change ∀ i j, raw12937step2 i j = -(raw12937step1 i j); unfold raw12937step2 raw12937step1; decide +kernel
      have hl : raw12937step2Labels = raw12937step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw12938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12938 raw12938Labels = mixedMoment B node5437 node5437Labels := by
  calc
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw12939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw12939step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12939step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12939step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12939step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12939 raw12939Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw12939 raw12939Labels = mixedMoment B raw12939step0 raw12939step0Labels := by
      have hz : ∀ j, raw12939 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12939step0 = (fun i j => raw12939 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12939step0 raw12939; decide +kernel
      have hl : raw12939step0Labels = raw12939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12939 raw12939Labels permutation265 hz
    mixedMoment B raw12939step0 raw12939step0Labels = mixedMoment B raw12939step1 raw12939step1Labels := by
      have ha : raw12939step1 = (fun i j => raw12939step0 (permutation56 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12939step1 raw12939step0; decide +kernel
      have hl : raw12939step1Labels = raw12939step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12939step0 raw12939step0Labels permutation56 permutation4
    mixedMoment B raw12939step1 raw12939step1Labels = mixedMoment B raw12939step2 raw12939step2Labels := by
      have ha : raw12939step2 = -raw12939step1 := by apply Matrix.ext; change ∀ i j, raw12939step2 i j = -(raw12939step1 i j); unfold raw12939step2 raw12939step1; decide +kernel
      have hl : raw12939step2Labels = raw12939step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12939step2 raw12939step2Labels = mixedMoment B raw12939step3 raw12939step3Labels := by
      have ha : raw12939step3 = raw12939step2 := by apply Matrix.ext; unfold raw12939step3 raw12939step2; decide +kernel
      have hl : raw12939step2Labels = labelEmbedding7 ∘ raw12939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12939step2 raw12939step2Labels raw12939step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw12940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12940step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12940step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12940step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12940step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12940 raw12940Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw12940 raw12940Labels = mixedMoment B raw12940step0 raw12940step0Labels := by
      have hz : ∀ j, raw12940 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12940step0 = (fun i j => raw12940 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12940step0 raw12940; decide +kernel
      have hl : raw12940step0Labels = raw12940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12940 raw12940Labels permutation434 hz
    mixedMoment B raw12940step0 raw12940step0Labels = mixedMoment B raw12940step1 raw12940step1Labels := by
      have hz : ∀ j, raw12940step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12940step1 = (fun i j => raw12940step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12940step1 raw12940step0; decide +kernel
      have hl : raw12940step1Labels = raw12940step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12940step0 raw12940step0Labels permutation56 hz
    mixedMoment B raw12940step1 raw12940step1Labels = mixedMoment B raw12940step2 raw12940step2Labels := by
      have ha : raw12940step2 = (fun i j => raw12940step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12940step2 raw12940step1; decide +kernel
      have hl : raw12940step2Labels = raw12940step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12940step1 raw12940step1Labels permutation17 permutation6
    mixedMoment B raw12940step2 raw12940step2Labels = mixedMoment B raw12940step3 raw12940step3Labels := by
      have ha : raw12940step3 = raw12940step2 := by apply Matrix.ext; unfold raw12940step3 raw12940step2; decide +kernel
      have hl : raw12940step2Labels = labelEmbedding9 ∘ raw12940step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12940step2 raw12940step2Labels raw12940step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw12941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw12941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12941step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12941step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12941step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12941 raw12941Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw12941 raw12941Labels = mixedMoment B raw12941step0 raw12941step0Labels := by
      have hz : ∀ j, raw12941 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12941step0 = (fun i j => raw12941 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12941step0 raw12941; decide +kernel
      have hl : raw12941step0Labels = raw12941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12941 raw12941Labels permutation520 hz
    mixedMoment B raw12941step0 raw12941step0Labels = mixedMoment B raw12941step1 raw12941step1Labels := by
      have hz : ∀ j, raw12941step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12941step1 = (fun i j => raw12941step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12941step1 raw12941step0; decide +kernel
      have hl : raw12941step1Labels = raw12941step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12941step0 raw12941step0Labels permutation56 hz
    mixedMoment B raw12941step1 raw12941step1Labels = mixedMoment B raw12941step2 raw12941step2Labels := by
      have ha : raw12941step2 = (fun i j => raw12941step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12941step2 raw12941step1; decide +kernel
      have hl : raw12941step2Labels = raw12941step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12941step1 raw12941step1Labels permutation17 permutation6
    mixedMoment B raw12941step2 raw12941step2Labels = mixedMoment B raw12941step3 raw12941step3Labels := by
      have ha : raw12941step3 = raw12941step2 := by apply Matrix.ext; unfold raw12941step3 raw12941step2; decide +kernel
      have hl : raw12941step2Labels = labelEmbedding9 ∘ raw12941step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12941step2 raw12941step2Labels raw12941step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw12942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw12942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12942step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12942step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12942 raw12942Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw12942 raw12942Labels = mixedMoment B raw12942step0 raw12942step0Labels := by
      have hz : ∀ j, raw12942 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12942step0 = (fun i j => raw12942 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12942step0 raw12942; decide +kernel
      have hl : raw12942step0Labels = raw12942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12942 raw12942Labels permutation590 hz
    mixedMoment B raw12942step0 raw12942step0Labels = mixedMoment B raw12942step1 raw12942step1Labels := by
      have hz : ∀ j, raw12942step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12942step1 = (fun i j => raw12942step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12942step1 raw12942step0; decide +kernel
      have hl : raw12942step1Labels = raw12942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12942step0 raw12942step0Labels permutation56 hz
    mixedMoment B raw12942step1 raw12942step1Labels = mixedMoment B raw12942step2 raw12942step2Labels := by
      have ha : raw12942step2 = (fun i j => raw12942step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12942step2 raw12942step1; decide +kernel
      have hl : raw12942step2Labels = raw12942step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12942step1 raw12942step1Labels permutation17 permutation6
    mixedMoment B raw12942step2 raw12942step2Labels = mixedMoment B raw12942step3 raw12942step3Labels := by
      have ha : raw12942step3 = raw12942step2 := by apply Matrix.ext; unfold raw12942step3 raw12942step2; decide +kernel
      have hl : raw12942step2Labels = labelEmbedding9 ∘ raw12942step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12942step2 raw12942step2Labels raw12942step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw12943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12943step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12943step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12943 raw12943Labels = mixedMoment B node4569 node4569Labels := by
  calc
    mixedMoment B raw12943 raw12943Labels = mixedMoment B raw12943step0 raw12943step0Labels := by
      have ha : raw12943step0 = (fun i j => raw12943 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12943step0 raw12943; decide +kernel
      have hl : raw12943step0Labels = raw12943Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12943 raw12943Labels permutation176 permutation3
    mixedMoment B raw12943step0 raw12943step0Labels = mixedMoment B raw12943step1 raw12943step1Labels := by
      have ha : raw12943step1 = raw12943step0 := by apply Matrix.ext; unfold raw12943step1 raw12943step0; decide +kernel
      have hl : raw12943step0Labels = labelEmbedding6 ∘ raw12943step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12943step0 raw12943step0Labels raw12943step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4569 node4569Labels := by rfl

def raw12944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12944 raw12944Labels = mixedMoment B node5212 node5212Labels := by
  calc
    mixedMoment B raw12944 raw12944Labels = mixedMoment B raw12944step0 raw12944step0Labels := by
      have ha : raw12944step0 = (fun i j => raw12944 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12944step0 raw12944; decide +kernel
      have hl : raw12944step0Labels = raw12944Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12944 raw12944Labels permutation176 permutation2
    _ = mixedMoment B node5212 node5212Labels := by rfl

def raw12945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12945 raw12945Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw12945 raw12945Labels = mixedMoment B raw12945step0 raw12945step0Labels := by
      have hz : ∀ j, raw12945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12945step0 = (fun i j => raw12945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12945step0 raw12945; decide +kernel
      have hl : raw12945step0Labels = raw12945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12945 raw12945Labels permutation434 hz
    mixedMoment B raw12945step0 raw12945step0Labels = mixedMoment B raw12945step1 raw12945step1Labels := by
      have ha : raw12945step1 = (fun i j => raw12945step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12945step1 raw12945step0; decide +kernel
      have hl : raw12945step1Labels = raw12945step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12945step0 raw12945step0Labels permutation38 permutation2
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw12946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw12946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12946 raw12946Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw12946 raw12946Labels = mixedMoment B raw12946step0 raw12946step0Labels := by
      have hz : ∀ j, raw12946 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12946step0 = (fun i j => raw12946 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12946step0 raw12946; decide +kernel
      have hl : raw12946step0Labels = raw12946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12946 raw12946Labels permutation520 hz
    mixedMoment B raw12946step0 raw12946step0Labels = mixedMoment B raw12946step1 raw12946step1Labels := by
      have ha : raw12946step1 = (fun i j => raw12946step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12946step1 raw12946step0; decide +kernel
      have hl : raw12946step1Labels = raw12946step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12946step0 raw12946step0Labels permutation38 permutation2
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw12947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw12947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12947 raw12947Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw12947 raw12947Labels = mixedMoment B raw12947step0 raw12947step0Labels := by
      have hz : ∀ j, raw12947 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12947step0 = (fun i j => raw12947 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12947step0 raw12947; decide +kernel
      have hl : raw12947step0Labels = raw12947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12947 raw12947Labels permutation590 hz
    mixedMoment B raw12947step0 raw12947step0Labels = mixedMoment B raw12947step1 raw12947step1Labels := by
      have ha : raw12947step1 = (fun i j => raw12947step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12947step1 raw12947step0; decide +kernel
      have hl : raw12947step1Labels = raw12947step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12947step0 raw12947step0Labels permutation38 permutation2
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw12948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12948step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12948step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12948 raw12948Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw12948 raw12948Labels = mixedMoment B raw12948step0 raw12948step0Labels := by
      have hz : ∀ j, raw12948 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12948step0 = (fun i j => raw12948 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12948step0 raw12948; decide +kernel
      have hl : raw12948step0Labels = raw12948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12948 raw12948Labels permutation265 hz
    mixedMoment B raw12948step0 raw12948step0Labels = mixedMoment B raw12948step1 raw12948step1Labels := by
      have ha : raw12948step1 = (fun i j => raw12948step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12948step1 raw12948step0; decide +kernel
      have hl : raw12948step1Labels = raw12948step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12948step0 raw12948step0Labels permutation32 permutation3
    mixedMoment B raw12948step1 raw12948step1Labels = mixedMoment B raw12948step2 raw12948step2Labels := by
      have ha : raw12948step2 = raw12948step1 := by apply Matrix.ext; unfold raw12948step2 raw12948step1; decide +kernel
      have hl : raw12948step1Labels = labelEmbedding6 ∘ raw12948step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12948step1 raw12948step1Labels raw12948step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw12949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12949 raw12949Labels = mixedMoment B node5166 node5166Labels := by
  calc
    mixedMoment B raw12949 raw12949Labels = mixedMoment B raw12949step0 raw12949step0Labels := by
      have ha : raw12949step0 = (fun i j => raw12949 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12949step0 raw12949; decide +kernel
      have hl : raw12949step0Labels = raw12949Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12949 raw12949Labels permutation161 permutation2
    _ = mixedMoment B node5166 node5166Labels := by rfl

def raw12950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12950step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12950step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12950 raw12950Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw12950 raw12950Labels = mixedMoment B raw12950step0 raw12950step0Labels := by
      have hz : ∀ j, raw12950 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12950step0 = (fun i j => raw12950 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12950step0 raw12950; decide +kernel
      have hl : raw12950step0Labels = raw12950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12950 raw12950Labels permutation434 hz
    mixedMoment B raw12950step0 raw12950step0Labels = mixedMoment B raw12950step1 raw12950step1Labels := by
      have hz : ∀ j, raw12950step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12950step1 = (fun i j => raw12950step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12950step1 raw12950step0; decide +kernel
      have hl : raw12950step1Labels = raw12950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12950step0 raw12950step0Labels permutation56 hz
    mixedMoment B raw12950step1 raw12950step1Labels = mixedMoment B raw12950step2 raw12950step2Labels := by
      have ha : raw12950step2 = (fun i j => raw12950step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12950step2 raw12950step1; decide +kernel
      have hl : raw12950step2Labels = raw12950step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12950step1 raw12950step1Labels permutation11 permutation2
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw12951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw12951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12951 raw12951Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw12951 raw12951Labels = mixedMoment B raw12951step0 raw12951step0Labels := by
      have hz : ∀ j, raw12951 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12951step0 = (fun i j => raw12951 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12951step0 raw12951; decide +kernel
      have hl : raw12951step0Labels = raw12951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12951 raw12951Labels permutation520 hz
    mixedMoment B raw12951step0 raw12951step0Labels = mixedMoment B raw12951step1 raw12951step1Labels := by
      have hz : ∀ j, raw12951step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12951step1 = (fun i j => raw12951step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12951step1 raw12951step0; decide +kernel
      have hl : raw12951step1Labels = raw12951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12951step0 raw12951step0Labels permutation56 hz
    mixedMoment B raw12951step1 raw12951step1Labels = mixedMoment B raw12951step2 raw12951step2Labels := by
      have ha : raw12951step2 = (fun i j => raw12951step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12951step2 raw12951step1; decide +kernel
      have hl : raw12951step2Labels = raw12951step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12951step1 raw12951step1Labels permutation11 permutation2
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw12952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw12952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12952step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12952 raw12952Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw12952 raw12952Labels = mixedMoment B raw12952step0 raw12952step0Labels := by
      have hz : ∀ j, raw12952 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12952step0 = (fun i j => raw12952 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12952step0 raw12952; decide +kernel
      have hl : raw12952step0Labels = raw12952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12952 raw12952Labels permutation590 hz
    mixedMoment B raw12952step0 raw12952step0Labels = mixedMoment B raw12952step1 raw12952step1Labels := by
      have hz : ∀ j, raw12952step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12952step1 = (fun i j => raw12952step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12952step1 raw12952step0; decide +kernel
      have hl : raw12952step1Labels = raw12952step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12952step0 raw12952step0Labels permutation56 hz
    mixedMoment B raw12952step1 raw12952step1Labels = mixedMoment B raw12952step2 raw12952step2Labels := by
      have ha : raw12952step2 = (fun i j => raw12952step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12952step2 raw12952step1; decide +kernel
      have hl : raw12952step2Labels = raw12952step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12952step1 raw12952step1Labels permutation11 permutation2
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw12953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12953step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12953step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12953 raw12953Labels = mixedMoment B node4570 node4570Labels := by
  calc
    mixedMoment B raw12953 raw12953Labels = mixedMoment B raw12953step0 raw12953step0Labels := by
      have hz : ∀ j, raw12953 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12953step0 = (fun i j => raw12953 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12953step0 raw12953; decide +kernel
      have hl : raw12953step0Labels = raw12953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12953 raw12953Labels permutation265 hz
    mixedMoment B raw12953step0 raw12953step0Labels = mixedMoment B raw12953step1 raw12953step1Labels := by
      have ha : raw12953step1 = (fun i j => raw12953step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12953step1 raw12953step0; decide +kernel
      have hl : raw12953step1Labels = raw12953step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12953step0 raw12953step0Labels permutation35 permutation3
    mixedMoment B raw12953step1 raw12953step1Labels = mixedMoment B raw12953step2 raw12953step2Labels := by
      have ha : raw12953step2 = raw12953step1 := by apply Matrix.ext; unfold raw12953step2 raw12953step1; decide +kernel
      have hl : raw12953step1Labels = labelEmbedding6 ∘ raw12953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12953step1 raw12953step1Labels raw12953step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4570 node4570Labels := by rfl

def raw12954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12954 raw12954Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw12954 raw12954Labels = mixedMoment B raw12954step0 raw12954step0Labels := by
      have ha : raw12954step0 = (fun i j => raw12954 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12954step0 raw12954; decide +kernel
      have hl : raw12954step0Labels = raw12954Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12954 raw12954Labels permutation155 permutation2
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw12955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12955step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12955 raw12955Labels = mixedMoment B node5213 node5213Labels := by
  calc
    mixedMoment B raw12955 raw12955Labels = mixedMoment B raw12955step0 raw12955step0Labels := by
      have hz : ∀ j, raw12955 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12955step0 = (fun i j => raw12955 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12955step0 raw12955; decide +kernel
      have hl : raw12955step0Labels = raw12955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12955 raw12955Labels permutation265 hz
    mixedMoment B raw12955step0 raw12955step0Labels = mixedMoment B raw12955step1 raw12955step1Labels := by
      have ha : raw12955step1 = (fun i j => raw12955step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12955step1 raw12955step0; decide +kernel
      have hl : raw12955step1Labels = raw12955step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12955step0 raw12955step0Labels permutation35 permutation2
    _ = mixedMoment B node5213 node5213Labels := by rfl

def raw12956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw12956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw12956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw12956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12956step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12956 raw12956Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw12956 raw12956Labels = mixedMoment B raw12956step0 raw12956step0Labels := by
      have hz : ∀ j, raw12956 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12956step0 = (fun i j => raw12956 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12956step0 raw12956; decide +kernel
      have hl : raw12956step0Labels = raw12956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12956 raw12956Labels permutation520 hz
    mixedMoment B raw12956step0 raw12956step0Labels = mixedMoment B raw12956step1 raw12956step1Labels := by
      have hz : ∀ j, raw12956step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12956step1 = (fun i j => raw12956step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12956step1 raw12956step0; decide +kernel
      have hl : raw12956step1Labels = raw12956step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12956step0 raw12956step0Labels permutation56 hz
    mixedMoment B raw12956step1 raw12956step1Labels = mixedMoment B raw12956step2 raw12956step2Labels := by
      have ha : raw12956step2 = (fun i j => raw12956step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12956step2 raw12956step1; decide +kernel
      have hl : raw12956step2Labels = raw12956step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12956step1 raw12956step1Labels permutation9 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw12957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw12957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw12957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw12957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12957 raw12957Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw12957 raw12957Labels = mixedMoment B raw12957step0 raw12957step0Labels := by
      have hz : ∀ j, raw12957 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12957step0 = (fun i j => raw12957 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12957step0 raw12957; decide +kernel
      have hl : raw12957step0Labels = raw12957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12957 raw12957Labels permutation590 hz
    mixedMoment B raw12957step0 raw12957step0Labels = mixedMoment B raw12957step1 raw12957step1Labels := by
      have hz : ∀ j, raw12957step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12957step1 = (fun i j => raw12957step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12957step1 raw12957step0; decide +kernel
      have hl : raw12957step1Labels = raw12957step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12957step0 raw12957step0Labels permutation56 hz
    mixedMoment B raw12957step1 raw12957step1Labels = mixedMoment B raw12957step2 raw12957step2Labels := by
      have ha : raw12957step2 = (fun i j => raw12957step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12957step2 raw12957step1; decide +kernel
      have hl : raw12957step2Labels = raw12957step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12957step1 raw12957step1Labels permutation9 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw12958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw12958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw12958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12958step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12958step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12958 raw12958Labels = mixedMoment B node4570 node4570Labels := by
  calc
    mixedMoment B raw12958 raw12958Labels = mixedMoment B raw12958step0 raw12958step0Labels := by
      have hz : ∀ j, raw12958 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12958step0 = (fun i j => raw12958 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12958step0 raw12958; decide +kernel
      have hl : raw12958step0Labels = raw12958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12958 raw12958Labels permutation265 hz
    mixedMoment B raw12958step0 raw12958step0Labels = mixedMoment B raw12958step1 raw12958step1Labels := by
      have ha : raw12958step1 = (fun i j => raw12958step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12958step1 raw12958step0; decide +kernel
      have hl : raw12958step1Labels = raw12958step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12958step0 raw12958step0Labels permutation33 permutation3
    mixedMoment B raw12958step1 raw12958step1Labels = mixedMoment B raw12958step2 raw12958step2Labels := by
      have ha : raw12958step2 = raw12958step1 := by apply Matrix.ext; unfold raw12958step2 raw12958step1; decide +kernel
      have hl : raw12958step1Labels = labelEmbedding6 ∘ raw12958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12958step1 raw12958step1Labels raw12958step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4570 node4570Labels := by rfl

def raw12959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw12959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12959 raw12959Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw12959 raw12959Labels = mixedMoment B raw12959step0 raw12959step0Labels := by
      have ha : raw12959step0 = (fun i j => raw12959 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12959step0 raw12959; decide +kernel
      have hl : raw12959step0Labels = raw12959Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12959 raw12959Labels permutation153 permutation2
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw12960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw12960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw12960step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12960step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12960 raw12960Labels = mixedMoment B node5213 node5213Labels := by
  calc
    mixedMoment B raw12960 raw12960Labels = mixedMoment B raw12960step0 raw12960step0Labels := by
      have hz : ∀ j, raw12960 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12960step0 = (fun i j => raw12960 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12960step0 raw12960; decide +kernel
      have hl : raw12960step0Labels = raw12960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12960 raw12960Labels permutation265 hz
    mixedMoment B raw12960step0 raw12960step0Labels = mixedMoment B raw12960step1 raw12960step1Labels := by
      have ha : raw12960step1 = (fun i j => raw12960step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12960step1 raw12960step0; decide +kernel
      have hl : raw12960step1Labels = raw12960step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12960step0 raw12960step0Labels permutation33 permutation2
    _ = mixedMoment B node5213 node5213Labels := by rfl

def raw12961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw12961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw12961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw12961step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12961step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12961 raw12961Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw12961 raw12961Labels = mixedMoment B raw12961step0 raw12961step0Labels := by
      have hz : ∀ j, raw12961 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12961step0 = (fun i j => raw12961 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12961step0 raw12961; decide +kernel
      have hl : raw12961step0Labels = raw12961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12961 raw12961Labels permutation434 hz
    mixedMoment B raw12961step0 raw12961step0Labels = mixedMoment B raw12961step1 raw12961step1Labels := by
      have hz : ∀ j, raw12961step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12961step1 = (fun i j => raw12961step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12961step1 raw12961step0; decide +kernel
      have hl : raw12961step1Labels = raw12961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12961step0 raw12961step0Labels permutation56 hz
    mixedMoment B raw12961step1 raw12961step1Labels = mixedMoment B raw12961step2 raw12961step2Labels := by
      have ha : raw12961step2 = (fun i j => raw12961step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12961step2 raw12961step1; decide +kernel
      have hl : raw12961step2Labels = raw12961step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12961step1 raw12961step1Labels permutation9 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw12962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw12962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12962step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12962 raw12962Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw12962 raw12962Labels = mixedMoment B raw12962step0 raw12962step0Labels := by
      have hz : ∀ j, raw12962 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12962step0 = (fun i j => raw12962 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12962step0 raw12962; decide +kernel
      have hl : raw12962step0Labels = raw12962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12962 raw12962Labels permutation590 hz
    mixedMoment B raw12962step0 raw12962step0Labels = mixedMoment B raw12962step1 raw12962step1Labels := by
      have hz : ∀ j, raw12962step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12962step1 = (fun i j => raw12962step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12962step1 raw12962step0; decide +kernel
      have hl : raw12962step1Labels = raw12962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12962step0 raw12962step0Labels permutation56 hz
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw12963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12963step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12963step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12963step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12963 raw12963Labels = mixedMoment B node4570 node4570Labels := by
  calc
    mixedMoment B raw12963 raw12963Labels = mixedMoment B raw12963step0 raw12963step0Labels := by
      have hz : ∀ j, raw12963 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12963step0 = (fun i j => raw12963 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12963step0 raw12963; decide +kernel
      have hl : raw12963step0Labels = raw12963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12963 raw12963Labels permutation265 hz
    mixedMoment B raw12963step0 raw12963step0Labels = mixedMoment B raw12963step1 raw12963step1Labels := by
      have ha : raw12963step1 = (fun i j => raw12963step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12963step1 raw12963step0; decide +kernel
      have hl : raw12963step1Labels = raw12963step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12963step0 raw12963step0Labels permutation32 permutation3
    mixedMoment B raw12963step1 raw12963step1Labels = mixedMoment B raw12963step2 raw12963step2Labels := by
      have ha : raw12963step2 = raw12963step1 := by apply Matrix.ext; unfold raw12963step2 raw12963step1; decide +kernel
      have hl : raw12963step1Labels = labelEmbedding6 ∘ raw12963step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12963step1 raw12963step1Labels raw12963step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4570 node4570Labels := by rfl

def raw12964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12964 raw12964Labels = mixedMoment B node5155 node5155Labels := by
  calc
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw12965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12965step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12965 raw12965Labels = mixedMoment B node5213 node5213Labels := by
  calc
    mixedMoment B raw12965 raw12965Labels = mixedMoment B raw12965step0 raw12965step0Labels := by
      have hz : ∀ j, raw12965 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12965step0 = (fun i j => raw12965 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12965step0 raw12965; decide +kernel
      have hl : raw12965step0Labels = raw12965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12965 raw12965Labels permutation265 hz
    _ = mixedMoment B node5213 node5213Labels := by rfl

def raw12966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12966 raw12966Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw12966 raw12966Labels = mixedMoment B raw12966step0 raw12966step0Labels := by
      have hz : ∀ j, raw12966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12966step0 = (fun i j => raw12966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12966step0 raw12966; decide +kernel
      have hl : raw12966step0Labels = raw12966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12966 raw12966Labels permutation434 hz
    mixedMoment B raw12966step0 raw12966step0Labels = mixedMoment B raw12966step1 raw12966step1Labels := by
      have hz : ∀ j, raw12966step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12966step1 = (fun i j => raw12966step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12966step1 raw12966step0; decide +kernel
      have hl : raw12966step1Labels = raw12966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12966step0 raw12966step0Labels permutation56 hz
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw12967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw12967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12967step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12967 raw12967Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw12967 raw12967Labels = mixedMoment B raw12967step0 raw12967step0Labels := by
      have hz : ∀ j, raw12967 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12967step0 = (fun i j => raw12967 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12967step0 raw12967; decide +kernel
      have hl : raw12967step0Labels = raw12967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12967 raw12967Labels permutation520 hz
    mixedMoment B raw12967step0 raw12967step0Labels = mixedMoment B raw12967step1 raw12967step1Labels := by
      have hz : ∀ j, raw12967step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12967step1 = (fun i j => raw12967step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12967step1 raw12967step0; decide +kernel
      have hl : raw12967step1Labels = raw12967step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12967step0 raw12967step0Labels permutation56 hz
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw12968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12968 raw12968Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw12968 raw12968Labels = mixedMoment B raw12968step0 raw12968step0Labels := by
      have ha : raw12968step0 = (fun i j => raw12968 (permutation373 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12968step0 raw12968; decide +kernel
      have hl : raw12968step0Labels = raw12968Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12968 raw12968Labels permutation373 permutation6
    _ = mixedMoment B node3899 node3899Labels := by rfl

def raw12969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12969step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12969 raw12969Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw12969 raw12969Labels = mixedMoment B raw12969step0 raw12969step0Labels := by
      have hz : ∀ j, raw12969 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12969step0 = (fun i j => raw12969 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12969step0 raw12969; decide +kernel
      have hl : raw12969step0Labels = raw12969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12969 raw12969Labels permutation265 hz
    mixedMoment B raw12969step0 raw12969step0Labels = mixedMoment B raw12969step1 raw12969step1Labels := by
      have ha : raw12969step1 = (fun i j => raw12969step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12969step1 raw12969step0; decide +kernel
      have hl : raw12969step1Labels = raw12969step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12969step0 raw12969step0Labels permutation65 permutation6
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw12970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12970step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12970step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12970 raw12970Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw12970 raw12970Labels = mixedMoment B raw12970step0 raw12970step0Labels := by
      have hz : ∀ j, raw12970 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12970step0 = (fun i j => raw12970 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12970step0 raw12970; decide +kernel
      have hl : raw12970step0Labels = raw12970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12970 raw12970Labels permutation434 hz
    mixedMoment B raw12970step0 raw12970step0Labels = mixedMoment B raw12970step1 raw12970step1Labels := by
      have hz : ∀ j, raw12970step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12970step1 = (fun i j => raw12970step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12970step1 raw12970step0; decide +kernel
      have hl : raw12970step1Labels = raw12970step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12970step0 raw12970step0Labels permutation56 hz
    mixedMoment B raw12970step1 raw12970step1Labels = mixedMoment B raw12970step2 raw12970step2Labels := by
      have ha : raw12970step2 = (fun i j => raw12970step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12970step2 raw12970step1; decide +kernel
      have hl : raw12970step2Labels = raw12970step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12970step1 raw12970step1Labels permutation17 permutation6
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw12971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw12971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12971step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12971 raw12971Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw12971 raw12971Labels = mixedMoment B raw12971step0 raw12971step0Labels := by
      have hz : ∀ j, raw12971 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12971step0 = (fun i j => raw12971 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12971step0 raw12971; decide +kernel
      have hl : raw12971step0Labels = raw12971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12971 raw12971Labels permutation520 hz
    mixedMoment B raw12971step0 raw12971step0Labels = mixedMoment B raw12971step1 raw12971step1Labels := by
      have hz : ∀ j, raw12971step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12971step1 = (fun i j => raw12971step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12971step1 raw12971step0; decide +kernel
      have hl : raw12971step1Labels = raw12971step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12971step0 raw12971step0Labels permutation56 hz
    mixedMoment B raw12971step1 raw12971step1Labels = mixedMoment B raw12971step2 raw12971step2Labels := by
      have ha : raw12971step2 = (fun i j => raw12971step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12971step2 raw12971step1; decide +kernel
      have hl : raw12971step2Labels = raw12971step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12971step1 raw12971step1Labels permutation17 permutation6
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw12972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw12972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12972step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12972 raw12972Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw12972 raw12972Labels = mixedMoment B raw12972step0 raw12972step0Labels := by
      have hz : ∀ j, raw12972 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12972step0 = (fun i j => raw12972 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12972step0 raw12972; decide +kernel
      have hl : raw12972step0Labels = raw12972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12972 raw12972Labels permutation590 hz
    mixedMoment B raw12972step0 raw12972step0Labels = mixedMoment B raw12972step1 raw12972step1Labels := by
      have hz : ∀ j, raw12972step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12972step1 = (fun i j => raw12972step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12972step1 raw12972step0; decide +kernel
      have hl : raw12972step1Labels = raw12972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12972step0 raw12972step0Labels permutation56 hz
    mixedMoment B raw12972step1 raw12972step1Labels = mixedMoment B raw12972step2 raw12972step2Labels := by
      have ha : raw12972step2 = (fun i j => raw12972step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12972step2 raw12972step1; decide +kernel
      have hl : raw12972step2Labels = raw12972step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12972step1 raw12972step1Labels permutation17 permutation6
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw12973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12973 raw12973Labels = mixedMoment B node1187 node1187Labels := by
  calc
    mixedMoment B raw12973 raw12973Labels = mixedMoment B raw12973step0 raw12973step0Labels := by
      have ha : raw12973step0 = (fun i j => raw12973 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12973step0 raw12973; decide +kernel
      have hl : raw12973step0Labels = raw12973Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12973 raw12973Labels permutation176 permutation3
    _ = mixedMoment B node1187 node1187Labels := by rfl

def raw12974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12974 raw12974Labels = mixedMoment B node2839 node2839Labels := by
  calc
    mixedMoment B raw12974 raw12974Labels = mixedMoment B raw12974step0 raw12974step0Labels := by
      have ha : raw12974step0 = (fun i j => raw12974 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12974step0 raw12974; decide +kernel
      have hl : raw12974step0Labels = raw12974Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12974 raw12974Labels permutation176 permutation3
    _ = mixedMoment B node2839 node2839Labels := by rfl

def raw12975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12975 raw12975Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw12975 raw12975Labels = mixedMoment B raw12975step0 raw12975step0Labels := by
      have hz : ∀ j, raw12975 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12975step0 = (fun i j => raw12975 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12975step0 raw12975; decide +kernel
      have hl : raw12975step0Labels = raw12975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12975 raw12975Labels permutation434 hz
    mixedMoment B raw12975step0 raw12975step0Labels = mixedMoment B raw12975step1 raw12975step1Labels := by
      have ha : raw12975step1 = (fun i j => raw12975step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12975step1 raw12975step0; decide +kernel
      have hl : raw12975step1Labels = raw12975step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12975step0 raw12975step0Labels permutation38 permutation3
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw12976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw12976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12976 raw12976Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw12976 raw12976Labels = mixedMoment B raw12976step0 raw12976step0Labels := by
      have hz : ∀ j, raw12976 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12976step0 = (fun i j => raw12976 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12976step0 raw12976; decide +kernel
      have hl : raw12976step0Labels = raw12976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12976 raw12976Labels permutation520 hz
    mixedMoment B raw12976step0 raw12976step0Labels = mixedMoment B raw12976step1 raw12976step1Labels := by
      have ha : raw12976step1 = (fun i j => raw12976step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12976step1 raw12976step0; decide +kernel
      have hl : raw12976step1Labels = raw12976step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12976step0 raw12976step0Labels permutation38 permutation3
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw12977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw12977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12977 raw12977Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw12977 raw12977Labels = mixedMoment B raw12977step0 raw12977step0Labels := by
      have hz : ∀ j, raw12977 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12977step0 = (fun i j => raw12977 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12977step0 raw12977; decide +kernel
      have hl : raw12977step0Labels = raw12977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12977 raw12977Labels permutation590 hz
    mixedMoment B raw12977step0 raw12977step0Labels = mixedMoment B raw12977step1 raw12977step1Labels := by
      have ha : raw12977step1 = (fun i j => raw12977step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12977step1 raw12977step0; decide +kernel
      have hl : raw12977step1Labels = raw12977step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12977step0 raw12977step0Labels permutation38 permutation3
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw12978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12978 raw12978Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw12978 raw12978Labels = mixedMoment B raw12978step0 raw12978step0Labels := by
      have hz : ∀ j, raw12978 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12978step0 = (fun i j => raw12978 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12978step0 raw12978; decide +kernel
      have hl : raw12978step0Labels = raw12978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12978 raw12978Labels permutation265 hz
    mixedMoment B raw12978step0 raw12978step0Labels = mixedMoment B raw12978step1 raw12978step1Labels := by
      have ha : raw12978step1 = (fun i j => raw12978step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12978step1 raw12978step0; decide +kernel
      have hl : raw12978step1Labels = raw12978step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12978step0 raw12978step0Labels permutation32 permutation3
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw12979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12979 raw12979Labels = mixedMoment B node2953 node2953Labels := by
  calc
    mixedMoment B raw12979 raw12979Labels = mixedMoment B raw12979step0 raw12979step0Labels := by
      have ha : raw12979step0 = (fun i j => raw12979 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12979step0 raw12979; decide +kernel
      have hl : raw12979step0Labels = raw12979Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12979 raw12979Labels permutation152 permutation3
    _ = mixedMoment B node2953 node2953Labels := by rfl

def raw12980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12980step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12980step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12980 raw12980Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw12980 raw12980Labels = mixedMoment B raw12980step0 raw12980step0Labels := by
      have hz : ∀ j, raw12980 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12980step0 = (fun i j => raw12980 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12980step0 raw12980; decide +kernel
      have hl : raw12980step0Labels = raw12980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12980 raw12980Labels permutation434 hz
    mixedMoment B raw12980step0 raw12980step0Labels = mixedMoment B raw12980step1 raw12980step1Labels := by
      have hz : ∀ j, raw12980step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12980step1 = (fun i j => raw12980step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12980step1 raw12980step0; decide +kernel
      have hl : raw12980step1Labels = raw12980step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12980step0 raw12980step0Labels permutation56 hz
    mixedMoment B raw12980step1 raw12980step1Labels = mixedMoment B raw12980step2 raw12980step2Labels := by
      have ha : raw12980step2 = (fun i j => raw12980step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12980step2 raw12980step1; decide +kernel
      have hl : raw12980step2Labels = raw12980step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12980step1 raw12980step1Labels permutation8 permutation3
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw12981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw12981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12981step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12981 raw12981Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw12981 raw12981Labels = mixedMoment B raw12981step0 raw12981step0Labels := by
      have hz : ∀ j, raw12981 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12981step0 = (fun i j => raw12981 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12981step0 raw12981; decide +kernel
      have hl : raw12981step0Labels = raw12981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12981 raw12981Labels permutation520 hz
    mixedMoment B raw12981step0 raw12981step0Labels = mixedMoment B raw12981step1 raw12981step1Labels := by
      have hz : ∀ j, raw12981step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12981step1 = (fun i j => raw12981step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12981step1 raw12981step0; decide +kernel
      have hl : raw12981step1Labels = raw12981step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12981step0 raw12981step0Labels permutation56 hz
    mixedMoment B raw12981step1 raw12981step1Labels = mixedMoment B raw12981step2 raw12981step2Labels := by
      have ha : raw12981step2 = (fun i j => raw12981step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12981step2 raw12981step1; decide +kernel
      have hl : raw12981step2Labels = raw12981step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12981step1 raw12981step1Labels permutation8 permutation3
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw12982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw12982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw12982step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12982 raw12982Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw12982 raw12982Labels = mixedMoment B raw12982step0 raw12982step0Labels := by
      have hz : ∀ j, raw12982 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12982step0 = (fun i j => raw12982 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12982step0 raw12982; decide +kernel
      have hl : raw12982step0Labels = raw12982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12982 raw12982Labels permutation590 hz
    mixedMoment B raw12982step0 raw12982step0Labels = mixedMoment B raw12982step1 raw12982step1Labels := by
      have hz : ∀ j, raw12982step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12982step1 = (fun i j => raw12982step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12982step1 raw12982step0; decide +kernel
      have hl : raw12982step1Labels = raw12982step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12982step0 raw12982step0Labels permutation56 hz
    mixedMoment B raw12982step1 raw12982step1Labels = mixedMoment B raw12982step2 raw12982step2Labels := by
      have ha : raw12982step2 = (fun i j => raw12982step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12982step2 raw12982step1; decide +kernel
      have hl : raw12982step2Labels = raw12982step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12982step1 raw12982step1Labels permutation8 permutation3
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw12983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12983step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12983 raw12983Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw12983 raw12983Labels = mixedMoment B raw12983step0 raw12983step0Labels := by
      have hz : ∀ j, raw12983 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12983step0 = (fun i j => raw12983 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12983step0 raw12983; decide +kernel
      have hl : raw12983step0Labels = raw12983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12983 raw12983Labels permutation265 hz
    mixedMoment B raw12983step0 raw12983step0Labels = mixedMoment B raw12983step1 raw12983step1Labels := by
      have ha : raw12983step1 = (fun i j => raw12983step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12983step1 raw12983step0; decide +kernel
      have hl : raw12983step1Labels = raw12983step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12983step0 raw12983step0Labels permutation35 permutation3
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw12984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12984 raw12984Labels = mixedMoment B node2908 node2908Labels := by
  calc
    mixedMoment B raw12984 raw12984Labels = mixedMoment B raw12984step0 raw12984step0Labels := by
      have ha : raw12984step0 = (fun i j => raw12984 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12984step0 raw12984; decide +kernel
      have hl : raw12984step0Labels = raw12984Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12984 raw12984Labels permutation155 permutation3
    _ = mixedMoment B node2908 node2908Labels := by rfl

def raw12985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12985step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12985 raw12985Labels = mixedMoment B node2840 node2840Labels := by
  calc
    mixedMoment B raw12985 raw12985Labels = mixedMoment B raw12985step0 raw12985step0Labels := by
      have hz : ∀ j, raw12985 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12985step0 = (fun i j => raw12985 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12985step0 raw12985; decide +kernel
      have hl : raw12985step0Labels = raw12985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12985 raw12985Labels permutation265 hz
    mixedMoment B raw12985step0 raw12985step0Labels = mixedMoment B raw12985step1 raw12985step1Labels := by
      have ha : raw12985step1 = (fun i j => raw12985step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12985step1 raw12985step0; decide +kernel
      have hl : raw12985step1Labels = raw12985step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12985step0 raw12985step0Labels permutation35 permutation3
    _ = mixedMoment B node2840 node2840Labels := by rfl

def raw12986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw12986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw12986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw12986step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12986 raw12986Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw12986 raw12986Labels = mixedMoment B raw12986step0 raw12986step0Labels := by
      have hz : ∀ j, raw12986 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12986step0 = (fun i j => raw12986 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12986step0 raw12986; decide +kernel
      have hl : raw12986step0Labels = raw12986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12986 raw12986Labels permutation520 hz
    mixedMoment B raw12986step0 raw12986step0Labels = mixedMoment B raw12986step1 raw12986step1Labels := by
      have hz : ∀ j, raw12986step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12986step1 = (fun i j => raw12986step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12986step1 raw12986step0; decide +kernel
      have hl : raw12986step1Labels = raw12986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12986step0 raw12986step0Labels permutation56 hz
    mixedMoment B raw12986step1 raw12986step1Labels = mixedMoment B raw12986step2 raw12986step2Labels := by
      have ha : raw12986step2 = (fun i j => raw12986step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12986step2 raw12986step1; decide +kernel
      have hl : raw12986step2Labels = raw12986step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12986step1 raw12986step1Labels permutation9 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw12987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw12987Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw12987step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw12987step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12987 raw12987Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw12987 raw12987Labels = mixedMoment B raw12987step0 raw12987step0Labels := by
      have hz : ∀ j, raw12987 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12987step0 = (fun i j => raw12987 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12987step0 raw12987; decide +kernel
      have hl : raw12987step0Labels = raw12987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12987 raw12987Labels permutation590 hz
    mixedMoment B raw12987step0 raw12987step0Labels = mixedMoment B raw12987step1 raw12987step1Labels := by
      have hz : ∀ j, raw12987step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12987step1 = (fun i j => raw12987step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12987step1 raw12987step0; decide +kernel
      have hl : raw12987step1Labels = raw12987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12987step0 raw12987step0Labels permutation56 hz
    mixedMoment B raw12987step1 raw12987step1Labels = mixedMoment B raw12987step2 raw12987step2Labels := by
      have ha : raw12987step2 = (fun i j => raw12987step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12987step2 raw12987step1; decide +kernel
      have hl : raw12987step2Labels = raw12987step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12987step1 raw12987step1Labels permutation9 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw12988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw12988Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw12988step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12988step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12988 raw12988Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw12988 raw12988Labels = mixedMoment B raw12988step0 raw12988step0Labels := by
      have hz : ∀ j, raw12988 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12988step0 = (fun i j => raw12988 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12988step0 raw12988; decide +kernel
      have hl : raw12988step0Labels = raw12988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12988 raw12988Labels permutation265 hz
    mixedMoment B raw12988step0 raw12988step0Labels = mixedMoment B raw12988step1 raw12988step1Labels := by
      have ha : raw12988step1 = (fun i j => raw12988step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12988step1 raw12988step0; decide +kernel
      have hl : raw12988step1Labels = raw12988step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12988step0 raw12988step0Labels permutation33 permutation3
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw12989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw12989Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12989 raw12989Labels = mixedMoment B node2908 node2908Labels := by
  calc
    mixedMoment B raw12989 raw12989Labels = mixedMoment B raw12989step0 raw12989step0Labels := by
      have ha : raw12989step0 = (fun i j => raw12989 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12989step0 raw12989; decide +kernel
      have hl : raw12989step0Labels = raw12989Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12989 raw12989Labels permutation153 permutation3
    _ = mixedMoment B node2908 node2908Labels := by rfl

def raw12990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw12990Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw12990step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12990 raw12990Labels = mixedMoment B node2840 node2840Labels := by
  calc
    mixedMoment B raw12990 raw12990Labels = mixedMoment B raw12990step0 raw12990step0Labels := by
      have hz : ∀ j, raw12990 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12990step0 = (fun i j => raw12990 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12990step0 raw12990; decide +kernel
      have hl : raw12990step0Labels = raw12990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12990 raw12990Labels permutation265 hz
    mixedMoment B raw12990step0 raw12990step0Labels = mixedMoment B raw12990step1 raw12990step1Labels := by
      have ha : raw12990step1 = (fun i j => raw12990step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12990step1 raw12990step0; decide +kernel
      have hl : raw12990step1Labels = raw12990step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12990step0 raw12990step0Labels permutation33 permutation3
    _ = mixedMoment B node2840 node2840Labels := by rfl

def raw12991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw12991Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw12991step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw12991step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12991step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12991 raw12991Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw12991 raw12991Labels = mixedMoment B raw12991step0 raw12991step0Labels := by
      have hz : ∀ j, raw12991 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12991step0 = (fun i j => raw12991 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12991step0 raw12991; decide +kernel
      have hl : raw12991step0Labels = raw12991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12991 raw12991Labels permutation434 hz
    mixedMoment B raw12991step0 raw12991step0Labels = mixedMoment B raw12991step1 raw12991step1Labels := by
      have hz : ∀ j, raw12991step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12991step1 = (fun i j => raw12991step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12991step1 raw12991step0; decide +kernel
      have hl : raw12991step1Labels = raw12991step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12991step0 raw12991step0Labels permutation56 hz
    mixedMoment B raw12991step1 raw12991step1Labels = mixedMoment B raw12991step2 raw12991step2Labels := by
      have ha : raw12991step2 = (fun i j => raw12991step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12991step2 raw12991step1; decide +kernel
      have hl : raw12991step2Labels = raw12991step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12991step1 raw12991step1Labels permutation9 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw12992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw12992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12992step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12992step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12992 raw12992Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw12992 raw12992Labels = mixedMoment B raw12992step0 raw12992step0Labels := by
      have hz : ∀ j, raw12992 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12992step0 = (fun i j => raw12992 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12992step0 raw12992; decide +kernel
      have hl : raw12992step0Labels = raw12992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12992 raw12992Labels permutation590 hz
    mixedMoment B raw12992step0 raw12992step0Labels = mixedMoment B raw12992step1 raw12992step1Labels := by
      have hz : ∀ j, raw12992step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12992step1 = (fun i j => raw12992step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12992step1 raw12992step0; decide +kernel
      have hl : raw12992step1Labels = raw12992step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12992step0 raw12992step0Labels permutation56 hz
    mixedMoment B raw12992step1 raw12992step1Labels = mixedMoment B raw12992step2 raw12992step2Labels := by
      have ha : raw12992step2 = (fun i j => raw12992step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12992step2 raw12992step1; decide +kernel
      have hl : raw12992step2Labels = raw12992step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12992step1 raw12992step1Labels permutation8 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw12993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12993step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12993 raw12993Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw12993 raw12993Labels = mixedMoment B raw12993step0 raw12993step0Labels := by
      have hz : ∀ j, raw12993 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12993step0 = (fun i j => raw12993 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12993step0 raw12993; decide +kernel
      have hl : raw12993step0Labels = raw12993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12993 raw12993Labels permutation265 hz
    mixedMoment B raw12993step0 raw12993step0Labels = mixedMoment B raw12993step1 raw12993step1Labels := by
      have ha : raw12993step1 = (fun i j => raw12993step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12993step1 raw12993step0; decide +kernel
      have hl : raw12993step1Labels = raw12993step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12993step0 raw12993step0Labels permutation32 permutation3
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw12994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12994 raw12994Labels = mixedMoment B node2908 node2908Labels := by
  calc
    mixedMoment B raw12994 raw12994Labels = mixedMoment B raw12994step0 raw12994step0Labels := by
      have ha : raw12994step0 = (fun i j => raw12994 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12994step0 raw12994; decide +kernel
      have hl : raw12994step0Labels = raw12994Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12994 raw12994Labels permutation152 permutation3
    _ = mixedMoment B node2908 node2908Labels := by rfl

def raw12995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12995step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw12995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12995 raw12995Labels = mixedMoment B node2840 node2840Labels := by
  calc
    mixedMoment B raw12995 raw12995Labels = mixedMoment B raw12995step0 raw12995step0Labels := by
      have hz : ∀ j, raw12995 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12995step0 = (fun i j => raw12995 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12995step0 raw12995; decide +kernel
      have hl : raw12995step0Labels = raw12995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12995 raw12995Labels permutation265 hz
    mixedMoment B raw12995step0 raw12995step0Labels = mixedMoment B raw12995step1 raw12995step1Labels := by
      have ha : raw12995step1 = (fun i j => raw12995step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12995step1 raw12995step0; decide +kernel
      have hl : raw12995step1Labels = raw12995step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12995step0 raw12995step0Labels permutation32 permutation3
    _ = mixedMoment B node2840 node2840Labels := by rfl

def raw12996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw12996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12996step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12996step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12996 raw12996Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw12996 raw12996Labels = mixedMoment B raw12996step0 raw12996step0Labels := by
      have hz : ∀ j, raw12996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12996step0 = (fun i j => raw12996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12996step0 raw12996; decide +kernel
      have hl : raw12996step0Labels = raw12996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12996 raw12996Labels permutation434 hz
    mixedMoment B raw12996step0 raw12996step0Labels = mixedMoment B raw12996step1 raw12996step1Labels := by
      have hz : ∀ j, raw12996step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12996step1 = (fun i j => raw12996step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12996step1 raw12996step0; decide +kernel
      have hl : raw12996step1Labels = raw12996step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12996step0 raw12996step0Labels permutation56 hz
    mixedMoment B raw12996step1 raw12996step1Labels = mixedMoment B raw12996step2 raw12996step2Labels := by
      have ha : raw12996step2 = (fun i j => raw12996step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12996step2 raw12996step1; decide +kernel
      have hl : raw12996step2Labels = raw12996step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12996step1 raw12996step1Labels permutation8 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw12997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw12997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12997step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12997step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12997 raw12997Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw12997 raw12997Labels = mixedMoment B raw12997step0 raw12997step0Labels := by
      have hz : ∀ j, raw12997 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12997step0 = (fun i j => raw12997 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12997step0 raw12997; decide +kernel
      have hl : raw12997step0Labels = raw12997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12997 raw12997Labels permutation520 hz
    mixedMoment B raw12997step0 raw12997step0Labels = mixedMoment B raw12997step1 raw12997step1Labels := by
      have hz : ∀ j, raw12997step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12997step1 = (fun i j => raw12997step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12997step1 raw12997step0; decide +kernel
      have hl : raw12997step1Labels = raw12997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12997step0 raw12997step0Labels permutation56 hz
    mixedMoment B raw12997step1 raw12997step1Labels = mixedMoment B raw12997step2 raw12997step2Labels := by
      have ha : raw12997step2 = (fun i j => raw12997step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12997step2 raw12997step1; decide +kernel
      have hl : raw12997step2Labels = raw12997step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12997step1 raw12997step1Labels permutation8 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw12998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw12998step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12998step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12998step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12998step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12998 raw12998Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw12998 raw12998Labels = mixedMoment B raw12998step0 raw12998step0Labels := by
      have ha : raw12998step0 = (fun i j => raw12998 (permutation346 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12998step0 raw12998; decide +kernel
      have hl : raw12998step0Labels = raw12998Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12998 raw12998Labels permutation346 permutation6
    mixedMoment B raw12998step0 raw12998step0Labels = mixedMoment B raw12998step1 raw12998step1Labels := by
      have ha : raw12998step1 = -raw12998step0 := by apply Matrix.ext; change ∀ i j, raw12998step1 i j = -(raw12998step0 i j); unfold raw12998step1 raw12998step0; decide +kernel
      have hl : raw12998step1Labels = raw12998step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12998step1 raw12998step1Labels = mixedMoment B raw12998step2 raw12998step2Labels := by
      have ha : raw12998step2 = raw12998step1 := by apply Matrix.ext; unfold raw12998step2 raw12998step1; decide +kernel
      have hl : raw12998step1Labels = labelEmbedding9 ∘ raw12998step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12998step1 raw12998step1Labels raw12998step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw12999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12999 raw12999Labels = mixedMoment B node5474 node5474Labels := by
  calc
    mixedMoment B raw12999 raw12999Labels = mixedMoment B raw12999step0 raw12999step0Labels := by
      have hz : ∀ j, raw12999 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12999step0 = (fun i j => raw12999 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12999step0 raw12999; decide +kernel
      have hl : raw12999step0Labels = raw12999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12999 raw12999Labels permutation265 hz
    _ = mixedMoment B node5474 node5474Labels := by rfl

def raw13000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13000step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13000step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13000step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13000 raw13000Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw13000 raw13000Labels = mixedMoment B raw13000step0 raw13000step0Labels := by
      have hz : ∀ j, raw13000 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13000step0 = (fun i j => raw13000 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13000step0 raw13000; decide +kernel
      have hl : raw13000step0Labels = raw13000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13000 raw13000Labels permutation265 hz
    mixedMoment B raw13000step0 raw13000step0Labels = mixedMoment B raw13000step1 raw13000step1Labels := by
      have ha : raw13000step1 = (fun i j => raw13000step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13000step1 raw13000step0; decide +kernel
      have hl : raw13000step1Labels = raw13000step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13000step0 raw13000step0Labels permutation59 permutation6
    mixedMoment B raw13000step1 raw13000step1Labels = mixedMoment B raw13000step2 raw13000step2Labels := by
      have ha : raw13000step2 = -raw13000step1 := by apply Matrix.ext; change ∀ i j, raw13000step2 i j = -(raw13000step1 i j); unfold raw13000step2 raw13000step1; decide +kernel
      have hl : raw13000step2Labels = raw13000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13000step2 raw13000step2Labels = mixedMoment B raw13000step3 raw13000step3Labels := by
      have ha : raw13000step3 = raw13000step2 := by apply Matrix.ext; unfold raw13000step3 raw13000step2; decide +kernel
      have hl : raw13000step2Labels = labelEmbedding9 ∘ raw13000step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13000step2 raw13000step2Labels raw13000step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw13001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13001step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13001step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13001step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13001step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13001 raw13001Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw13001 raw13001Labels = mixedMoment B raw13001step0 raw13001step0Labels := by
      have hz : ∀ j, raw13001 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13001step0 = (fun i j => raw13001 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13001step0 raw13001; decide +kernel
      have hl : raw13001step0Labels = raw13001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13001 raw13001Labels permutation265 hz
    mixedMoment B raw13001step0 raw13001step0Labels = mixedMoment B raw13001step1 raw13001step1Labels := by
      have ha : raw13001step1 = (fun i j => raw13001step0 (permutation57 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13001step1 raw13001step0; decide +kernel
      have hl : raw13001step1Labels = raw13001step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13001step0 raw13001step0Labels permutation57 permutation6
    mixedMoment B raw13001step1 raw13001step1Labels = mixedMoment B raw13001step2 raw13001step2Labels := by
      have ha : raw13001step2 = -raw13001step1 := by apply Matrix.ext; change ∀ i j, raw13001step2 i j = -(raw13001step1 i j); unfold raw13001step2 raw13001step1; decide +kernel
      have hl : raw13001step2Labels = raw13001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13001step2 raw13001step2Labels = mixedMoment B raw13001step3 raw13001step3Labels := by
      have ha : raw13001step3 = raw13001step2 := by apply Matrix.ext; unfold raw13001step3 raw13001step2; decide +kernel
      have hl : raw13001step2Labels = labelEmbedding9 ∘ raw13001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13001step2 raw13001step2Labels raw13001step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw13002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13002step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13002step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13002step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13002step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13002 raw13002Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw13002 raw13002Labels = mixedMoment B raw13002step0 raw13002step0Labels := by
      have hz : ∀ j, raw13002 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13002step0 = (fun i j => raw13002 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13002step0 raw13002; decide +kernel
      have hl : raw13002step0Labels = raw13002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13002 raw13002Labels permutation265 hz
    mixedMoment B raw13002step0 raw13002step0Labels = mixedMoment B raw13002step1 raw13002step1Labels := by
      have ha : raw13002step1 = (fun i j => raw13002step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13002step1 raw13002step0; decide +kernel
      have hl : raw13002step1Labels = raw13002step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13002step0 raw13002step0Labels permutation56 permutation6
    mixedMoment B raw13002step1 raw13002step1Labels = mixedMoment B raw13002step2 raw13002step2Labels := by
      have ha : raw13002step2 = -raw13002step1 := by apply Matrix.ext; change ∀ i j, raw13002step2 i j = -(raw13002step1 i j); unfold raw13002step2 raw13002step1; decide +kernel
      have hl : raw13002step2Labels = raw13002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13002step2 raw13002step2Labels = mixedMoment B raw13002step3 raw13002step3Labels := by
      have ha : raw13002step3 = raw13002step2 := by apply Matrix.ext; unfold raw13002step3 raw13002step2; decide +kernel
      have hl : raw13002step2Labels = labelEmbedding9 ∘ raw13002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13002step2 raw13002step2Labels raw13002step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw13003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13003step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13003 raw13003Labels = mixedMoment B node4473 node4473Labels := by
  calc
    mixedMoment B raw13003 raw13003Labels = mixedMoment B raw13003step0 raw13003step0Labels := by
      have ha : raw13003step0 = (fun i j => raw13003 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13003step0 raw13003; decide +kernel
      have hl : raw13003step0Labels = raw13003Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13003 raw13003Labels permutation185 permutation3
    mixedMoment B raw13003step0 raw13003step0Labels = mixedMoment B raw13003step1 raw13003step1Labels := by
      have ha : raw13003step1 = raw13003step0 := by apply Matrix.ext; unfold raw13003step1 raw13003step0; decide +kernel
      have hl : raw13003step0Labels = labelEmbedding6 ∘ raw13003step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13003step0 raw13003step0Labels raw13003step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4473 node4473Labels := by rfl

def raw13004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13004step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13004step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13004 raw13004Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw13004 raw13004Labels = mixedMoment B raw13004step0 raw13004step0Labels := by
      have ha : raw13004step0 = (fun i j => raw13004 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13004step0 raw13004; decide +kernel
      have hl : raw13004step0Labels = raw13004Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13004 raw13004Labels permutation185 permutation3
    mixedMoment B raw13004step0 raw13004step0Labels = mixedMoment B raw13004step1 raw13004step1Labels := by
      have ha : raw13004step1 = raw13004step0 := by apply Matrix.ext; unfold raw13004step1 raw13004step0; decide +kernel
      have hl : raw13004step0Labels = labelEmbedding6 ∘ raw13004step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13004step0 raw13004step0Labels raw13004step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw13005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13005step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13005 raw13005Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw13005 raw13005Labels = mixedMoment B raw13005step0 raw13005step0Labels := by
      have ha : raw13005step0 = (fun i j => raw13005 (permutation209 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13005step0 raw13005; decide +kernel
      have hl : raw13005step0Labels = raw13005Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13005 raw13005Labels permutation209 permutation3
    mixedMoment B raw13005step0 raw13005step0Labels = mixedMoment B raw13005step1 raw13005step1Labels := by
      have ha : raw13005step1 = raw13005step0 := by apply Matrix.ext; unfold raw13005step1 raw13005step0; decide +kernel
      have hl : raw13005step0Labels = labelEmbedding6 ∘ raw13005step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13005step0 raw13005step0Labels raw13005step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw13006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13006step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13006 raw13006Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw13006 raw13006Labels = mixedMoment B raw13006step0 raw13006step0Labels := by
      have ha : raw13006step0 = (fun i j => raw13006 (permutation233 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13006step0 raw13006; decide +kernel
      have hl : raw13006step0Labels = raw13006Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13006 raw13006Labels permutation233 permutation3
    mixedMoment B raw13006step0 raw13006step0Labels = mixedMoment B raw13006step1 raw13006step1Labels := by
      have ha : raw13006step1 = raw13006step0 := by apply Matrix.ext; unfold raw13006step1 raw13006step0; decide +kernel
      have hl : raw13006step0Labels = labelEmbedding6 ∘ raw13006step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13006step0 raw13006step0Labels raw13006step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw13007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13007step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13007 raw13007Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw13007 raw13007Labels = mixedMoment B raw13007step0 raw13007step0Labels := by
      have ha : raw13007step0 = (fun i j => raw13007 (permutation255 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13007step0 raw13007; decide +kernel
      have hl : raw13007step0Labels = raw13007Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13007 raw13007Labels permutation255 permutation3
    mixedMoment B raw13007step0 raw13007step0Labels = mixedMoment B raw13007step1 raw13007step1Labels := by
      have ha : raw13007step1 = raw13007step0 := by apply Matrix.ext; unfold raw13007step1 raw13007step0; decide +kernel
      have hl : raw13007step0Labels = labelEmbedding6 ∘ raw13007step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13007step0 raw13007step0Labels raw13007step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw13008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13008step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13008step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13008step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13008step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13008 raw13008Labels = mixedMoment B node4494 node4494Labels := by
  calc
    mixedMoment B raw13008 raw13008Labels = mixedMoment B raw13008step0 raw13008step0Labels := by
      have hz : ∀ j, raw13008 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13008step0 = (fun i j => raw13008 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13008step0 raw13008; decide +kernel
      have hl : raw13008step0Labels = raw13008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13008 raw13008Labels permutation265 hz
    mixedMoment B raw13008step0 raw13008step0Labels = mixedMoment B raw13008step1 raw13008step1Labels := by
      have ha : raw13008step1 = (fun i j => raw13008step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13008step1 raw13008step0; decide +kernel
      have hl : raw13008step1Labels = raw13008step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13008step0 raw13008step0Labels permutation41 permutation3
    mixedMoment B raw13008step1 raw13008step1Labels = mixedMoment B raw13008step2 raw13008step2Labels := by
      have ha : raw13008step2 = raw13008step1 := by apply Matrix.ext; unfold raw13008step2 raw13008step1; decide +kernel
      have hl : raw13008step1Labels = labelEmbedding6 ∘ raw13008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13008step1 raw13008step1Labels raw13008step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4494 node4494Labels := by rfl

def raw13009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13009step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13009step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13009step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13009 raw13009Labels = mixedMoment B node5097 node5097Labels := by
  calc
    mixedMoment B raw13009 raw13009Labels = mixedMoment B raw13009step0 raw13009step0Labels := by
      have ha : raw13009step0 = (fun i j => raw13009 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13009step0 raw13009; decide +kernel
      have hl : raw13009step0Labels = raw13009Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13009 raw13009Labels permutation161 permutation3
    mixedMoment B raw13009step0 raw13009step0Labels = mixedMoment B raw13009step1 raw13009step1Labels := by
      have ha : raw13009step1 = raw13009step0 := by apply Matrix.ext; unfold raw13009step1 raw13009step0; decide +kernel
      have hl : raw13009step0Labels = labelEmbedding6 ∘ raw13009step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13009step0 raw13009step0Labels raw13009step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5097 node5097Labels := by rfl

def raw13010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13010step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13010step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13010 raw13010Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw13010 raw13010Labels = mixedMoment B raw13010step0 raw13010step0Labels := by
      have hz : ∀ j, raw13010 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13010step0 = (fun i j => raw13010 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13010step0 raw13010; decide +kernel
      have hl : raw13010step0Labels = raw13010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13010 raw13010Labels permutation265 hz
    mixedMoment B raw13010step0 raw13010step0Labels = mixedMoment B raw13010step1 raw13010step1Labels := by
      have ha : raw13010step1 = (fun i j => raw13010step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13010step1 raw13010step0; decide +kernel
      have hl : raw13010step1Labels = raw13010step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13010step0 raw13010step0Labels permutation41 permutation3
    mixedMoment B raw13010step1 raw13010step1Labels = mixedMoment B raw13010step2 raw13010step2Labels := by
      have ha : raw13010step2 = raw13010step1 := by apply Matrix.ext; unfold raw13010step2 raw13010step1; decide +kernel
      have hl : raw13010step1Labels = labelEmbedding6 ∘ raw13010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13010step1 raw13010step1Labels raw13010step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw13011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13011step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13011step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13011 raw13011Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw13011 raw13011Labels = mixedMoment B raw13011step0 raw13011step0Labels := by
      have hz : ∀ j, raw13011 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13011step0 = (fun i j => raw13011 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13011step0 raw13011; decide +kernel
      have hl : raw13011step0Labels = raw13011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13011 raw13011Labels permutation265 hz
    mixedMoment B raw13011step0 raw13011step0Labels = mixedMoment B raw13011step1 raw13011step1Labels := by
      have ha : raw13011step1 = (fun i j => raw13011step0 (permutation47 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13011step1 raw13011step0; decide +kernel
      have hl : raw13011step1Labels = raw13011step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13011step0 raw13011step0Labels permutation47 permutation3
    mixedMoment B raw13011step1 raw13011step1Labels = mixedMoment B raw13011step2 raw13011step2Labels := by
      have ha : raw13011step2 = raw13011step1 := by apply Matrix.ext; unfold raw13011step2 raw13011step1; decide +kernel
      have hl : raw13011step1Labels = labelEmbedding6 ∘ raw13011step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13011step1 raw13011step1Labels raw13011step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw13012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13012step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13012step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13012 raw13012Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw13012 raw13012Labels = mixedMoment B raw13012step0 raw13012step0Labels := by
      have hz : ∀ j, raw13012 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13012step0 = (fun i j => raw13012 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13012step0 raw13012; decide +kernel
      have hl : raw13012step0Labels = raw13012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13012 raw13012Labels permutation265 hz
    mixedMoment B raw13012step0 raw13012step0Labels = mixedMoment B raw13012step1 raw13012step1Labels := by
      have ha : raw13012step1 = (fun i j => raw13012step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13012step1 raw13012step0; decide +kernel
      have hl : raw13012step1Labels = raw13012step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13012step0 raw13012step0Labels permutation53 permutation3
    mixedMoment B raw13012step1 raw13012step1Labels = mixedMoment B raw13012step2 raw13012step2Labels := by
      have ha : raw13012step2 = raw13012step1 := by apply Matrix.ext; unfold raw13012step2 raw13012step1; decide +kernel
      have hl : raw13012step1Labels = labelEmbedding6 ∘ raw13012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13012step1 raw13012step1Labels raw13012step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw13013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13013step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13013step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13013 raw13013Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw13013 raw13013Labels = mixedMoment B raw13013step0 raw13013step0Labels := by
      have hz : ∀ j, raw13013 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13013step0 = (fun i j => raw13013 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13013step0 raw13013; decide +kernel
      have hl : raw13013step0Labels = raw13013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13013 raw13013Labels permutation265 hz
    mixedMoment B raw13013step0 raw13013step0Labels = mixedMoment B raw13013step1 raw13013step1Labels := by
      have ha : raw13013step1 = (fun i j => raw13013step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13013step1 raw13013step0; decide +kernel
      have hl : raw13013step1Labels = raw13013step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13013step0 raw13013step0Labels permutation35 permutation3
    mixedMoment B raw13013step1 raw13013step1Labels = mixedMoment B raw13013step2 raw13013step2Labels := by
      have ha : raw13013step2 = raw13013step1 := by apply Matrix.ext; unfold raw13013step2 raw13013step1; decide +kernel
      have hl : raw13013step1Labels = labelEmbedding6 ∘ raw13013step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13013step1 raw13013step1Labels raw13013step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw13014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13014step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13014step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13014 raw13014Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw13014 raw13014Labels = mixedMoment B raw13014step0 raw13014step0Labels := by
      have ha : raw13014step0 = (fun i j => raw13014 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13014step0 raw13014; decide +kernel
      have hl : raw13014step0Labels = raw13014Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13014 raw13014Labels permutation155 permutation3
    mixedMoment B raw13014step0 raw13014step0Labels = mixedMoment B raw13014step1 raw13014step1Labels := by
      have ha : raw13014step1 = raw13014step0 := by apply Matrix.ext; unfold raw13014step1 raw13014step0; decide +kernel
      have hl : raw13014step0Labels = labelEmbedding6 ∘ raw13014step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13014step0 raw13014step0Labels raw13014step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw13015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13015step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13015step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13015 raw13015Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw13015 raw13015Labels = mixedMoment B raw13015step0 raw13015step0Labels := by
      have hz : ∀ j, raw13015 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13015step0 = (fun i j => raw13015 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13015step0 raw13015; decide +kernel
      have hl : raw13015step0Labels = raw13015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13015 raw13015Labels permutation265 hz
    mixedMoment B raw13015step0 raw13015step0Labels = mixedMoment B raw13015step1 raw13015step1Labels := by
      have ha : raw13015step1 = (fun i j => raw13015step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13015step1 raw13015step0; decide +kernel
      have hl : raw13015step1Labels = raw13015step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13015step0 raw13015step0Labels permutation35 permutation3
    mixedMoment B raw13015step1 raw13015step1Labels = mixedMoment B raw13015step2 raw13015step2Labels := by
      have ha : raw13015step2 = raw13015step1 := by apply Matrix.ext; unfold raw13015step2 raw13015step1; decide +kernel
      have hl : raw13015step1Labels = labelEmbedding6 ∘ raw13015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13015step1 raw13015step1Labels raw13015step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw13016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13016step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13016 raw13016Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw13016 raw13016Labels = mixedMoment B raw13016step0 raw13016step0Labels := by
      have hz : ∀ j, raw13016 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13016step0 = (fun i j => raw13016 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13016step0 raw13016; decide +kernel
      have hl : raw13016step0Labels = raw13016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13016 raw13016Labels permutation265 hz
    mixedMoment B raw13016step0 raw13016step0Labels = mixedMoment B raw13016step1 raw13016step1Labels := by
      have ha : raw13016step1 = (fun i j => raw13016step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13016step1 raw13016step0; decide +kernel
      have hl : raw13016step1Labels = raw13016step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13016step0 raw13016step0Labels permutation45 permutation3
    mixedMoment B raw13016step1 raw13016step1Labels = mixedMoment B raw13016step2 raw13016step2Labels := by
      have ha : raw13016step2 = raw13016step1 := by apply Matrix.ext; unfold raw13016step2 raw13016step1; decide +kernel
      have hl : raw13016step1Labels = labelEmbedding6 ∘ raw13016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13016step1 raw13016step1Labels raw13016step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw13017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13017step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13017step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13017 raw13017Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw13017 raw13017Labels = mixedMoment B raw13017step0 raw13017step0Labels := by
      have hz : ∀ j, raw13017 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13017step0 = (fun i j => raw13017 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13017step0 raw13017; decide +kernel
      have hl : raw13017step0Labels = raw13017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13017 raw13017Labels permutation265 hz
    mixedMoment B raw13017step0 raw13017step0Labels = mixedMoment B raw13017step1 raw13017step1Labels := by
      have ha : raw13017step1 = (fun i j => raw13017step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13017step1 raw13017step0; decide +kernel
      have hl : raw13017step1Labels = raw13017step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13017step0 raw13017step0Labels permutation51 permutation3
    mixedMoment B raw13017step1 raw13017step1Labels = mixedMoment B raw13017step2 raw13017step2Labels := by
      have ha : raw13017step2 = raw13017step1 := by apply Matrix.ext; unfold raw13017step2 raw13017step1; decide +kernel
      have hl : raw13017step1Labels = labelEmbedding6 ∘ raw13017step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13017step1 raw13017step1Labels raw13017step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw13018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13018step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13018step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13018 raw13018Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw13018 raw13018Labels = mixedMoment B raw13018step0 raw13018step0Labels := by
      have hz : ∀ j, raw13018 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13018step0 = (fun i j => raw13018 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13018step0 raw13018; decide +kernel
      have hl : raw13018step0Labels = raw13018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13018 raw13018Labels permutation265 hz
    mixedMoment B raw13018step0 raw13018step0Labels = mixedMoment B raw13018step1 raw13018step1Labels := by
      have ha : raw13018step1 = (fun i j => raw13018step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13018step1 raw13018step0; decide +kernel
      have hl : raw13018step1Labels = raw13018step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13018step0 raw13018step0Labels permutation33 permutation3
    mixedMoment B raw13018step1 raw13018step1Labels = mixedMoment B raw13018step2 raw13018step2Labels := by
      have ha : raw13018step2 = raw13018step1 := by apply Matrix.ext; unfold raw13018step2 raw13018step1; decide +kernel
      have hl : raw13018step1Labels = labelEmbedding6 ∘ raw13018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13018step1 raw13018step1Labels raw13018step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw13019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13019step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13019 raw13019Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw13019 raw13019Labels = mixedMoment B raw13019step0 raw13019step0Labels := by
      have ha : raw13019step0 = (fun i j => raw13019 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13019step0 raw13019; decide +kernel
      have hl : raw13019step0Labels = raw13019Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13019 raw13019Labels permutation153 permutation3
    mixedMoment B raw13019step0 raw13019step0Labels = mixedMoment B raw13019step1 raw13019step1Labels := by
      have ha : raw13019step1 = raw13019step0 := by apply Matrix.ext; unfold raw13019step1 raw13019step0; decide +kernel
      have hl : raw13019step0Labels = labelEmbedding6 ∘ raw13019step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13019step0 raw13019step0Labels raw13019step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw13020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13020step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13020step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13020 raw13020Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw13020 raw13020Labels = mixedMoment B raw13020step0 raw13020step0Labels := by
      have hz : ∀ j, raw13020 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13020step0 = (fun i j => raw13020 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13020step0 raw13020; decide +kernel
      have hl : raw13020step0Labels = raw13020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13020 raw13020Labels permutation265 hz
    mixedMoment B raw13020step0 raw13020step0Labels = mixedMoment B raw13020step1 raw13020step1Labels := by
      have ha : raw13020step1 = (fun i j => raw13020step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13020step1 raw13020step0; decide +kernel
      have hl : raw13020step1Labels = raw13020step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13020step0 raw13020step0Labels permutation33 permutation3
    mixedMoment B raw13020step1 raw13020step1Labels = mixedMoment B raw13020step2 raw13020step2Labels := by
      have ha : raw13020step2 = raw13020step1 := by apply Matrix.ext; unfold raw13020step2 raw13020step1; decide +kernel
      have hl : raw13020step1Labels = labelEmbedding6 ∘ raw13020step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13020step1 raw13020step1Labels raw13020step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw13021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13021step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13021step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13021 raw13021Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw13021 raw13021Labels = mixedMoment B raw13021step0 raw13021step0Labels := by
      have hz : ∀ j, raw13021 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13021step0 = (fun i j => raw13021 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13021step0 raw13021; decide +kernel
      have hl : raw13021step0Labels = raw13021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13021 raw13021Labels permutation265 hz
    mixedMoment B raw13021step0 raw13021step0Labels = mixedMoment B raw13021step1 raw13021step1Labels := by
      have ha : raw13021step1 = (fun i j => raw13021step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13021step1 raw13021step0; decide +kernel
      have hl : raw13021step1Labels = raw13021step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13021step0 raw13021step0Labels permutation39 permutation3
    mixedMoment B raw13021step1 raw13021step1Labels = mixedMoment B raw13021step2 raw13021step2Labels := by
      have ha : raw13021step2 = raw13021step1 := by apply Matrix.ext; unfold raw13021step2 raw13021step1; decide +kernel
      have hl : raw13021step1Labels = labelEmbedding6 ∘ raw13021step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13021step1 raw13021step1Labels raw13021step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw13022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw13022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw13022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13022step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13022 raw13022Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw13022 raw13022Labels = mixedMoment B raw13022step0 raw13022step0Labels := by
      have hz : ∀ j, raw13022 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13022step0 = (fun i j => raw13022 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13022step0 raw13022; decide +kernel
      have hl : raw13022step0Labels = raw13022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13022 raw13022Labels permutation265 hz
    mixedMoment B raw13022step0 raw13022step0Labels = mixedMoment B raw13022step1 raw13022step1Labels := by
      have ha : raw13022step1 = (fun i j => raw13022step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13022step1 raw13022step0; decide +kernel
      have hl : raw13022step1Labels = raw13022step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13022step0 raw13022step0Labels permutation50 permutation3
    mixedMoment B raw13022step1 raw13022step1Labels = mixedMoment B raw13022step2 raw13022step2Labels := by
      have ha : raw13022step2 = raw13022step1 := by apply Matrix.ext; unfold raw13022step2 raw13022step1; decide +kernel
      have hl : raw13022step1Labels = labelEmbedding6 ∘ raw13022step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13022step1 raw13022step1Labels raw13022step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw13023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13023step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13023step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13023 raw13023Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw13023 raw13023Labels = mixedMoment B raw13023step0 raw13023step0Labels := by
      have hz : ∀ j, raw13023 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13023step0 = (fun i j => raw13023 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13023step0 raw13023; decide +kernel
      have hl : raw13023step0Labels = raw13023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13023 raw13023Labels permutation265 hz
    mixedMoment B raw13023step0 raw13023step0Labels = mixedMoment B raw13023step1 raw13023step1Labels := by
      have ha : raw13023step1 = (fun i j => raw13023step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13023step1 raw13023step0; decide +kernel
      have hl : raw13023step1Labels = raw13023step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13023step0 raw13023step0Labels permutation32 permutation3
    mixedMoment B raw13023step1 raw13023step1Labels = mixedMoment B raw13023step2 raw13023step2Labels := by
      have ha : raw13023step2 = raw13023step1 := by apply Matrix.ext; unfold raw13023step2 raw13023step1; decide +kernel
      have hl : raw13023step1Labels = labelEmbedding6 ∘ raw13023step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13023step1 raw13023step1Labels raw13023step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw13024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13024step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13024step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13024 raw13024Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw13024 raw13024Labels = mixedMoment B raw13024step0 raw13024step0Labels := by
      have ha : raw13024step0 = (fun i j => raw13024 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13024step0 raw13024; decide +kernel
      have hl : raw13024step0Labels = raw13024Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13024 raw13024Labels permutation152 permutation3
    mixedMoment B raw13024step0 raw13024step0Labels = mixedMoment B raw13024step1 raw13024step1Labels := by
      have ha : raw13024step1 = raw13024step0 := by apply Matrix.ext; unfold raw13024step1 raw13024step0; decide +kernel
      have hl : raw13024step0Labels = labelEmbedding6 ∘ raw13024step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13024step0 raw13024step0Labels raw13024step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw13025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13025step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13025step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13025step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13025 raw13025Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw13025 raw13025Labels = mixedMoment B raw13025step0 raw13025step0Labels := by
      have hz : ∀ j, raw13025 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13025step0 = (fun i j => raw13025 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13025step0 raw13025; decide +kernel
      have hl : raw13025step0Labels = raw13025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13025 raw13025Labels permutation265 hz
    mixedMoment B raw13025step0 raw13025step0Labels = mixedMoment B raw13025step1 raw13025step1Labels := by
      have ha : raw13025step1 = (fun i j => raw13025step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13025step1 raw13025step0; decide +kernel
      have hl : raw13025step1Labels = raw13025step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13025step0 raw13025step0Labels permutation32 permutation3
    mixedMoment B raw13025step1 raw13025step1Labels = mixedMoment B raw13025step2 raw13025step2Labels := by
      have ha : raw13025step2 = raw13025step1 := by apply Matrix.ext; unfold raw13025step2 raw13025step1; decide +kernel
      have hl : raw13025step1Labels = labelEmbedding6 ∘ raw13025step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13025step1 raw13025step1Labels raw13025step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw13026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13026step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13026step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13026 raw13026Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw13026 raw13026Labels = mixedMoment B raw13026step0 raw13026step0Labels := by
      have hz : ∀ j, raw13026 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13026step0 = (fun i j => raw13026 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13026step0 raw13026; decide +kernel
      have hl : raw13026step0Labels = raw13026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13026 raw13026Labels permutation265 hz
    mixedMoment B raw13026step0 raw13026step0Labels = mixedMoment B raw13026step1 raw13026step1Labels := by
      have ha : raw13026step1 = (fun i j => raw13026step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13026step1 raw13026step0; decide +kernel
      have hl : raw13026step1Labels = raw13026step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13026step0 raw13026step0Labels permutation38 permutation3
    mixedMoment B raw13026step1 raw13026step1Labels = mixedMoment B raw13026step2 raw13026step2Labels := by
      have ha : raw13026step2 = raw13026step1 := by apply Matrix.ext; unfold raw13026step2 raw13026step1; decide +kernel
      have hl : raw13026step1Labels = labelEmbedding6 ∘ raw13026step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13026step1 raw13026step1Labels raw13026step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw13027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw13027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw13027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13027step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw13027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13027 raw13027Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw13027 raw13027Labels = mixedMoment B raw13027step0 raw13027step0Labels := by
      have hz : ∀ j, raw13027 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13027step0 = (fun i j => raw13027 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13027step0 raw13027; decide +kernel
      have hl : raw13027step0Labels = raw13027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13027 raw13027Labels permutation265 hz
    mixedMoment B raw13027step0 raw13027step0Labels = mixedMoment B raw13027step1 raw13027step1Labels := by
      have ha : raw13027step1 = (fun i j => raw13027step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13027step1 raw13027step0; decide +kernel
      have hl : raw13027step1Labels = raw13027step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13027step0 raw13027step0Labels permutation44 permutation3
    mixedMoment B raw13027step1 raw13027step1Labels = mixedMoment B raw13027step2 raw13027step2Labels := by
      have ha : raw13027step2 = raw13027step1 := by apply Matrix.ext; unfold raw13027step2 raw13027step1; decide +kernel
      have hl : raw13027step1Labels = labelEmbedding6 ∘ raw13027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13027step1 raw13027step1Labels raw13027step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw13028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13028Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13028step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13028step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13028 raw13028Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw13028 raw13028Labels = mixedMoment B raw13028step0 raw13028step0Labels := by
      have ha : raw13028step0 = (fun i j => raw13028 (permutation346 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13028step0 raw13028; decide +kernel
      have hl : raw13028step0Labels = raw13028Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13028 raw13028Labels permutation346 permutation7
    mixedMoment B raw13028step0 raw13028step0Labels = mixedMoment B raw13028step1 raw13028step1Labels := by
      have ha : raw13028step1 = -raw13028step0 := by apply Matrix.ext; change ∀ i j, raw13028step1 i j = -(raw13028step0 i j); unfold raw13028step1 raw13028step0; decide +kernel
      have hl : raw13028step1Labels = raw13028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13028step1 raw13028step1Labels = mixedMoment B raw13028step2 raw13028step2Labels := by
      have ha : raw13028step2 = raw13028step1 := by apply Matrix.ext; unfold raw13028step2 raw13028step1; decide +kernel
      have hl : raw13028step1Labels = labelEmbedding1 ∘ raw13028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13028step1 raw13028step1Labels raw13028step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw13029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13029step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13029step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13029step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13029step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13029 raw13029Labels = mixedMoment B node3962 node3962Labels := by
  calc
    mixedMoment B raw13029 raw13029Labels = mixedMoment B raw13029step0 raw13029step0Labels := by
      have hz : ∀ j, raw13029 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13029step0 = (fun i j => raw13029 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13029step0 raw13029; decide +kernel
      have hl : raw13029step0Labels = raw13029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13029 raw13029Labels permutation265 hz
    mixedMoment B raw13029step0 raw13029step0Labels = mixedMoment B raw13029step1 raw13029step1Labels := by
      have ha : raw13029step1 = (fun i j => raw13029step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13029step1 raw13029step0; decide +kernel
      have hl : raw13029step1Labels = raw13029step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13029step0 raw13029step0Labels permutation56 permutation7
    mixedMoment B raw13029step1 raw13029step1Labels = mixedMoment B raw13029step2 raw13029step2Labels := by
      have ha : raw13029step2 = -raw13029step1 := by apply Matrix.ext; change ∀ i j, raw13029step2 i j = -(raw13029step1 i j); unfold raw13029step2 raw13029step1; decide +kernel
      have hl : raw13029step2Labels = raw13029step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13029step2 raw13029step2Labels = mixedMoment B raw13029step3 raw13029step3Labels := by
      have ha : raw13029step3 = raw13029step2 := by apply Matrix.ext; unfold raw13029step3 raw13029step2; decide +kernel
      have hl : raw13029step2Labels = labelEmbedding1 ∘ raw13029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13029step2 raw13029step2Labels raw13029step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3962 node3962Labels := by rfl

def raw13030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13030step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13030step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13030step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13030step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13030 raw13030Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw13030 raw13030Labels = mixedMoment B raw13030step0 raw13030step0Labels := by
      have hz : ∀ j, raw13030 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13030step0 = (fun i j => raw13030 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13030step0 raw13030; decide +kernel
      have hl : raw13030step0Labels = raw13030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13030 raw13030Labels permutation265 hz
    mixedMoment B raw13030step0 raw13030step0Labels = mixedMoment B raw13030step1 raw13030step1Labels := by
      have ha : raw13030step1 = (fun i j => raw13030step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13030step1 raw13030step0; decide +kernel
      have hl : raw13030step1Labels = raw13030step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13030step0 raw13030step0Labels permutation56 permutation7
    mixedMoment B raw13030step1 raw13030step1Labels = mixedMoment B raw13030step2 raw13030step2Labels := by
      have ha : raw13030step2 = -raw13030step1 := by apply Matrix.ext; change ∀ i j, raw13030step2 i j = -(raw13030step1 i j); unfold raw13030step2 raw13030step1; decide +kernel
      have hl : raw13030step2Labels = raw13030step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13030step2 raw13030step2Labels = mixedMoment B raw13030step3 raw13030step3Labels := by
      have ha : raw13030step3 = raw13030step2 := by apply Matrix.ext; unfold raw13030step3 raw13030step2; decide +kernel
      have hl : raw13030step2Labels = labelEmbedding1 ∘ raw13030step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13030step2 raw13030step2Labels raw13030step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw13031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13031Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13031step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13031step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13031step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13031step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13031step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13031 raw13031Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw13031 raw13031Labels = mixedMoment B raw13031step0 raw13031step0Labels := by
      have hz : ∀ j, raw13031 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13031step0 = (fun i j => raw13031 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13031step0 raw13031; decide +kernel
      have hl : raw13031step0Labels = raw13031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13031 raw13031Labels permutation265 hz
    mixedMoment B raw13031step0 raw13031step0Labels = mixedMoment B raw13031step1 raw13031step1Labels := by
      have ha : raw13031step1 = (fun i j => raw13031step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13031step1 raw13031step0; decide +kernel
      have hl : raw13031step1Labels = raw13031step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13031step0 raw13031step0Labels permutation58 permutation7
    mixedMoment B raw13031step1 raw13031step1Labels = mixedMoment B raw13031step2 raw13031step2Labels := by
      have ha : raw13031step2 = -raw13031step1 := by apply Matrix.ext; change ∀ i j, raw13031step2 i j = -(raw13031step1 i j); unfold raw13031step2 raw13031step1; decide +kernel
      have hl : raw13031step2Labels = raw13031step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13031step2 raw13031step2Labels = mixedMoment B raw13031step3 raw13031step3Labels := by
      have ha : raw13031step3 = raw13031step2 := by apply Matrix.ext; unfold raw13031step3 raw13031step2; decide +kernel
      have hl : raw13031step2Labels = labelEmbedding1 ∘ raw13031step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13031step2 raw13031step2Labels raw13031step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw13032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13032Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13032step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13032step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13032step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13032 raw13032Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw13032 raw13032Labels = mixedMoment B raw13032step0 raw13032step0Labels := by
      have hz : ∀ j, raw13032 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13032step0 = (fun i j => raw13032 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13032step0 raw13032; decide +kernel
      have hl : raw13032step0Labels = raw13032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13032 raw13032Labels permutation265 hz
    mixedMoment B raw13032step0 raw13032step0Labels = mixedMoment B raw13032step1 raw13032step1Labels := by
      have ha : raw13032step1 = (fun i j => raw13032step0 (permutation60 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13032step1 raw13032step0; decide +kernel
      have hl : raw13032step1Labels = raw13032step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13032step0 raw13032step0Labels permutation60 permutation7
    mixedMoment B raw13032step1 raw13032step1Labels = mixedMoment B raw13032step2 raw13032step2Labels := by
      have ha : raw13032step2 = -raw13032step1 := by apply Matrix.ext; change ∀ i j, raw13032step2 i j = -(raw13032step1 i j); unfold raw13032step2 raw13032step1; decide +kernel
      have hl : raw13032step2Labels = raw13032step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13032step2 raw13032step2Labels = mixedMoment B raw13032step3 raw13032step3Labels := by
      have ha : raw13032step3 = raw13032step2 := by apply Matrix.ext; unfold raw13032step3 raw13032step2; decide +kernel
      have hl : raw13032step2Labels = labelEmbedding1 ∘ raw13032step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13032step2 raw13032step2Labels raw13032step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw13033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13033Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13033step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13033step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13033step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13033step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13033 raw13033Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw13033 raw13033Labels = mixedMoment B raw13033step0 raw13033step0Labels := by
      have ha : raw13033step0 = (fun i j => raw13033 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13033step0 raw13033; decide +kernel
      have hl : raw13033step0Labels = raw13033Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13033 raw13033Labels permutation216 permutation5
    mixedMoment B raw13033step0 raw13033step0Labels = mixedMoment B raw13033step1 raw13033step1Labels := by
      have ha : raw13033step1 = -raw13033step0 := by apply Matrix.ext; change ∀ i j, raw13033step1 i j = -(raw13033step0 i j); unfold raw13033step1 raw13033step0; decide +kernel
      have hl : raw13033step1Labels = raw13033step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13033step1 raw13033step1Labels = mixedMoment B raw13033step2 raw13033step2Labels := by
      have ha : raw13033step2 = raw13033step1 := by apply Matrix.ext; unfold raw13033step2 raw13033step1; decide +kernel
      have hl : raw13033step1Labels = labelEmbedding1 ∘ raw13033step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13033step1 raw13033step1Labels raw13033step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1699 node1699Labels := by rfl

def raw13034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13034Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw13034step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13034step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13034step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13034 raw13034Labels = mixedMoment B node3617 node3617Labels := by
  calc
    mixedMoment B raw13034 raw13034Labels = mixedMoment B raw13034step0 raw13034step0Labels := by
      have ha : raw13034step0 = (fun i j => raw13034 (permutation217 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13034step0 raw13034; decide +kernel
      have hl : raw13034step0Labels = raw13034Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13034 raw13034Labels permutation217 permutation5
    mixedMoment B raw13034step0 raw13034step0Labels = mixedMoment B raw13034step1 raw13034step1Labels := by
      have ha : raw13034step1 = -raw13034step0 := by apply Matrix.ext; change ∀ i j, raw13034step1 i j = -(raw13034step0 i j); unfold raw13034step1 raw13034step0; decide +kernel
      have hl : raw13034step1Labels = raw13034step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13034step1 raw13034step1Labels = mixedMoment B raw13034step2 raw13034step2Labels := by
      have ha : raw13034step2 = raw13034step1 := by apply Matrix.ext; unfold raw13034step2 raw13034step1; decide +kernel
      have hl : raw13034step1Labels = labelEmbedding1 ∘ raw13034step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13034step1 raw13034step1Labels raw13034step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3617 node3617Labels := by rfl

def raw13035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13035Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13035step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13035step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13035step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13035 raw13035Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw13035 raw13035Labels = mixedMoment B raw13035step0 raw13035step0Labels := by
      have ha : raw13035step0 = (fun i j => raw13035 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13035step0 raw13035; decide +kernel
      have hl : raw13035step0Labels = raw13035Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13035 raw13035Labels permutation216 permutation5
    mixedMoment B raw13035step0 raw13035step0Labels = mixedMoment B raw13035step1 raw13035step1Labels := by
      have ha : raw13035step1 = -raw13035step0 := by apply Matrix.ext; change ∀ i j, raw13035step1 i j = -(raw13035step0 i j); unfold raw13035step1 raw13035step0; decide +kernel
      have hl : raw13035step1Labels = raw13035step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13035step1 raw13035step1Labels = mixedMoment B raw13035step2 raw13035step2Labels := by
      have ha : raw13035step2 = raw13035step1 := by apply Matrix.ext; unfold raw13035step2 raw13035step1; decide +kernel
      have hl : raw13035step1Labels = labelEmbedding1 ∘ raw13035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13035step1 raw13035step1Labels raw13035step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw13036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13036Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13036step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13036step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13036 raw13036Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw13036 raw13036Labels = mixedMoment B raw13036step0 raw13036step0Labels := by
      have ha : raw13036step0 = (fun i j => raw13036 (permutation238 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13036step0 raw13036; decide +kernel
      have hl : raw13036step0Labels = raw13036Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13036 raw13036Labels permutation238 permutation5
    mixedMoment B raw13036step0 raw13036step0Labels = mixedMoment B raw13036step1 raw13036step1Labels := by
      have ha : raw13036step1 = -raw13036step0 := by apply Matrix.ext; change ∀ i j, raw13036step1 i j = -(raw13036step0 i j); unfold raw13036step1 raw13036step0; decide +kernel
      have hl : raw13036step1Labels = raw13036step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13036step1 raw13036step1Labels = mixedMoment B raw13036step2 raw13036step2Labels := by
      have ha : raw13036step2 = raw13036step1 := by apply Matrix.ext; unfold raw13036step2 raw13036step1; decide +kernel
      have hl : raw13036step1Labels = labelEmbedding1 ∘ raw13036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13036step1 raw13036step1Labels raw13036step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw13037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13037Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13037step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13037step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13037step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13037step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13037 raw13037Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw13037 raw13037Labels = mixedMoment B raw13037step0 raw13037step0Labels := by
      have ha : raw13037step0 = (fun i j => raw13037 (permutation258 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13037step0 raw13037; decide +kernel
      have hl : raw13037step0Labels = raw13037Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13037 raw13037Labels permutation258 permutation5
    mixedMoment B raw13037step0 raw13037step0Labels = mixedMoment B raw13037step1 raw13037step1Labels := by
      have ha : raw13037step1 = -raw13037step0 := by apply Matrix.ext; change ∀ i j, raw13037step1 i j = -(raw13037step0 i j); unfold raw13037step1 raw13037step0; decide +kernel
      have hl : raw13037step1Labels = raw13037step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13037step1 raw13037step1Labels = mixedMoment B raw13037step2 raw13037step2Labels := by
      have ha : raw13037step2 = raw13037step1 := by apply Matrix.ext; unfold raw13037step2 raw13037step1; decide +kernel
      have hl : raw13037step1Labels = labelEmbedding1 ∘ raw13037step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13037step1 raw13037step1Labels raw13037step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw13038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13038Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13038step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13038step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw13038step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13038step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw13038step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13038 raw13038Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw13038 raw13038Labels = mixedMoment B raw13038step0 raw13038step0Labels := by
      have hz : ∀ j, raw13038 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13038step0 = (fun i j => raw13038 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13038step0 raw13038; decide +kernel
      have hl : raw13038step0Labels = raw13038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13038 raw13038Labels permutation265 hz
    mixedMoment B raw13038step0 raw13038step0Labels = mixedMoment B raw13038step1 raw13038step1Labels := by
      have ha : raw13038step1 = (fun i j => raw13038step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13038step1 raw13038step0; decide +kernel
      have hl : raw13038step1Labels = raw13038step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13038step0 raw13038step0Labels permutation41 permutation5
    mixedMoment B raw13038step1 raw13038step1Labels = mixedMoment B raw13038step2 raw13038step2Labels := by
      have ha : raw13038step2 = -raw13038step1 := by apply Matrix.ext; change ∀ i j, raw13038step2 i j = -(raw13038step1 i j); unfold raw13038step2 raw13038step1; decide +kernel
      have hl : raw13038step2Labels = raw13038step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13038step2 raw13038step2Labels = mixedMoment B raw13038step3 raw13038step3Labels := by
      have ha : raw13038step3 = raw13038step2 := by apply Matrix.ext; unfold raw13038step3 raw13038step2; decide +kernel
      have hl : raw13038step2Labels = labelEmbedding1 ∘ raw13038step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13038step2 raw13038step2Labels raw13038step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1700 node1700Labels := by rfl

def raw13039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13039Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13039step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13039 raw13039Labels = mixedMoment B node3058 node3058Labels := by
  calc
    mixedMoment B raw13039 raw13039Labels = mixedMoment B raw13039step0 raw13039step0Labels := by
      have ha : raw13039step0 = (fun i j => raw13039 (permutation394 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13039step0 raw13039; decide +kernel
      have hl : raw13039step0Labels = raw13039Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13039 raw13039Labels permutation394 permutation5
    mixedMoment B raw13039step0 raw13039step0Labels = mixedMoment B raw13039step1 raw13039step1Labels := by
      have ha : raw13039step1 = raw13039step0 := by apply Matrix.ext; unfold raw13039step1 raw13039step0; decide +kernel
      have hl : raw13039step0Labels = labelEmbedding1 ∘ raw13039step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13039step0 raw13039step0Labels raw13039step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3058 node3058Labels := by rfl

def raw13040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13040Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13040step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13040step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13040 raw13040Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw13040 raw13040Labels = mixedMoment B raw13040step0 raw13040step0Labels := by
      have hz : ∀ j, raw13040 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13040step0 = (fun i j => raw13040 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13040step0 raw13040; decide +kernel
      have hl : raw13040step0Labels = raw13040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13040 raw13040Labels permutation265 hz
    mixedMoment B raw13040step0 raw13040step0Labels = mixedMoment B raw13040step1 raw13040step1Labels := by
      have ha : raw13040step1 = (fun i j => raw13040step0 (permutation73 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13040step1 raw13040step0; decide +kernel
      have hl : raw13040step1Labels = raw13040step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13040step0 raw13040step0Labels permutation73 permutation5
    mixedMoment B raw13040step1 raw13040step1Labels = mixedMoment B raw13040step2 raw13040step2Labels := by
      have ha : raw13040step2 = raw13040step1 := by apply Matrix.ext; unfold raw13040step2 raw13040step1; decide +kernel
      have hl : raw13040step1Labels = labelEmbedding1 ∘ raw13040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13040step1 raw13040step1Labels raw13040step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw13041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13041Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13041step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13041step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13041step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13041 raw13041Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw13041 raw13041Labels = mixedMoment B raw13041step0 raw13041step0Labels := by
      have hz : ∀ j, raw13041 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13041step0 = (fun i j => raw13041 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13041step0 raw13041; decide +kernel
      have hl : raw13041step0Labels = raw13041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13041 raw13041Labels permutation265 hz
    mixedMoment B raw13041step0 raw13041step0Labels = mixedMoment B raw13041step1 raw13041step1Labels := by
      have ha : raw13041step1 = (fun i j => raw13041step0 (permutation67 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13041step1 raw13041step0; decide +kernel
      have hl : raw13041step1Labels = raw13041step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13041step0 raw13041step0Labels permutation67 permutation5
    mixedMoment B raw13041step1 raw13041step1Labels = mixedMoment B raw13041step2 raw13041step2Labels := by
      have ha : raw13041step2 = raw13041step1 := by apply Matrix.ext; unfold raw13041step2 raw13041step1; decide +kernel
      have hl : raw13041step1Labels = labelEmbedding1 ∘ raw13041step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13041step1 raw13041step1Labels raw13041step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw13042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13042Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13042step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13042step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13042 raw13042Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw13042 raw13042Labels = mixedMoment B raw13042step0 raw13042step0Labels := by
      have hz : ∀ j, raw13042 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13042step0 = (fun i j => raw13042 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13042step0 raw13042; decide +kernel
      have hl : raw13042step0Labels = raw13042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13042 raw13042Labels permutation265 hz
    mixedMoment B raw13042step0 raw13042step0Labels = mixedMoment B raw13042step1 raw13042step1Labels := by
      have ha : raw13042step1 = (fun i j => raw13042step0 (permutation65 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13042step1 raw13042step0; decide +kernel
      have hl : raw13042step1Labels = raw13042step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13042step0 raw13042step0Labels permutation65 permutation5
    mixedMoment B raw13042step1 raw13042step1Labels = mixedMoment B raw13042step2 raw13042step2Labels := by
      have ha : raw13042step2 = raw13042step1 := by apply Matrix.ext; unfold raw13042step2 raw13042step1; decide +kernel
      have hl : raw13042step1Labels = labelEmbedding1 ∘ raw13042step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13042step1 raw13042step1Labels raw13042step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw13043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13043Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13043step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13043step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13043step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13043step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13043step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13043 raw13043Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw13043 raw13043Labels = mixedMoment B raw13043step0 raw13043step0Labels := by
      have hz : ∀ j, raw13043 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13043step0 = (fun i j => raw13043 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13043step0 raw13043; decide +kernel
      have hl : raw13043step0Labels = raw13043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13043 raw13043Labels permutation265 hz
    mixedMoment B raw13043step0 raw13043step0Labels = mixedMoment B raw13043step1 raw13043step1Labels := by
      have ha : raw13043step1 = (fun i j => raw13043step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13043step1 raw13043step0; decide +kernel
      have hl : raw13043step1Labels = raw13043step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13043step0 raw13043step0Labels permutation49 permutation5
    mixedMoment B raw13043step1 raw13043step1Labels = mixedMoment B raw13043step2 raw13043step2Labels := by
      have ha : raw13043step2 = -raw13043step1 := by apply Matrix.ext; change ∀ i j, raw13043step2 i j = -(raw13043step1 i j); unfold raw13043step2 raw13043step1; decide +kernel
      have hl : raw13043step2Labels = raw13043step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13043step2 raw13043step2Labels = mixedMoment B raw13043step3 raw13043step3Labels := by
      have ha : raw13043step3 = raw13043step2 := by apply Matrix.ext; unfold raw13043step3 raw13043step2; decide +kernel
      have hl : raw13043step2Labels = labelEmbedding1 ∘ raw13043step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13043step2 raw13043step2Labels raw13043step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw13044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13044Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13044step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13044step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13044step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13044 raw13044Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw13044 raw13044Labels = mixedMoment B raw13044step0 raw13044step0Labels := by
      have ha : raw13044step0 = (fun i j => raw13044 (permutation169 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13044step0 raw13044; decide +kernel
      have hl : raw13044step0Labels = raw13044Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13044 raw13044Labels permutation169 permutation5
    mixedMoment B raw13044step0 raw13044step0Labels = mixedMoment B raw13044step1 raw13044step1Labels := by
      have ha : raw13044step1 = -raw13044step0 := by apply Matrix.ext; change ∀ i j, raw13044step1 i j = -(raw13044step0 i j); unfold raw13044step1 raw13044step0; decide +kernel
      have hl : raw13044step1Labels = raw13044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13044step1 raw13044step1Labels = mixedMoment B raw13044step2 raw13044step2Labels := by
      have ha : raw13044step2 = raw13044step1 := by apply Matrix.ext; unfold raw13044step2 raw13044step1; decide +kernel
      have hl : raw13044step1Labels = labelEmbedding1 ∘ raw13044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13044step1 raw13044step1Labels raw13044step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw13045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13045Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13045step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw13045step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13045step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13045step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13045 raw13045Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw13045 raw13045Labels = mixedMoment B raw13045step0 raw13045step0Labels := by
      have hz : ∀ j, raw13045 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13045step0 = (fun i j => raw13045 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13045step0 raw13045; decide +kernel
      have hl : raw13045step0Labels = raw13045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13045 raw13045Labels permutation265 hz
    mixedMoment B raw13045step0 raw13045step0Labels = mixedMoment B raw13045step1 raw13045step1Labels := by
      have ha : raw13045step1 = (fun i j => raw13045step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13045step1 raw13045step0; decide +kernel
      have hl : raw13045step1Labels = raw13045step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13045step0 raw13045step0Labels permutation48 permutation5
    mixedMoment B raw13045step1 raw13045step1Labels = mixedMoment B raw13045step2 raw13045step2Labels := by
      have ha : raw13045step2 = -raw13045step1 := by apply Matrix.ext; change ∀ i j, raw13045step2 i j = -(raw13045step1 i j); unfold raw13045step2 raw13045step1; decide +kernel
      have hl : raw13045step2Labels = raw13045step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13045step2 raw13045step2Labels = mixedMoment B raw13045step3 raw13045step3Labels := by
      have ha : raw13045step3 = raw13045step2 := by apply Matrix.ext; unfold raw13045step3 raw13045step2; decide +kernel
      have hl : raw13045step2Labels = labelEmbedding1 ∘ raw13045step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13045step2 raw13045step2Labels raw13045step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

def raw13046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13046Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13046step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13046step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13046step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13046step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13046 raw13046Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw13046 raw13046Labels = mixedMoment B raw13046step0 raw13046step0Labels := by
      have hz : ∀ j, raw13046 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13046step0 = (fun i j => raw13046 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13046step0 raw13046; decide +kernel
      have hl : raw13046step0Labels = raw13046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13046 raw13046Labels permutation265 hz
    mixedMoment B raw13046step0 raw13046step0Labels = mixedMoment B raw13046step1 raw13046step1Labels := by
      have ha : raw13046step1 = (fun i j => raw13046step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13046step1 raw13046step0; decide +kernel
      have hl : raw13046step1Labels = raw13046step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13046step0 raw13046step0Labels permutation49 permutation5
    mixedMoment B raw13046step1 raw13046step1Labels = mixedMoment B raw13046step2 raw13046step2Labels := by
      have ha : raw13046step2 = -raw13046step1 := by apply Matrix.ext; change ∀ i j, raw13046step2 i j = -(raw13046step1 i j); unfold raw13046step2 raw13046step1; decide +kernel
      have hl : raw13046step2Labels = raw13046step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13046step2 raw13046step2Labels = mixedMoment B raw13046step3 raw13046step3Labels := by
      have ha : raw13046step3 = raw13046step2 := by apply Matrix.ext; unfold raw13046step3 raw13046step2; decide +kernel
      have hl : raw13046step2Labels = labelEmbedding1 ∘ raw13046step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13046step2 raw13046step2Labels raw13046step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw13047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13047Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13047step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13047step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13047step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13047step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13047step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13047 raw13047Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw13047 raw13047Labels = mixedMoment B raw13047step0 raw13047step0Labels := by
      have hz : ∀ j, raw13047 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13047step0 = (fun i j => raw13047 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13047step0 raw13047; decide +kernel
      have hl : raw13047step0Labels = raw13047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13047 raw13047Labels permutation265 hz
    mixedMoment B raw13047step0 raw13047step0Labels = mixedMoment B raw13047step1 raw13047step1Labels := by
      have ha : raw13047step1 = (fun i j => raw13047step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13047step1 raw13047step0; decide +kernel
      have hl : raw13047step1Labels = raw13047step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13047step0 raw13047step0Labels permutation55 permutation5
    mixedMoment B raw13047step1 raw13047step1Labels = mixedMoment B raw13047step2 raw13047step2Labels := by
      have ha : raw13047step2 = -raw13047step1 := by apply Matrix.ext; change ∀ i j, raw13047step2 i j = -(raw13047step1 i j); unfold raw13047step2 raw13047step1; decide +kernel
      have hl : raw13047step2Labels = raw13047step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13047step2 raw13047step2Labels = mixedMoment B raw13047step3 raw13047step3Labels := by
      have ha : raw13047step3 = raw13047step2 := by apply Matrix.ext; unfold raw13047step3 raw13047step2; decide +kernel
      have hl : raw13047step2Labels = labelEmbedding1 ∘ raw13047step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13047step2 raw13047step2Labels raw13047step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw13048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13048Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13048step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13048step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13048step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13048step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13048step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13048 raw13048Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw13048 raw13048Labels = mixedMoment B raw13048step0 raw13048step0Labels := by
      have hz : ∀ j, raw13048 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13048step0 = (fun i j => raw13048 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13048step0 raw13048; decide +kernel
      have hl : raw13048step0Labels = raw13048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13048 raw13048Labels permutation265 hz
    mixedMoment B raw13048step0 raw13048step0Labels = mixedMoment B raw13048step1 raw13048step1Labels := by
      have ha : raw13048step1 = (fun i j => raw13048step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13048step1 raw13048step0; decide +kernel
      have hl : raw13048step1Labels = raw13048step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13048step0 raw13048step0Labels permutation43 permutation5
    mixedMoment B raw13048step1 raw13048step1Labels = mixedMoment B raw13048step2 raw13048step2Labels := by
      have ha : raw13048step2 = -raw13048step1 := by apply Matrix.ext; change ∀ i j, raw13048step2 i j = -(raw13048step1 i j); unfold raw13048step2 raw13048step1; decide +kernel
      have hl : raw13048step2Labels = raw13048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13048step2 raw13048step2Labels = mixedMoment B raw13048step3 raw13048step3Labels := by
      have ha : raw13048step3 = raw13048step2 := by apply Matrix.ext; unfold raw13048step3 raw13048step2; decide +kernel
      have hl : raw13048step2Labels = labelEmbedding1 ∘ raw13048step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13048step2 raw13048step2Labels raw13048step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw13049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13049step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13049step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13049 raw13049Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw13049 raw13049Labels = mixedMoment B raw13049step0 raw13049step0Labels := by
      have ha : raw13049step0 = (fun i j => raw13049 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13049step0 raw13049; decide +kernel
      have hl : raw13049step0Labels = raw13049Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13049 raw13049Labels permutation163 permutation5
    mixedMoment B raw13049step0 raw13049step0Labels = mixedMoment B raw13049step1 raw13049step1Labels := by
      have ha : raw13049step1 = -raw13049step0 := by apply Matrix.ext; change ∀ i j, raw13049step1 i j = -(raw13049step0 i j); unfold raw13049step1 raw13049step0; decide +kernel
      have hl : raw13049step1Labels = raw13049step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13049step1 raw13049step1Labels = mixedMoment B raw13049step2 raw13049step2Labels := by
      have ha : raw13049step2 = raw13049step1 := by apply Matrix.ext; unfold raw13049step2 raw13049step1; decide +kernel
      have hl : raw13049step1Labels = labelEmbedding1 ∘ raw13049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13049step1 raw13049step1Labels raw13049step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw13050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13050step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw13050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13050step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13050step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13050step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13050 raw13050Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw13050 raw13050Labels = mixedMoment B raw13050step0 raw13050step0Labels := by
      have hz : ∀ j, raw13050 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13050step0 = (fun i j => raw13050 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13050step0 raw13050; decide +kernel
      have hl : raw13050step0Labels = raw13050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13050 raw13050Labels permutation265 hz
    mixedMoment B raw13050step0 raw13050step0Labels = mixedMoment B raw13050step1 raw13050step1Labels := by
      have ha : raw13050step1 = (fun i j => raw13050step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13050step1 raw13050step0; decide +kernel
      have hl : raw13050step1Labels = raw13050step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13050step0 raw13050step0Labels permutation42 permutation5
    mixedMoment B raw13050step1 raw13050step1Labels = mixedMoment B raw13050step2 raw13050step2Labels := by
      have ha : raw13050step2 = -raw13050step1 := by apply Matrix.ext; change ∀ i j, raw13050step2 i j = -(raw13050step1 i j); unfold raw13050step2 raw13050step1; decide +kernel
      have hl : raw13050step2Labels = raw13050step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13050step2 raw13050step2Labels = mixedMoment B raw13050step3 raw13050step3Labels := by
      have ha : raw13050step3 = raw13050step2 := by apply Matrix.ext; unfold raw13050step3 raw13050step2; decide +kernel
      have hl : raw13050step2Labels = labelEmbedding1 ∘ raw13050step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13050step2 raw13050step2Labels raw13050step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

def raw13051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13051step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13051step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13051 raw13051Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw13051 raw13051Labels = mixedMoment B raw13051step0 raw13051step0Labels := by
      have hz : ∀ j, raw13051 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13051step0 = (fun i j => raw13051 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13051step0 raw13051; decide +kernel
      have hl : raw13051step0Labels = raw13051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13051 raw13051Labels permutation265 hz
    mixedMoment B raw13051step0 raw13051step0Labels = mixedMoment B raw13051step1 raw13051step1Labels := by
      have ha : raw13051step1 = (fun i j => raw13051step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13051step1 raw13051step0; decide +kernel
      have hl : raw13051step1Labels = raw13051step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13051step0 raw13051step0Labels permutation43 permutation5
    mixedMoment B raw13051step1 raw13051step1Labels = mixedMoment B raw13051step2 raw13051step2Labels := by
      have ha : raw13051step2 = -raw13051step1 := by apply Matrix.ext; change ∀ i j, raw13051step2 i j = -(raw13051step1 i j); unfold raw13051step2 raw13051step1; decide +kernel
      have hl : raw13051step2Labels = raw13051step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13051step2 raw13051step2Labels = mixedMoment B raw13051step3 raw13051step3Labels := by
      have ha : raw13051step3 = raw13051step2 := by apply Matrix.ext; unfold raw13051step3 raw13051step2; decide +kernel
      have hl : raw13051step2Labels = labelEmbedding1 ∘ raw13051step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13051step2 raw13051step2Labels raw13051step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw13052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw13052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw13052step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13052step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13052step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13052step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13052 raw13052Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw13052 raw13052Labels = mixedMoment B raw13052step0 raw13052step0Labels := by
      have hz : ∀ j, raw13052 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13052step0 = (fun i j => raw13052 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13052step0 raw13052; decide +kernel
      have hl : raw13052step0Labels = raw13052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13052 raw13052Labels permutation265 hz
    mixedMoment B raw13052step0 raw13052step0Labels = mixedMoment B raw13052step1 raw13052step1Labels := by
      have ha : raw13052step1 = (fun i j => raw13052step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13052step1 raw13052step0; decide +kernel
      have hl : raw13052step1Labels = raw13052step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13052step0 raw13052step0Labels permutation53 permutation5
    mixedMoment B raw13052step1 raw13052step1Labels = mixedMoment B raw13052step2 raw13052step2Labels := by
      have ha : raw13052step2 = -raw13052step1 := by apply Matrix.ext; change ∀ i j, raw13052step2 i j = -(raw13052step1 i j); unfold raw13052step2 raw13052step1; decide +kernel
      have hl : raw13052step2Labels = raw13052step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13052step2 raw13052step2Labels = mixedMoment B raw13052step3 raw13052step3Labels := by
      have ha : raw13052step3 = raw13052step2 := by apply Matrix.ext; unfold raw13052step3 raw13052step2; decide +kernel
      have hl : raw13052step2Labels = labelEmbedding1 ∘ raw13052step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13052step2 raw13052step2Labels raw13052step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw13053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13053step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13053step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13053step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13053step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13053 raw13053Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw13053 raw13053Labels = mixedMoment B raw13053step0 raw13053step0Labels := by
      have hz : ∀ j, raw13053 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13053step0 = (fun i j => raw13053 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13053step0 raw13053; decide +kernel
      have hl : raw13053step0Labels = raw13053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13053 raw13053Labels permutation265 hz
    mixedMoment B raw13053step0 raw13053step0Labels = mixedMoment B raw13053step1 raw13053step1Labels := by
      have ha : raw13053step1 = (fun i j => raw13053step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13053step1 raw13053step0; decide +kernel
      have hl : raw13053step1Labels = raw13053step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13053step0 raw13053step0Labels permutation41 permutation5
    mixedMoment B raw13053step1 raw13053step1Labels = mixedMoment B raw13053step2 raw13053step2Labels := by
      have ha : raw13053step2 = -raw13053step1 := by apply Matrix.ext; change ∀ i j, raw13053step2 i j = -(raw13053step1 i j); unfold raw13053step2 raw13053step1; decide +kernel
      have hl : raw13053step2Labels = raw13053step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13053step2 raw13053step2Labels = mixedMoment B raw13053step3 raw13053step3Labels := by
      have ha : raw13053step3 = raw13053step2 := by apply Matrix.ext; unfold raw13053step3 raw13053step2; decide +kernel
      have hl : raw13053step2Labels = labelEmbedding1 ∘ raw13053step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13053step2 raw13053step2Labels raw13053step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw13054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13054step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13054step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13054 raw13054Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw13054 raw13054Labels = mixedMoment B raw13054step0 raw13054step0Labels := by
      have ha : raw13054step0 = (fun i j => raw13054 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13054step0 raw13054; decide +kernel
      have hl : raw13054step0Labels = raw13054Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13054 raw13054Labels permutation161 permutation5
    mixedMoment B raw13054step0 raw13054step0Labels = mixedMoment B raw13054step1 raw13054step1Labels := by
      have ha : raw13054step1 = -raw13054step0 := by apply Matrix.ext; change ∀ i j, raw13054step1 i j = -(raw13054step0 i j); unfold raw13054step1 raw13054step0; decide +kernel
      have hl : raw13054step1Labels = raw13054step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13054step1 raw13054step1Labels = mixedMoment B raw13054step2 raw13054step2Labels := by
      have ha : raw13054step2 = raw13054step1 := by apply Matrix.ext; unfold raw13054step2 raw13054step1; decide +kernel
      have hl : raw13054step1Labels = labelEmbedding1 ∘ raw13054step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13054step1 raw13054step1Labels raw13054step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw13055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13055Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13055step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw13055step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13055step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13055step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw13055step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13055 raw13055Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw13055 raw13055Labels = mixedMoment B raw13055step0 raw13055step0Labels := by
      have hz : ∀ j, raw13055 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13055step0 = (fun i j => raw13055 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13055step0 raw13055; decide +kernel
      have hl : raw13055step0Labels = raw13055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13055 raw13055Labels permutation265 hz
    mixedMoment B raw13055step0 raw13055step0Labels = mixedMoment B raw13055step1 raw13055step1Labels := by
      have ha : raw13055step1 = (fun i j => raw13055step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13055step1 raw13055step0; decide +kernel
      have hl : raw13055step1Labels = raw13055step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13055step0 raw13055step0Labels permutation40 permutation5
    mixedMoment B raw13055step1 raw13055step1Labels = mixedMoment B raw13055step2 raw13055step2Labels := by
      have ha : raw13055step2 = -raw13055step1 := by apply Matrix.ext; change ∀ i j, raw13055step2 i j = -(raw13055step1 i j); unfold raw13055step2 raw13055step1; decide +kernel
      have hl : raw13055step2Labels = raw13055step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13055step2 raw13055step2Labels = mixedMoment B raw13055step3 raw13055step3Labels := by
      have ha : raw13055step3 = raw13055step2 := by apply Matrix.ext; unfold raw13055step3 raw13055step2; decide +kernel
      have hl : raw13055step2Labels = labelEmbedding1 ∘ raw13055step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13055step2 raw13055step2Labels raw13055step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
