import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8960 raw8960Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw8960 raw8960Labels = mixedMoment B raw8960step0 raw8960step0Labels := by
      have hz : ∀ j, raw8960 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8960step0 = (fun i j => raw8960 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8960step0 raw8960; decide +kernel
      have hl : raw8960step0Labels = raw8960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8960 raw8960Labels permutation265 hz
    mixedMoment B raw8960step0 raw8960step0Labels = mixedMoment B raw8960step1 raw8960step1Labels := by
      have ha : raw8960step1 = (fun i j => raw8960step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8960step1 raw8960step0; decide +kernel
      have hl : raw8960step1Labels = raw8960step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8960step0 raw8960step0Labels permutation46 permutation3
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw8961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8961 raw8961Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw8961 raw8961Labels = mixedMoment B raw8961step0 raw8961step0Labels := by
      have hz : ∀ j, raw8961 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8961step0 = (fun i j => raw8961 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8961step0 raw8961; decide +kernel
      have hl : raw8961step0Labels = raw8961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8961 raw8961Labels permutation265 hz
    mixedMoment B raw8961step0 raw8961step0Labels = mixedMoment B raw8961step1 raw8961step1Labels := by
      have ha : raw8961step1 = (fun i j => raw8961step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8961step1 raw8961step0; decide +kernel
      have hl : raw8961step1Labels = raw8961step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8961step0 raw8961step0Labels permutation41 permutation3
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw8962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8962 raw8962Labels = mixedMoment B node1036 node1036Labels := by
  calc
    mixedMoment B raw8962 raw8962Labels = mixedMoment B raw8962step0 raw8962step0Labels := by
      have hz : ∀ j, raw8962 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8962step0 = (fun i j => raw8962 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8962step0 raw8962; decide +kernel
      have hl : raw8962step0Labels = raw8962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8962 raw8962Labels permutation265 hz
    mixedMoment B raw8962step0 raw8962step0Labels = mixedMoment B raw8962step1 raw8962step1Labels := by
      have ha : raw8962step1 = (fun i j => raw8962step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8962step1 raw8962step0; decide +kernel
      have hl : raw8962step1Labels = raw8962step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8962step0 raw8962step0Labels permutation34 permutation3
    _ = mixedMoment B node1036 node1036Labels := by rfl

def raw8963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8963 raw8963Labels = mixedMoment B node2478 node2478Labels := by
  calc
    mixedMoment B raw8963 raw8963Labels = mixedMoment B raw8963step0 raw8963step0Labels := by
      have ha : raw8963step0 = (fun i j => raw8963 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8963step0 raw8963; decide +kernel
      have hl : raw8963step0Labels = raw8963Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8963 raw8963Labels permutation154 permutation3
    _ = mixedMoment B node2478 node2478Labels := by rfl

def raw8964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8964 raw8964Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw8964 raw8964Labels = mixedMoment B raw8964step0 raw8964step0Labels := by
      have hz : ∀ j, raw8964 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8964step0 = (fun i j => raw8964 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8964step0 raw8964; decide +kernel
      have hl : raw8964step0Labels = raw8964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8964 raw8964Labels permutation265 hz
    mixedMoment B raw8964step0 raw8964step0Labels = mixedMoment B raw8964step1 raw8964step1Labels := by
      have ha : raw8964step1 = (fun i j => raw8964step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8964step1 raw8964step0; decide +kernel
      have hl : raw8964step1Labels = raw8964step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8964step0 raw8964step0Labels permutation34 permutation3
    _ = mixedMoment B node2591 node2591Labels := by rfl

def raw8965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8965 raw8965Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw8965 raw8965Labels = mixedMoment B raw8965step0 raw8965step0Labels := by
      have hz : ∀ j, raw8965 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8965step0 = (fun i j => raw8965 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8965step0 raw8965; decide +kernel
      have hl : raw8965step0Labels = raw8965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8965 raw8965Labels permutation265 hz
    mixedMoment B raw8965step0 raw8965step0Labels = mixedMoment B raw8965step1 raw8965step1Labels := by
      have ha : raw8965step1 = (fun i j => raw8965step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8965step1 raw8965step0; decide +kernel
      have hl : raw8965step1Labels = raw8965step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8965step0 raw8965step0Labels permutation44 permutation3
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw8966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8966 raw8966Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw8966 raw8966Labels = mixedMoment B raw8966step0 raw8966step0Labels := by
      have hz : ∀ j, raw8966 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8966step0 = (fun i j => raw8966 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8966step0 raw8966; decide +kernel
      have hl : raw8966step0Labels = raw8966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8966 raw8966Labels permutation265 hz
    mixedMoment B raw8966step0 raw8966step0Labels = mixedMoment B raw8966step1 raw8966step1Labels := by
      have ha : raw8966step1 = (fun i j => raw8966step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8966step1 raw8966step0; decide +kernel
      have hl : raw8966step1Labels = raw8966step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8966step0 raw8966step0Labels permutation35 permutation3
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw8967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8967 raw8967Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw8967 raw8967Labels = mixedMoment B raw8967step0 raw8967step0Labels := by
      have hz : ∀ j, raw8967 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8967step0 = (fun i j => raw8967 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8967step0 raw8967; decide +kernel
      have hl : raw8967step0Labels = raw8967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8967 raw8967Labels permutation265 hz
    mixedMoment B raw8967step0 raw8967step0Labels = mixedMoment B raw8967step1 raw8967step1Labels := by
      have ha : raw8967step1 = (fun i j => raw8967step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8967step1 raw8967step0; decide +kernel
      have hl : raw8967step1Labels = raw8967step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8967step0 raw8967step0Labels permutation32 permutation3
    _ = mixedMoment B node1026 node1026Labels := by rfl

def raw8968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8968 raw8968Labels = mixedMoment B node2473 node2473Labels := by
  calc
    mixedMoment B raw8968 raw8968Labels = mixedMoment B raw8968step0 raw8968step0Labels := by
      have ha : raw8968step0 = (fun i j => raw8968 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8968step0 raw8968; decide +kernel
      have hl : raw8968step0Labels = raw8968Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8968 raw8968Labels permutation152 permutation3
    _ = mixedMoment B node2473 node2473Labels := by rfl

def raw8969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8969step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8969 raw8969Labels = mixedMoment B node2576 node2576Labels := by
  calc
    mixedMoment B raw8969 raw8969Labels = mixedMoment B raw8969step0 raw8969step0Labels := by
      have hz : ∀ j, raw8969 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8969step0 = (fun i j => raw8969 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8969step0 raw8969; decide +kernel
      have hl : raw8969step0Labels = raw8969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8969 raw8969Labels permutation265 hz
    mixedMoment B raw8969step0 raw8969step0Labels = mixedMoment B raw8969step1 raw8969step1Labels := by
      have ha : raw8969step1 = (fun i j => raw8969step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8969step1 raw8969step0; decide +kernel
      have hl : raw8969step1Labels = raw8969step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8969step0 raw8969step0Labels permutation32 permutation3
    _ = mixedMoment B node2576 node2576Labels := by rfl

def raw8970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8970 raw8970Labels = mixedMoment B node2576 node2576Labels := by
  calc
    mixedMoment B raw8970 raw8970Labels = mixedMoment B raw8970step0 raw8970step0Labels := by
      have hz : ∀ j, raw8970 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8970step0 = (fun i j => raw8970 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8970step0 raw8970; decide +kernel
      have hl : raw8970step0Labels = raw8970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8970 raw8970Labels permutation265 hz
    mixedMoment B raw8970step0 raw8970step0Labels = mixedMoment B raw8970step1 raw8970step1Labels := by
      have ha : raw8970step1 = (fun i j => raw8970step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8970step1 raw8970step0; decide +kernel
      have hl : raw8970step1Labels = raw8970step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8970step0 raw8970step0Labels permutation38 permutation3
    _ = mixedMoment B node2576 node2576Labels := by rfl

def raw8971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw8971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw8971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw8971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8971 raw8971Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw8971 raw8971Labels = mixedMoment B raw8971step0 raw8971step0Labels := by
      have hz : ∀ j, raw8971 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8971step0 = (fun i j => raw8971 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8971step0 raw8971; decide +kernel
      have hl : raw8971step0Labels = raw8971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8971 raw8971Labels permutation265 hz
    mixedMoment B raw8971step0 raw8971step0Labels = mixedMoment B raw8971step1 raw8971step1Labels := by
      have ha : raw8971step1 = (fun i j => raw8971step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8971step1 raw8971step0; decide +kernel
      have hl : raw8971step1Labels = raw8971step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8971step0 raw8971step0Labels permutation33 permutation3
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw8972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8972 raw8972Labels = mixedMoment B node1019 node1019Labels := by
  calc
    mixedMoment B raw8972 raw8972Labels = mixedMoment B raw8972step0 raw8972step0Labels := by
      have hz : ∀ j, raw8972 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8972step0 = (fun i j => raw8972 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8972step0 raw8972; decide +kernel
      have hl : raw8972step0Labels = raw8972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8972 raw8972Labels permutation265 hz
    mixedMoment B raw8972step0 raw8972step0Labels = mixedMoment B raw8972step1 raw8972step1Labels := by
      have ha : raw8972step1 = (fun i j => raw8972step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8972step1 raw8972step0; decide +kernel
      have hl : raw8972step1Labels = raw8972step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8972step0 raw8972step0Labels permutation32 permutation3
    _ = mixedMoment B node1019 node1019Labels := by rfl

def raw8973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8973 raw8973Labels = mixedMoment B node2469 node2469Labels := by
  calc
    mixedMoment B raw8973 raw8973Labels = mixedMoment B raw8973step0 raw8973step0Labels := by
      have ha : raw8973step0 = (fun i j => raw8973 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8973step0 raw8973; decide +kernel
      have hl : raw8973step0Labels = raw8973Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8973 raw8973Labels permutation152 permutation3
    _ = mixedMoment B node2469 node2469Labels := by rfl

def raw8974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8974step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8974 raw8974Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw8974 raw8974Labels = mixedMoment B raw8974step0 raw8974step0Labels := by
      have hz : ∀ j, raw8974 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8974step0 = (fun i j => raw8974 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8974step0 raw8974; decide +kernel
      have hl : raw8974step0Labels = raw8974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8974 raw8974Labels permutation265 hz
    mixedMoment B raw8974step0 raw8974step0Labels = mixedMoment B raw8974step1 raw8974step1Labels := by
      have ha : raw8974step1 = (fun i j => raw8974step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8974step1 raw8974step0; decide +kernel
      have hl : raw8974step1Labels = raw8974step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8974step0 raw8974step0Labels permutation32 permutation3
    _ = mixedMoment B node2569 node2569Labels := by rfl

def raw8975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8975 raw8975Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw8975 raw8975Labels = mixedMoment B raw8975step0 raw8975step0Labels := by
      have hz : ∀ j, raw8975 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8975step0 = (fun i j => raw8975 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8975step0 raw8975; decide +kernel
      have hl : raw8975step0Labels = raw8975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8975 raw8975Labels permutation265 hz
    mixedMoment B raw8975step0 raw8975step0Labels = mixedMoment B raw8975step1 raw8975step1Labels := by
      have ha : raw8975step1 = (fun i j => raw8975step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8975step1 raw8975step0; decide +kernel
      have hl : raw8975step1Labels = raw8975step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8975step0 raw8975step0Labels permutation38 permutation3
    _ = mixedMoment B node2569 node2569Labels := by rfl

def raw8976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw8976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8976 raw8976Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw8976 raw8976Labels = mixedMoment B raw8976step0 raw8976step0Labels := by
      have hz : ∀ j, raw8976 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8976step0 = (fun i j => raw8976 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8976step0 raw8976; decide +kernel
      have hl : raw8976step0Labels = raw8976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8976 raw8976Labels permutation265 hz
    mixedMoment B raw8976step0 raw8976step0Labels = mixedMoment B raw8976step1 raw8976step1Labels := by
      have ha : raw8976step1 = (fun i j => raw8976step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8976step1 raw8976step0; decide +kernel
      have hl : raw8976step1Labels = raw8976step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8976step0 raw8976step0Labels permutation44 permutation3
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw8977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8977step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8977 raw8977Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw8977 raw8977Labels = mixedMoment B raw8977step0 raw8977step0Labels := by
      have ha : raw8977step0 = (fun i j => raw8977 (permutation577 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8977step0 raw8977; decide +kernel
      have hl : raw8977step0Labels = raw8977Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8977 raw8977Labels permutation577 permutation7
    mixedMoment B raw8977step0 raw8977step0Labels = mixedMoment B raw8977step1 raw8977step1Labels := by
      have ha : raw8977step1 = raw8977step0 := by apply Matrix.ext; unfold raw8977step1 raw8977step0; decide +kernel
      have hl : raw8977step0Labels = labelEmbedding1 ∘ raw8977step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8977step0 raw8977step0Labels raw8977step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3956 node3956Labels := by rfl

def raw8978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8978step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8978 raw8978Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw8978 raw8978Labels = mixedMoment B raw8978step0 raw8978step0Labels := by
      have hz : ∀ j, raw8978 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8978step0 = (fun i j => raw8978 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8978step0 raw8978; decide +kernel
      have hl : raw8978step0Labels = raw8978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8978 raw8978Labels permutation265 hz
    mixedMoment B raw8978step0 raw8978step0Labels = mixedMoment B raw8978step1 raw8978step1Labels := by
      have ha : raw8978step1 = (fun i j => raw8978step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8978step1 raw8978step0; decide +kernel
      have hl : raw8978step1Labels = raw8978step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8978step0 raw8978step0Labels permutation127 permutation7
    mixedMoment B raw8978step1 raw8978step1Labels = mixedMoment B raw8978step2 raw8978step2Labels := by
      have ha : raw8978step2 = raw8978step1 := by apply Matrix.ext; unfold raw8978step2 raw8978step1; decide +kernel
      have hl : raw8978step1Labels = labelEmbedding1 ∘ raw8978step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8978step1 raw8978step1Labels raw8978step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw8979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8979step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8979 raw8979Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw8979 raw8979Labels = mixedMoment B raw8979step0 raw8979step0Labels := by
      have hz : ∀ j, raw8979 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8979step0 = (fun i j => raw8979 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8979step0 raw8979; decide +kernel
      have hl : raw8979step0Labels = raw8979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8979 raw8979Labels permutation265 hz
    mixedMoment B raw8979step0 raw8979step0Labels = mixedMoment B raw8979step1 raw8979step1Labels := by
      have ha : raw8979step1 = (fun i j => raw8979step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8979step1 raw8979step0; decide +kernel
      have hl : raw8979step1Labels = raw8979step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8979step0 raw8979step0Labels permutation125 permutation7
    mixedMoment B raw8979step1 raw8979step1Labels = mixedMoment B raw8979step2 raw8979step2Labels := by
      have ha : raw8979step2 = raw8979step1 := by apply Matrix.ext; unfold raw8979step2 raw8979step1; decide +kernel
      have hl : raw8979step1Labels = labelEmbedding1 ∘ raw8979step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8979step1 raw8979step1Labels raw8979step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw8980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8980step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8980step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8980 raw8980Labels = mixedMoment B node4028 node4028Labels := by
  calc
    mixedMoment B raw8980 raw8980Labels = mixedMoment B raw8980step0 raw8980step0Labels := by
      have hz : ∀ j, raw8980 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8980step0 = (fun i j => raw8980 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8980step0 raw8980; decide +kernel
      have hl : raw8980step0Labels = raw8980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8980 raw8980Labels permutation265 hz
    mixedMoment B raw8980step0 raw8980step0Labels = mixedMoment B raw8980step1 raw8980step1Labels := by
      have ha : raw8980step1 = (fun i j => raw8980step0 (permutation104 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8980step1 raw8980step0; decide +kernel
      have hl : raw8980step1Labels = raw8980step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8980step0 raw8980step0Labels permutation104 permutation5
    mixedMoment B raw8980step1 raw8980step1Labels = mixedMoment B raw8980step2 raw8980step2Labels := by
      have ha : raw8980step2 = -raw8980step1 := by apply Matrix.ext; change ∀ i j, raw8980step2 i j = -(raw8980step1 i j); unfold raw8980step2 raw8980step1; decide +kernel
      have hl : raw8980step2Labels = raw8980step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8980step2 raw8980step2Labels = mixedMoment B raw8980step3 raw8980step3Labels := by
      have ha : raw8980step3 = raw8980step2 := by apply Matrix.ext; unfold raw8980step3 raw8980step2; decide +kernel
      have hl : raw8980step2Labels = labelEmbedding1 ∘ raw8980step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8980step2 raw8980step2Labels raw8980step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4028 node4028Labels := by rfl

def raw8981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8981 raw8981Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw8981 raw8981Labels = mixedMoment B raw8981step0 raw8981step0Labels := by
      have hz : ∀ j, raw8981 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8981step0 = (fun i j => raw8981 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8981step0 raw8981; decide +kernel
      have hl : raw8981step0Labels = raw8981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8981 raw8981Labels permutation265 hz
    mixedMoment B raw8981step0 raw8981step0Labels = mixedMoment B raw8981step1 raw8981step1Labels := by
      have ha : raw8981step1 = (fun i j => raw8981step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8981step1 raw8981step0; decide +kernel
      have hl : raw8981step1Labels = raw8981step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8981step0 raw8981step0Labels permutation125 permutation7
    mixedMoment B raw8981step1 raw8981step1Labels = mixedMoment B raw8981step2 raw8981step2Labels := by
      have ha : raw8981step2 = raw8981step1 := by apply Matrix.ext; unfold raw8981step2 raw8981step1; decide +kernel
      have hl : raw8981step1Labels = labelEmbedding1 ∘ raw8981step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8981step1 raw8981step1Labels raw8981step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw8982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8982step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8982step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8982 raw8982Labels = mixedMoment B node1642 node1642Labels := by
  calc
    mixedMoment B raw8982 raw8982Labels = mixedMoment B raw8982step0 raw8982step0Labels := by
      have ha : raw8982step0 = (fun i j => raw8982 (permutation232 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8982step0 raw8982; decide +kernel
      have hl : raw8982step0Labels = raw8982Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8982 raw8982Labels permutation232 permutation5
    mixedMoment B raw8982step0 raw8982step0Labels = mixedMoment B raw8982step1 raw8982step1Labels := by
      have ha : raw8982step1 = -raw8982step0 := by apply Matrix.ext; change ∀ i j, raw8982step1 i j = -(raw8982step0 i j); unfold raw8982step1 raw8982step0; decide +kernel
      have hl : raw8982step1Labels = raw8982step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8982step1 raw8982step1Labels = mixedMoment B raw8982step2 raw8982step2Labels := by
      have ha : raw8982step2 = raw8982step1 := by apply Matrix.ext; unfold raw8982step2 raw8982step1; decide +kernel
      have hl : raw8982step1Labels = labelEmbedding1 ∘ raw8982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8982step1 raw8982step1Labels raw8982step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1642 node1642Labels := by rfl

def raw8983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8983step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8983step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8983 raw8983Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw8983 raw8983Labels = mixedMoment B raw8983step0 raw8983step0Labels := by
      have ha : raw8983step0 = (fun i j => raw8983 (permutation232 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8983step0 raw8983; decide +kernel
      have hl : raw8983step0Labels = raw8983Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8983 raw8983Labels permutation232 permutation5
    mixedMoment B raw8983step0 raw8983step0Labels = mixedMoment B raw8983step1 raw8983step1Labels := by
      have ha : raw8983step1 = -raw8983step0 := by apply Matrix.ext; change ∀ i j, raw8983step1 i j = -(raw8983step0 i j); unfold raw8983step1 raw8983step0; decide +kernel
      have hl : raw8983step1Labels = raw8983step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8983step1 raw8983step1Labels = mixedMoment B raw8983step2 raw8983step2Labels := by
      have ha : raw8983step2 = raw8983step1 := by apply Matrix.ext; unfold raw8983step2 raw8983step1; decide +kernel
      have hl : raw8983step1Labels = labelEmbedding1 ∘ raw8983step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8983step1 raw8983step1Labels raw8983step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw8984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8984step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8984step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8984step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8984 raw8984Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw8984 raw8984Labels = mixedMoment B raw8984step0 raw8984step0Labels := by
      have ha : raw8984step0 = (fun i j => raw8984 (permutation236 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8984step0 raw8984; decide +kernel
      have hl : raw8984step0Labels = raw8984Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8984 raw8984Labels permutation236 permutation5
    mixedMoment B raw8984step0 raw8984step0Labels = mixedMoment B raw8984step1 raw8984step1Labels := by
      have ha : raw8984step1 = -raw8984step0 := by apply Matrix.ext; change ∀ i j, raw8984step1 i j = -(raw8984step0 i j); unfold raw8984step1 raw8984step0; decide +kernel
      have hl : raw8984step1Labels = raw8984step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8984step1 raw8984step1Labels = mixedMoment B raw8984step2 raw8984step2Labels := by
      have ha : raw8984step2 = raw8984step1 := by apply Matrix.ext; unfold raw8984step2 raw8984step1; decide +kernel
      have hl : raw8984step1Labels = labelEmbedding1 ∘ raw8984step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8984step1 raw8984step1Labels raw8984step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw8985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8985step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8985step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8985step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8985 raw8985Labels = mixedMoment B node3388 node3388Labels := by
  calc
    mixedMoment B raw8985 raw8985Labels = mixedMoment B raw8985step0 raw8985step0Labels := by
      have ha : raw8985step0 = (fun i j => raw8985 (permutation232 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8985step0 raw8985; decide +kernel
      have hl : raw8985step0Labels = raw8985Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8985 raw8985Labels permutation232 permutation5
    mixedMoment B raw8985step0 raw8985step0Labels = mixedMoment B raw8985step1 raw8985step1Labels := by
      have ha : raw8985step1 = -raw8985step0 := by apply Matrix.ext; change ∀ i j, raw8985step1 i j = -(raw8985step0 i j); unfold raw8985step1 raw8985step0; decide +kernel
      have hl : raw8985step1Labels = raw8985step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8985step1 raw8985step1Labels = mixedMoment B raw8985step2 raw8985step2Labels := by
      have ha : raw8985step2 = raw8985step1 := by apply Matrix.ext; unfold raw8985step2 raw8985step1; decide +kernel
      have hl : raw8985step1Labels = labelEmbedding1 ∘ raw8985step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8985step1 raw8985step1Labels raw8985step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3388 node3388Labels := by rfl

def raw8986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw8986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8986step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8986 raw8986Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw8986 raw8986Labels = mixedMoment B raw8986step0 raw8986step0Labels := by
      have ha : raw8986step0 = (fun i j => raw8986 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8986step0 raw8986; decide +kernel
      have hl : raw8986step0Labels = raw8986Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8986 raw8986Labels permutation243 permutation5
    mixedMoment B raw8986step0 raw8986step0Labels = mixedMoment B raw8986step1 raw8986step1Labels := by
      have ha : raw8986step1 = -raw8986step0 := by apply Matrix.ext; change ∀ i j, raw8986step1 i j = -(raw8986step0 i j); unfold raw8986step1 raw8986step0; decide +kernel
      have hl : raw8986step1Labels = raw8986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8986step1 raw8986step1Labels = mixedMoment B raw8986step2 raw8986step2Labels := by
      have ha : raw8986step2 = raw8986step1 := by apply Matrix.ext; unfold raw8986step2 raw8986step1; decide +kernel
      have hl : raw8986step1Labels = labelEmbedding1 ∘ raw8986step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8986step1 raw8986step1Labels raw8986step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw8987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8987step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8987step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8987step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8987 raw8987Labels = mixedMoment B node1646 node1646Labels := by
  calc
    mixedMoment B raw8987 raw8987Labels = mixedMoment B raw8987step0 raw8987step0Labels := by
      have hz : ∀ j, raw8987 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8987step0 = (fun i j => raw8987 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8987step0 raw8987; decide +kernel
      have hl : raw8987step0Labels = raw8987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8987 raw8987Labels permutation265 hz
    mixedMoment B raw8987step0 raw8987step0Labels = mixedMoment B raw8987step1 raw8987step1Labels := by
      have ha : raw8987step1 = (fun i j => raw8987step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8987step1 raw8987step0; decide +kernel
      have hl : raw8987step1Labels = raw8987step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8987step0 raw8987step0Labels permutation47 permutation5
    mixedMoment B raw8987step1 raw8987step1Labels = mixedMoment B raw8987step2 raw8987step2Labels := by
      have ha : raw8987step2 = -raw8987step1 := by apply Matrix.ext; change ∀ i j, raw8987step2 i j = -(raw8987step1 i j); unfold raw8987step2 raw8987step1; decide +kernel
      have hl : raw8987step2Labels = raw8987step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8987step2 raw8987step2Labels = mixedMoment B raw8987step3 raw8987step3Labels := by
      have ha : raw8987step3 = raw8987step2 := by apply Matrix.ext; unfold raw8987step3 raw8987step2; decide +kernel
      have hl : raw8987step2Labels = labelEmbedding1 ∘ raw8987step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8987step2 raw8987step2Labels raw8987step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1646 node1646Labels := by rfl

def raw8988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8988step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8988step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8988 raw8988Labels = mixedMoment B node3445 node3445Labels := by
  calc
    mixedMoment B raw8988 raw8988Labels = mixedMoment B raw8988step0 raw8988step0Labels := by
      have ha : raw8988step0 = (fun i j => raw8988 (permutation167 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8988step0 raw8988; decide +kernel
      have hl : raw8988step0Labels = raw8988Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8988 raw8988Labels permutation167 permutation5
    mixedMoment B raw8988step0 raw8988step0Labels = mixedMoment B raw8988step1 raw8988step1Labels := by
      have ha : raw8988step1 = -raw8988step0 := by apply Matrix.ext; change ∀ i j, raw8988step1 i j = -(raw8988step0 i j); unfold raw8988step1 raw8988step0; decide +kernel
      have hl : raw8988step1Labels = raw8988step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8988step1 raw8988step1Labels = mixedMoment B raw8988step2 raw8988step2Labels := by
      have ha : raw8988step2 = raw8988step1 := by apply Matrix.ext; unfold raw8988step2 raw8988step1; decide +kernel
      have hl : raw8988step1Labels = labelEmbedding1 ∘ raw8988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8988step1 raw8988step1Labels raw8988step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3445 node3445Labels := by rfl

def raw8989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8989step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8989step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8989 raw8989Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw8989 raw8989Labels = mixedMoment B raw8989step0 raw8989step0Labels := by
      have hz : ∀ j, raw8989 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8989step0 = (fun i j => raw8989 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8989step0 raw8989; decide +kernel
      have hl : raw8989step0Labels = raw8989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8989 raw8989Labels permutation265 hz
    mixedMoment B raw8989step0 raw8989step0Labels = mixedMoment B raw8989step1 raw8989step1Labels := by
      have ha : raw8989step1 = (fun i j => raw8989step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8989step1 raw8989step0; decide +kernel
      have hl : raw8989step1Labels = raw8989step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8989step0 raw8989step0Labels permutation47 permutation5
    mixedMoment B raw8989step1 raw8989step1Labels = mixedMoment B raw8989step2 raw8989step2Labels := by
      have ha : raw8989step2 = -raw8989step1 := by apply Matrix.ext; change ∀ i j, raw8989step2 i j = -(raw8989step1 i j); unfold raw8989step2 raw8989step1; decide +kernel
      have hl : raw8989step2Labels = raw8989step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8989step2 raw8989step2Labels = mixedMoment B raw8989step3 raw8989step3Labels := by
      have ha : raw8989step3 = raw8989step2 := by apply Matrix.ext; unfold raw8989step3 raw8989step2; decide +kernel
      have hl : raw8989step2Labels = labelEmbedding1 ∘ raw8989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8989step2 raw8989step2Labels raw8989step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw8990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8990step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8990step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8990 raw8990Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw8990 raw8990Labels = mixedMoment B raw8990step0 raw8990step0Labels := by
      have hz : ∀ j, raw8990 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8990step0 = (fun i j => raw8990 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8990step0 raw8990; decide +kernel
      have hl : raw8990step0Labels = raw8990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8990 raw8990Labels permutation265 hz
    mixedMoment B raw8990step0 raw8990step0Labels = mixedMoment B raw8990step1 raw8990step1Labels := by
      have ha : raw8990step1 = (fun i j => raw8990step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8990step1 raw8990step0; decide +kernel
      have hl : raw8990step1Labels = raw8990step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8990step0 raw8990step0Labels permutation47 permutation5
    mixedMoment B raw8990step1 raw8990step1Labels = mixedMoment B raw8990step2 raw8990step2Labels := by
      have ha : raw8990step2 = -raw8990step1 := by apply Matrix.ext; change ∀ i j, raw8990step2 i j = -(raw8990step1 i j); unfold raw8990step2 raw8990step1; decide +kernel
      have hl : raw8990step2Labels = raw8990step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8990step2 raw8990step2Labels = mixedMoment B raw8990step3 raw8990step3Labels := by
      have ha : raw8990step3 = raw8990step2 := by apply Matrix.ext; unfold raw8990step3 raw8990step2; decide +kernel
      have hl : raw8990step2Labels = labelEmbedding1 ∘ raw8990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8990step2 raw8990step2Labels raw8990step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3392 node3392Labels := by rfl

def raw8991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8991 raw8991Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw8991 raw8991Labels = mixedMoment B raw8991step0 raw8991step0Labels := by
      have hz : ∀ j, raw8991 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8991step0 = (fun i j => raw8991 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8991step0 raw8991; decide +kernel
      have hl : raw8991step0Labels = raw8991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8991 raw8991Labels permutation265 hz
    mixedMoment B raw8991step0 raw8991step0Labels = mixedMoment B raw8991step1 raw8991step1Labels := by
      have ha : raw8991step1 = (fun i j => raw8991step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8991step1 raw8991step0; decide +kernel
      have hl : raw8991step1Labels = raw8991step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8991step0 raw8991step0Labels permutation49 permutation5
    mixedMoment B raw8991step1 raw8991step1Labels = mixedMoment B raw8991step2 raw8991step2Labels := by
      have ha : raw8991step2 = -raw8991step1 := by apply Matrix.ext; change ∀ i j, raw8991step2 i j = -(raw8991step1 i j); unfold raw8991step2 raw8991step1; decide +kernel
      have hl : raw8991step2Labels = raw8991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8991step2 raw8991step2Labels = mixedMoment B raw8991step3 raw8991step3Labels := by
      have ha : raw8991step3 = raw8991step2 := by apply Matrix.ext; unfold raw8991step3 raw8991step2; decide +kernel
      have hl : raw8991step2Labels = labelEmbedding1 ∘ raw8991step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8991step2 raw8991step2Labels raw8991step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw8992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8992step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8992 raw8992Labels = mixedMoment B node1646 node1646Labels := by
  calc
    mixedMoment B raw8992 raw8992Labels = mixedMoment B raw8992step0 raw8992step0Labels := by
      have hz : ∀ j, raw8992 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8992step0 = (fun i j => raw8992 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8992step0 raw8992; decide +kernel
      have hl : raw8992step0Labels = raw8992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8992 raw8992Labels permutation265 hz
    mixedMoment B raw8992step0 raw8992step0Labels = mixedMoment B raw8992step1 raw8992step1Labels := by
      have ha : raw8992step1 = (fun i j => raw8992step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8992step1 raw8992step0; decide +kernel
      have hl : raw8992step1Labels = raw8992step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8992step0 raw8992step0Labels permutation45 permutation5
    mixedMoment B raw8992step1 raw8992step1Labels = mixedMoment B raw8992step2 raw8992step2Labels := by
      have ha : raw8992step2 = -raw8992step1 := by apply Matrix.ext; change ∀ i j, raw8992step2 i j = -(raw8992step1 i j); unfold raw8992step2 raw8992step1; decide +kernel
      have hl : raw8992step2Labels = raw8992step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8992step2 raw8992step2Labels = mixedMoment B raw8992step3 raw8992step3Labels := by
      have ha : raw8992step3 = raw8992step2 := by apply Matrix.ext; unfold raw8992step3 raw8992step2; decide +kernel
      have hl : raw8992step2Labels = labelEmbedding1 ∘ raw8992step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8992step2 raw8992step2Labels raw8992step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1646 node1646Labels := by rfl

def raw8993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8993step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8993step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8993 raw8993Labels = mixedMoment B node3445 node3445Labels := by
  calc
    mixedMoment B raw8993 raw8993Labels = mixedMoment B raw8993step0 raw8993step0Labels := by
      have ha : raw8993step0 = (fun i j => raw8993 (permutation165 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8993step0 raw8993; decide +kernel
      have hl : raw8993step0Labels = raw8993Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8993 raw8993Labels permutation165 permutation5
    mixedMoment B raw8993step0 raw8993step0Labels = mixedMoment B raw8993step1 raw8993step1Labels := by
      have ha : raw8993step1 = -raw8993step0 := by apply Matrix.ext; change ∀ i j, raw8993step1 i j = -(raw8993step0 i j); unfold raw8993step1 raw8993step0; decide +kernel
      have hl : raw8993step1Labels = raw8993step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8993step1 raw8993step1Labels = mixedMoment B raw8993step2 raw8993step2Labels := by
      have ha : raw8993step2 = raw8993step1 := by apply Matrix.ext; unfold raw8993step2 raw8993step1; decide +kernel
      have hl : raw8993step1Labels = labelEmbedding1 ∘ raw8993step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8993step1 raw8993step1Labels raw8993step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3445 node3445Labels := by rfl

def raw8994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8994 raw8994Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw8994 raw8994Labels = mixedMoment B raw8994step0 raw8994step0Labels := by
      have hz : ∀ j, raw8994 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8994step0 = (fun i j => raw8994 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8994step0 raw8994; decide +kernel
      have hl : raw8994step0Labels = raw8994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8994 raw8994Labels permutation265 hz
    mixedMoment B raw8994step0 raw8994step0Labels = mixedMoment B raw8994step1 raw8994step1Labels := by
      have ha : raw8994step1 = (fun i j => raw8994step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8994step1 raw8994step0; decide +kernel
      have hl : raw8994step1Labels = raw8994step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8994step0 raw8994step0Labels permutation45 permutation5
    mixedMoment B raw8994step1 raw8994step1Labels = mixedMoment B raw8994step2 raw8994step2Labels := by
      have ha : raw8994step2 = -raw8994step1 := by apply Matrix.ext; change ∀ i j, raw8994step2 i j = -(raw8994step1 i j); unfold raw8994step2 raw8994step1; decide +kernel
      have hl : raw8994step2Labels = raw8994step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8994step2 raw8994step2Labels = mixedMoment B raw8994step3 raw8994step3Labels := by
      have ha : raw8994step3 = raw8994step2 := by apply Matrix.ext; unfold raw8994step3 raw8994step2; decide +kernel
      have hl : raw8994step2Labels = labelEmbedding1 ∘ raw8994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8994step2 raw8994step2Labels raw8994step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw8995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8995 raw8995Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw8995 raw8995Labels = mixedMoment B raw8995step0 raw8995step0Labels := by
      have hz : ∀ j, raw8995 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8995step0 = (fun i j => raw8995 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8995step0 raw8995; decide +kernel
      have hl : raw8995step0Labels = raw8995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8995 raw8995Labels permutation265 hz
    mixedMoment B raw8995step0 raw8995step0Labels = mixedMoment B raw8995step1 raw8995step1Labels := by
      have ha : raw8995step1 = (fun i j => raw8995step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8995step1 raw8995step0; decide +kernel
      have hl : raw8995step1Labels = raw8995step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8995step0 raw8995step0Labels permutation45 permutation5
    mixedMoment B raw8995step1 raw8995step1Labels = mixedMoment B raw8995step2 raw8995step2Labels := by
      have ha : raw8995step2 = -raw8995step1 := by apply Matrix.ext; change ∀ i j, raw8995step2 i j = -(raw8995step1 i j); unfold raw8995step2 raw8995step1; decide +kernel
      have hl : raw8995step2Labels = raw8995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8995step2 raw8995step2Labels = mixedMoment B raw8995step3 raw8995step3Labels := by
      have ha : raw8995step3 = raw8995step2 := by apply Matrix.ext; unfold raw8995step3 raw8995step2; decide +kernel
      have hl : raw8995step2Labels = labelEmbedding1 ∘ raw8995step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8995step2 raw8995step2Labels raw8995step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3392 node3392Labels := by rfl

def raw8996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8996step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8996step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8996 raw8996Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw8996 raw8996Labels = mixedMoment B raw8996step0 raw8996step0Labels := by
      have hz : ∀ j, raw8996 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8996step0 = (fun i j => raw8996 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8996step0 raw8996; decide +kernel
      have hl : raw8996step0Labels = raw8996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8996 raw8996Labels permutation265 hz
    mixedMoment B raw8996step0 raw8996step0Labels = mixedMoment B raw8996step1 raw8996step1Labels := by
      have ha : raw8996step1 = (fun i j => raw8996step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8996step1 raw8996step0; decide +kernel
      have hl : raw8996step1Labels = raw8996step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8996step0 raw8996step0Labels permutation48 permutation5
    mixedMoment B raw8996step1 raw8996step1Labels = mixedMoment B raw8996step2 raw8996step2Labels := by
      have ha : raw8996step2 = -raw8996step1 := by apply Matrix.ext; change ∀ i j, raw8996step2 i j = -(raw8996step1 i j); unfold raw8996step2 raw8996step1; decide +kernel
      have hl : raw8996step2Labels = raw8996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8996step2 raw8996step2Labels = mixedMoment B raw8996step3 raw8996step3Labels := by
      have ha : raw8996step3 = raw8996step2 := by apply Matrix.ext; unfold raw8996step3 raw8996step2; decide +kernel
      have hl : raw8996step2Labels = labelEmbedding1 ∘ raw8996step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8996step2 raw8996step2Labels raw8996step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw8997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8997step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8997step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8997 raw8997Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw8997 raw8997Labels = mixedMoment B raw8997step0 raw8997step0Labels := by
      have hz : ∀ j, raw8997 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8997step0 = (fun i j => raw8997 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8997step0 raw8997; decide +kernel
      have hl : raw8997step0Labels = raw8997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8997 raw8997Labels permutation265 hz
    mixedMoment B raw8997step0 raw8997step0Labels = mixedMoment B raw8997step1 raw8997step1Labels := by
      have ha : raw8997step1 = (fun i j => raw8997step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8997step1 raw8997step0; decide +kernel
      have hl : raw8997step1Labels = raw8997step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8997step0 raw8997step0Labels permutation44 permutation5
    mixedMoment B raw8997step1 raw8997step1Labels = mixedMoment B raw8997step2 raw8997step2Labels := by
      have ha : raw8997step2 = -raw8997step1 := by apply Matrix.ext; change ∀ i j, raw8997step2 i j = -(raw8997step1 i j); unfold raw8997step2 raw8997step1; decide +kernel
      have hl : raw8997step2Labels = raw8997step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8997step2 raw8997step2Labels = mixedMoment B raw8997step3 raw8997step3Labels := by
      have ha : raw8997step3 = raw8997step2 := by apply Matrix.ext; unfold raw8997step3 raw8997step2; decide +kernel
      have hl : raw8997step2Labels = labelEmbedding1 ∘ raw8997step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8997step2 raw8997step2Labels raw8997step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

def raw8998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8998step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8998step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8998 raw8998Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw8998 raw8998Labels = mixedMoment B raw8998step0 raw8998step0Labels := by
      have ha : raw8998step0 = (fun i j => raw8998 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8998step0 raw8998; decide +kernel
      have hl : raw8998step0Labels = raw8998Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8998 raw8998Labels permutation164 permutation5
    mixedMoment B raw8998step0 raw8998step0Labels = mixedMoment B raw8998step1 raw8998step1Labels := by
      have ha : raw8998step1 = -raw8998step0 := by apply Matrix.ext; change ∀ i j, raw8998step1 i j = -(raw8998step0 i j); unfold raw8998step1 raw8998step0; decide +kernel
      have hl : raw8998step1Labels = raw8998step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8998step1 raw8998step1Labels = mixedMoment B raw8998step2 raw8998step2Labels := by
      have ha : raw8998step2 = raw8998step1 := by apply Matrix.ext; unfold raw8998step2 raw8998step1; decide +kernel
      have hl : raw8998step1Labels = labelEmbedding1 ∘ raw8998step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8998step1 raw8998step1Labels raw8998step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

def raw8999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw8999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw8999step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8999step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw8999step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8999 raw8999Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw8999 raw8999Labels = mixedMoment B raw8999step0 raw8999step0Labels := by
      have hz : ∀ j, raw8999 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8999step0 = (fun i j => raw8999 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8999step0 raw8999; decide +kernel
      have hl : raw8999step0Labels = raw8999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8999 raw8999Labels permutation265 hz
    mixedMoment B raw8999step0 raw8999step0Labels = mixedMoment B raw8999step1 raw8999step1Labels := by
      have ha : raw8999step1 = (fun i j => raw8999step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8999step1 raw8999step0; decide +kernel
      have hl : raw8999step1Labels = raw8999step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8999step0 raw8999step0Labels permutation34 permutation5
    mixedMoment B raw8999step1 raw8999step1Labels = mixedMoment B raw8999step2 raw8999step2Labels := by
      have ha : raw8999step2 = -raw8999step1 := by apply Matrix.ext; change ∀ i j, raw8999step2 i j = -(raw8999step1 i j); unfold raw8999step2 raw8999step1; decide +kernel
      have hl : raw8999step2Labels = raw8999step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8999step2 raw8999step2Labels = mixedMoment B raw8999step3 raw8999step3Labels := by
      have ha : raw8999step3 = raw8999step2 := by apply Matrix.ext; unfold raw8999step3 raw8999step2; decide +kernel
      have hl : raw8999step2Labels = labelEmbedding1 ∘ raw8999step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8999step2 raw8999step2Labels raw8999step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw9000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw9000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw9000step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw9000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9000 raw9000Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw9000 raw9000Labels = mixedMoment B raw9000step0 raw9000step0Labels := by
      have hz : ∀ j, raw9000 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9000step0 = (fun i j => raw9000 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9000step0 raw9000; decide +kernel
      have hl : raw9000step0Labels = raw9000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9000 raw9000Labels permutation265 hz
    mixedMoment B raw9000step0 raw9000step0Labels = mixedMoment B raw9000step1 raw9000step1Labels := by
      have ha : raw9000step1 = (fun i j => raw9000step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9000step1 raw9000step0; decide +kernel
      have hl : raw9000step1Labels = raw9000step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9000step0 raw9000step0Labels permutation40 permutation5
    mixedMoment B raw9000step1 raw9000step1Labels = mixedMoment B raw9000step2 raw9000step2Labels := by
      have ha : raw9000step2 = -raw9000step1 := by apply Matrix.ext; change ∀ i j, raw9000step2 i j = -(raw9000step1 i j); unfold raw9000step2 raw9000step1; decide +kernel
      have hl : raw9000step2Labels = raw9000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9000step2 raw9000step2Labels = mixedMoment B raw9000step3 raw9000step3Labels := by
      have ha : raw9000step3 = raw9000step2 := by apply Matrix.ext; unfold raw9000step3 raw9000step2; decide +kernel
      have hl : raw9000step2Labels = labelEmbedding1 ∘ raw9000step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9000step2 raw9000step2Labels raw9000step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw9001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw9001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw9001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw9001step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw9001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9001step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw9001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9001 raw9001Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw9001 raw9001Labels = mixedMoment B raw9001step0 raw9001step0Labels := by
      have hz : ∀ j, raw9001 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9001step0 = (fun i j => raw9001 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9001step0 raw9001; decide +kernel
      have hl : raw9001step0Labels = raw9001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9001 raw9001Labels permutation265 hz
    mixedMoment B raw9001step0 raw9001step0Labels = mixedMoment B raw9001step1 raw9001step1Labels := by
      have ha : raw9001step1 = (fun i j => raw9001step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9001step1 raw9001step0; decide +kernel
      have hl : raw9001step1Labels = raw9001step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9001step0 raw9001step0Labels permutation54 permutation5
    mixedMoment B raw9001step1 raw9001step1Labels = mixedMoment B raw9001step2 raw9001step2Labels := by
      have ha : raw9001step2 = -raw9001step1 := by apply Matrix.ext; change ∀ i j, raw9001step2 i j = -(raw9001step1 i j); unfold raw9001step2 raw9001step1; decide +kernel
      have hl : raw9001step2Labels = raw9001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9001step2 raw9001step2Labels = mixedMoment B raw9001step3 raw9001step3Labels := by
      have ha : raw9001step3 = raw9001step2 := by apply Matrix.ext; unfold raw9001step3 raw9001step2; decide +kernel
      have hl : raw9001step2Labels = labelEmbedding1 ∘ raw9001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9001step2 raw9001step2Labels raw9001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw9002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw9002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9002step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9002step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9002 raw9002Labels = mixedMoment B node1643 node1643Labels := by
  calc
    mixedMoment B raw9002 raw9002Labels = mixedMoment B raw9002step0 raw9002step0Labels := by
      have hz : ∀ j, raw9002 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9002step0 = (fun i j => raw9002 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9002step0 raw9002; decide +kernel
      have hl : raw9002step0Labels = raw9002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9002 raw9002Labels permutation265 hz
    mixedMoment B raw9002step0 raw9002step0Labels = mixedMoment B raw9002step1 raw9002step1Labels := by
      have ha : raw9002step1 = (fun i j => raw9002step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9002step1 raw9002step0; decide +kernel
      have hl : raw9002step1Labels = raw9002step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9002step0 raw9002step0Labels permutation44 permutation5
    mixedMoment B raw9002step1 raw9002step1Labels = mixedMoment B raw9002step2 raw9002step2Labels := by
      have ha : raw9002step2 = -raw9002step1 := by apply Matrix.ext; change ∀ i j, raw9002step2 i j = -(raw9002step1 i j); unfold raw9002step2 raw9002step1; decide +kernel
      have hl : raw9002step2Labels = raw9002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9002step2 raw9002step2Labels = mixedMoment B raw9002step3 raw9002step3Labels := by
      have ha : raw9002step3 = raw9002step2 := by apply Matrix.ext; unfold raw9002step3 raw9002step2; decide +kernel
      have hl : raw9002step2Labels = labelEmbedding1 ∘ raw9002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9002step2 raw9002step2Labels raw9002step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1643 node1643Labels := by rfl

def raw9003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw9003step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9003step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9003 raw9003Labels = mixedMoment B node3443 node3443Labels := by
  calc
    mixedMoment B raw9003 raw9003Labels = mixedMoment B raw9003step0 raw9003step0Labels := by
      have ha : raw9003step0 = (fun i j => raw9003 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9003step0 raw9003; decide +kernel
      have hl : raw9003step0Labels = raw9003Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9003 raw9003Labels permutation164 permutation5
    mixedMoment B raw9003step0 raw9003step0Labels = mixedMoment B raw9003step1 raw9003step1Labels := by
      have ha : raw9003step1 = -raw9003step0 := by apply Matrix.ext; change ∀ i j, raw9003step1 i j = -(raw9003step0 i j); unfold raw9003step1 raw9003step0; decide +kernel
      have hl : raw9003step1Labels = raw9003step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9003step1 raw9003step1Labels = mixedMoment B raw9003step2 raw9003step2Labels := by
      have ha : raw9003step2 = raw9003step1 := by apply Matrix.ext; unfold raw9003step2 raw9003step1; decide +kernel
      have hl : raw9003step1Labels = labelEmbedding1 ∘ raw9003step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9003step1 raw9003step1Labels raw9003step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3443 node3443Labels := by rfl

def raw9004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9004 raw9004Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw9004 raw9004Labels = mixedMoment B raw9004step0 raw9004step0Labels := by
      have hz : ∀ j, raw9004 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9004step0 = (fun i j => raw9004 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9004step0 raw9004; decide +kernel
      have hl : raw9004step0Labels = raw9004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9004 raw9004Labels permutation265 hz
    mixedMoment B raw9004step0 raw9004step0Labels = mixedMoment B raw9004step1 raw9004step1Labels := by
      have ha : raw9004step1 = (fun i j => raw9004step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9004step1 raw9004step0; decide +kernel
      have hl : raw9004step1Labels = raw9004step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9004step0 raw9004step0Labels permutation143 permutation5
    mixedMoment B raw9004step1 raw9004step1Labels = mixedMoment B raw9004step2 raw9004step2Labels := by
      have ha : raw9004step2 = raw9004step1 := by apply Matrix.ext; unfold raw9004step2 raw9004step1; decide +kernel
      have hl : raw9004step1Labels = labelEmbedding1 ∘ raw9004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9004step1 raw9004step1Labels raw9004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw9005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9005step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9005step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9005 raw9005Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw9005 raw9005Labels = mixedMoment B raw9005step0 raw9005step0Labels := by
      have hz : ∀ j, raw9005 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9005step0 = (fun i j => raw9005 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9005step0 raw9005; decide +kernel
      have hl : raw9005step0Labels = raw9005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9005 raw9005Labels permutation265 hz
    mixedMoment B raw9005step0 raw9005step0Labels = mixedMoment B raw9005step1 raw9005step1Labels := by
      have ha : raw9005step1 = (fun i j => raw9005step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9005step1 raw9005step0; decide +kernel
      have hl : raw9005step1Labels = raw9005step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9005step0 raw9005step0Labels permutation137 permutation5
    mixedMoment B raw9005step1 raw9005step1Labels = mixedMoment B raw9005step2 raw9005step2Labels := by
      have ha : raw9005step2 = raw9005step1 := by apply Matrix.ext; unfold raw9005step2 raw9005step1; decide +kernel
      have hl : raw9005step1Labels = labelEmbedding1 ∘ raw9005step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9005step1 raw9005step1Labels raw9005step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw9006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw9006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw9006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw9006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9006 raw9006Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw9006 raw9006Labels = mixedMoment B raw9006step0 raw9006step0Labels := by
      have hz : ∀ j, raw9006 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9006step0 = (fun i j => raw9006 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9006step0 raw9006; decide +kernel
      have hl : raw9006step0Labels = raw9006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9006 raw9006Labels permutation265 hz
    mixedMoment B raw9006step0 raw9006step0Labels = mixedMoment B raw9006step1 raw9006step1Labels := by
      have ha : raw9006step1 = (fun i j => raw9006step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9006step1 raw9006step0; decide +kernel
      have hl : raw9006step1Labels = raw9006step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9006step0 raw9006step0Labels permutation44 permutation5
    mixedMoment B raw9006step1 raw9006step1Labels = mixedMoment B raw9006step2 raw9006step2Labels := by
      have ha : raw9006step2 = -raw9006step1 := by apply Matrix.ext; change ∀ i j, raw9006step2 i j = -(raw9006step1 i j); unfold raw9006step2 raw9006step1; decide +kernel
      have hl : raw9006step2Labels = raw9006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9006step2 raw9006step2Labels = mixedMoment B raw9006step3 raw9006step3Labels := by
      have ha : raw9006step3 = raw9006step2 := by apply Matrix.ext; unfold raw9006step3 raw9006step2; decide +kernel
      have hl : raw9006step2Labels = labelEmbedding1 ∘ raw9006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9006step2 raw9006step2Labels raw9006step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3389 node3389Labels := by rfl

def raw9007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9007 raw9007Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw9007 raw9007Labels = mixedMoment B raw9007step0 raw9007step0Labels := by
      have hz : ∀ j, raw9007 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9007step0 = (fun i j => raw9007 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9007step0 raw9007; decide +kernel
      have hl : raw9007step0Labels = raw9007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9007 raw9007Labels permutation265 hz
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw9008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9008 raw9008Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw9008 raw9008Labels = mixedMoment B raw9008step0 raw9008step0Labels := by
      have ha : raw9008step0 = (fun i j => raw9008 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9008step0 raw9008; decide +kernel
      have hl : raw9008step0Labels = raw9008Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9008 raw9008Labels permutation682 permutation2
    mixedMoment B raw9008step0 raw9008step0Labels = mixedMoment B raw9008step1 raw9008step1Labels := by
      have ha : raw9008step1 = -raw9008step0 := by apply Matrix.ext; change ∀ i j, raw9008step1 i j = -(raw9008step0 i j); unfold raw9008step1 raw9008step0; decide +kernel
      have hl : raw9008step1Labels = raw9008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3953 node3953Labels := by rfl

def raw9009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9009 raw9009Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw9009 raw9009Labels = mixedMoment B raw9009step0 raw9009step0Labels := by
      have hz : ∀ j, raw9009 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9009step0 = (fun i j => raw9009 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9009step0 raw9009; decide +kernel
      have hl : raw9009step0Labels = raw9009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9009 raw9009Labels permutation265 hz
    mixedMoment B raw9009step0 raw9009step0Labels = mixedMoment B raw9009step1 raw9009step1Labels := by
      have ha : raw9009step1 = (fun i j => raw9009step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9009step1 raw9009step0; decide +kernel
      have hl : raw9009step1Labels = raw9009step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9009step0 raw9009step0Labels permutation151 permutation2
    mixedMoment B raw9009step1 raw9009step1Labels = mixedMoment B raw9009step2 raw9009step2Labels := by
      have ha : raw9009step2 = -raw9009step1 := by apply Matrix.ext; change ∀ i j, raw9009step2 i j = -(raw9009step1 i j); unfold raw9009step2 raw9009step1; decide +kernel
      have hl : raw9009step2Labels = raw9009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw9010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9010 raw9010Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw9010 raw9010Labels = mixedMoment B raw9010step0 raw9010step0Labels := by
      have hz : ∀ j, raw9010 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9010step0 = (fun i j => raw9010 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9010step0 raw9010; decide +kernel
      have hl : raw9010step0Labels = raw9010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9010 raw9010Labels permutation265 hz
    mixedMoment B raw9010step0 raw9010step0Labels = mixedMoment B raw9010step1 raw9010step1Labels := by
      have ha : raw9010step1 = (fun i j => raw9010step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9010step1 raw9010step0; decide +kernel
      have hl : raw9010step1Labels = raw9010step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9010step0 raw9010step0Labels permutation149 permutation2
    mixedMoment B raw9010step1 raw9010step1Labels = mixedMoment B raw9010step2 raw9010step2Labels := by
      have ha : raw9010step2 = -raw9010step1 := by apply Matrix.ext; change ∀ i j, raw9010step2 i j = -(raw9010step1 i j); unfold raw9010step2 raw9010step1; decide +kernel
      have hl : raw9010step2Labels = raw9010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw9011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw9011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9011step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9011 raw9011Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw9011 raw9011Labels = mixedMoment B raw9011step0 raw9011step0Labels := by
      have hz : ∀ j, raw9011 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9011step0 = (fun i j => raw9011 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9011step0 raw9011; decide +kernel
      have hl : raw9011step0Labels = raw9011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9011 raw9011Labels permutation265 hz
    mixedMoment B raw9011step0 raw9011step0Labels = mixedMoment B raw9011step1 raw9011step1Labels := by
      have ha : raw9011step1 = (fun i j => raw9011step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9011step1 raw9011step0; decide +kernel
      have hl : raw9011step1Labels = raw9011step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9011step0 raw9011step0Labels permutation108 permutation4
    mixedMoment B raw9011step1 raw9011step1Labels = mixedMoment B raw9011step2 raw9011step2Labels := by
      have ha : raw9011step2 = -raw9011step1 := by apply Matrix.ext; change ∀ i j, raw9011step2 i j = -(raw9011step1 i j); unfold raw9011step2 raw9011step1; decide +kernel
      have hl : raw9011step2Labels = raw9011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw9012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw9012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw9012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9012 raw9012Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw9012 raw9012Labels = mixedMoment B raw9012step0 raw9012step0Labels := by
      have hz : ∀ j, raw9012 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9012step0 = (fun i j => raw9012 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9012step0 raw9012; decide +kernel
      have hl : raw9012step0Labels = raw9012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9012 raw9012Labels permutation265 hz
    mixedMoment B raw9012step0 raw9012step0Labels = mixedMoment B raw9012step1 raw9012step1Labels := by
      have ha : raw9012step1 = (fun i j => raw9012step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9012step1 raw9012step0; decide +kernel
      have hl : raw9012step1Labels = raw9012step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9012step0 raw9012step0Labels permutation33 permutation2
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw9013 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw9013Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9013step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw9013step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9013step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw9013step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9013step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw9013step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical9013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9013 raw9013Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9013 raw9013Labels = mixedMoment B raw9013step0 raw9013step0Labels := by
      have hz : ∀ j, raw9013 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9013step0 = (fun i j => raw9013 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9013step0 raw9013; decide +kernel
      have hl : raw9013step0Labels = raw9013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9013 raw9013Labels permutation265 hz
    mixedMoment B raw9013step0 raw9013step0Labels = mixedMoment B raw9013step1 raw9013step1Labels := by
      have ha : raw9013step1 = (fun i j => raw9013step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9013step1 raw9013step0; decide +kernel
      have hl : raw9013step1Labels = raw9013step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9013step0 raw9013step0Labels permutation122 permutation0
    mixedMoment B raw9013step1 raw9013step1Labels = mixedMoment B raw9013step2 raw9013step2Labels := by
      have ha : raw9013step2 = -raw9013step1 := by apply Matrix.ext; change ∀ i j, raw9013step2 i j = -(raw9013step1 i j); unfold raw9013step2 raw9013step1; decide +kernel
      have hl : raw9013step2Labels = raw9013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw9014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9014 raw9014Labels = mixedMoment B node1384 node1384Labels := by
  calc
    mixedMoment B raw9014 raw9014Labels = mixedMoment B raw9014step0 raw9014step0Labels := by
      have ha : raw9014step0 = (fun i j => raw9014 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9014step0 raw9014; decide +kernel
      have hl : raw9014step0Labels = raw9014Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9014 raw9014Labels permutation182 permutation2
    _ = mixedMoment B node1384 node1384Labels := by rfl

def raw9015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9015 raw9015Labels = mixedMoment B node1407 node1407Labels := by
  calc
    mixedMoment B raw9015 raw9015Labels = mixedMoment B raw9015step0 raw9015step0Labels := by
      have hz : ∀ j, raw9015 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9015step0 = (fun i j => raw9015 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9015step0 raw9015; decide +kernel
      have hl : raw9015step0Labels = raw9015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9015 raw9015Labels permutation265 hz
    mixedMoment B raw9015step0 raw9015step0Labels = mixedMoment B raw9015step1 raw9015step1Labels := by
      have ha : raw9015step1 = (fun i j => raw9015step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9015step1 raw9015step0; decide +kernel
      have hl : raw9015step1Labels = raw9015step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9015step0 raw9015step0Labels permutation38 permutation2
    _ = mixedMoment B node1407 node1407Labels := by rfl

def raw9016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9016 raw9016Labels = mixedMoment B node1407 node1407Labels := by
  calc
    mixedMoment B raw9016 raw9016Labels = mixedMoment B raw9016step0 raw9016step0Labels := by
      have hz : ∀ j, raw9016 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9016step0 = (fun i j => raw9016 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9016step0 raw9016; decide +kernel
      have hl : raw9016step0Labels = raw9016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9016 raw9016Labels permutation265 hz
    _ = mixedMoment B node1407 node1407Labels := by rfl

def raw9017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9017 raw9017Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw9017 raw9017Labels = mixedMoment B raw9017step0 raw9017step0Labels := by
      have hz : ∀ j, raw9017 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9017step0 = (fun i j => raw9017 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9017step0 raw9017; decide +kernel
      have hl : raw9017step0Labels = raw9017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9017 raw9017Labels permutation265 hz
    mixedMoment B raw9017step0 raw9017step0Labels = mixedMoment B raw9017step1 raw9017step1Labels := by
      have ha : raw9017step1 = (fun i j => raw9017step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9017step1 raw9017step0; decide +kernel
      have hl : raw9017step1Labels = raw9017step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9017step0 raw9017step0Labels permutation33 permutation2
    _ = mixedMoment B node1391 node1391Labels := by rfl

def raw9018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9018 raw9018Labels = mixedMoment B node1389 node1389Labels := by
  calc
    mixedMoment B raw9018 raw9018Labels = mixedMoment B raw9018step0 raw9018step0Labels := by
      have hz : ∀ j, raw9018 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9018step0 = (fun i j => raw9018 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9018step0 raw9018; decide +kernel
      have hl : raw9018step0Labels = raw9018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9018 raw9018Labels permutation265 hz
    _ = mixedMoment B node1389 node1389Labels := by rfl

def raw9019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9019 raw9019Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw9019 raw9019Labels = mixedMoment B raw9019step0 raw9019step0Labels := by
      have ha : raw9019step0 = (fun i j => raw9019 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9019step0 raw9019; decide +kernel
      have hl : raw9019step0Labels = raw9019Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9019 raw9019Labels permutation182 permutation2
    _ = mixedMoment B node2925 node2925Labels := by rfl

def raw9020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9020 raw9020Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw9020 raw9020Labels = mixedMoment B raw9020step0 raw9020step0Labels := by
      have ha : raw9020step0 = (fun i j => raw9020 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9020step0 raw9020; decide +kernel
      have hl : raw9020step0Labels = raw9020Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9020 raw9020Labels permutation206 permutation2
    _ = mixedMoment B node2925 node2925Labels := by rfl

def raw9021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9021 raw9021Labels = mixedMoment B node3068 node3068Labels := by
  calc
    mixedMoment B raw9021 raw9021Labels = mixedMoment B raw9021step0 raw9021step0Labels := by
      have ha : raw9021step0 = (fun i j => raw9021 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9021step0 raw9021; decide +kernel
      have hl : raw9021step0Labels = raw9021Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9021 raw9021Labels permutation184 permutation2
    _ = mixedMoment B node3068 node3068Labels := by rfl

def raw9022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw9022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9022 raw9022Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw9022 raw9022Labels = mixedMoment B raw9022step0 raw9022step0Labels := by
      have ha : raw9022step0 = (fun i j => raw9022 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9022step0 raw9022; decide +kernel
      have hl : raw9022step0Labels = raw9022Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9022 raw9022Labels permutation183 permutation2
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw9023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9023 raw9023Labels = mixedMoment B node2985 node2985Labels := by
  calc
    mixedMoment B raw9023 raw9023Labels = mixedMoment B raw9023step0 raw9023step0Labels := by
      have ha : raw9023step0 = (fun i j => raw9023 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9023step0 raw9023; decide +kernel
      have hl : raw9023step0Labels = raw9023Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9023 raw9023Labels permutation158 permutation2
    _ = mixedMoment B node2985 node2985Labels := by rfl

def raw9024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9024 raw9024Labels = mixedMoment B node2985 node2985Labels := by
  calc
    _ = mixedMoment B node2985 node2985Labels := by rfl

def raw9025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9025 raw9025Labels = mixedMoment B node2981 node2981Labels := by
  calc
    mixedMoment B raw9025 raw9025Labels = mixedMoment B raw9025step0 raw9025step0Labels := by
      have ha : raw9025step0 = (fun i j => raw9025 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9025step0 raw9025; decide +kernel
      have hl : raw9025step0Labels = raw9025Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9025 raw9025Labels permutation153 permutation2
    _ = mixedMoment B node2981 node2981Labels := by rfl

def raw9026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw9026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9026 raw9026Labels = mixedMoment B node2857 node2857Labels := by
  calc
    mixedMoment B raw9026 raw9026Labels = mixedMoment B raw9026step0 raw9026step0Labels := by
      have ha : raw9026step0 = (fun i j => raw9026 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9026step0 raw9026; decide +kernel
      have hl : raw9026step0Labels = raw9026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9026 raw9026Labels permutation682 permutation2
    mixedMoment B raw9026step0 raw9026step0Labels = mixedMoment B raw9026step1 raw9026step1Labels := by
      have ha : raw9026step1 = -raw9026step0 := by apply Matrix.ext; change ∀ i j, raw9026step1 i j = -(raw9026step0 i j); unfold raw9026step1 raw9026step0; decide +kernel
      have hl : raw9026step1Labels = raw9026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2857 node2857Labels := by rfl

def raw9027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9027 raw9027Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw9027 raw9027Labels = mixedMoment B raw9027step0 raw9027step0Labels := by
      have hz : ∀ j, raw9027 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9027step0 = (fun i j => raw9027 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9027step0 raw9027; decide +kernel
      have hl : raw9027step0Labels = raw9027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9027 raw9027Labels permutation265 hz
    mixedMoment B raw9027step0 raw9027step0Labels = mixedMoment B raw9027step1 raw9027step1Labels := by
      have ha : raw9027step1 = (fun i j => raw9027step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9027step1 raw9027step0; decide +kernel
      have hl : raw9027step1Labels = raw9027step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9027step0 raw9027step0Labels permutation38 permutation2
    _ = mixedMoment B node2955 node2955Labels := by rfl

def raw9028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9028 raw9028Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw9028 raw9028Labels = mixedMoment B raw9028step0 raw9028step0Labels := by
      have hz : ∀ j, raw9028 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9028step0 = (fun i j => raw9028 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9028step0 raw9028; decide +kernel
      have hl : raw9028step0Labels = raw9028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9028 raw9028Labels permutation265 hz
    mixedMoment B raw9028step0 raw9028step0Labels = mixedMoment B raw9028step1 raw9028step1Labels := by
      have ha : raw9028step1 = (fun i j => raw9028step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9028step1 raw9028step0; decide +kernel
      have hl : raw9028step1Labels = raw9028step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9028step0 raw9028step0Labels permutation40 permutation2
    _ = mixedMoment B node3092 node3092Labels := by rfl

def raw9029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw9029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw9029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9029 raw9029Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw9029 raw9029Labels = mixedMoment B raw9029step0 raw9029step0Labels := by
      have hz : ∀ j, raw9029 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9029step0 = (fun i j => raw9029 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9029step0 raw9029; decide +kernel
      have hl : raw9029step0Labels = raw9029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9029 raw9029Labels permutation265 hz
    mixedMoment B raw9029step0 raw9029step0Labels = mixedMoment B raw9029step1 raw9029step1Labels := by
      have ha : raw9029step1 = (fun i j => raw9029step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9029step1 raw9029step0; decide +kernel
      have hl : raw9029step1Labels = raw9029step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9029step0 raw9029step0Labels permutation39 permutation2
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw9030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9030 raw9030Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw9030 raw9030Labels = mixedMoment B raw9030step0 raw9030step0Labels := by
      have hz : ∀ j, raw9030 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9030step0 = (fun i j => raw9030 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9030step0 raw9030; decide +kernel
      have hl : raw9030step0Labels = raw9030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9030 raw9030Labels permutation265 hz
    _ = mixedMoment B node2955 node2955Labels := by rfl

def raw9031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9031 raw9031Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw9031 raw9031Labels = mixedMoment B raw9031step0 raw9031step0Labels := by
      have hz : ∀ j, raw9031 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9031step0 = (fun i j => raw9031 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9031step0 raw9031; decide +kernel
      have hl : raw9031step0Labels = raw9031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9031 raw9031Labels permutation265 hz
    mixedMoment B raw9031step0 raw9031step0Labels = mixedMoment B raw9031step1 raw9031step1Labels := by
      have ha : raw9031step1 = (fun i j => raw9031step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9031step1 raw9031step0; decide +kernel
      have hl : raw9031step1Labels = raw9031step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9031step0 raw9031step0Labels permutation33 permutation2
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw9032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9032 raw9032Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw9032 raw9032Labels = mixedMoment B raw9032step0 raw9032step0Labels := by
      have hz : ∀ j, raw9032 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9032step0 = (fun i j => raw9032 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9032step0 raw9032; decide +kernel
      have hl : raw9032step0Labels = raw9032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9032 raw9032Labels permutation265 hz
    mixedMoment B raw9032step0 raw9032step0Labels = mixedMoment B raw9032step1 raw9032step1Labels := by
      have ha : raw9032step1 = (fun i j => raw9032step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9032step1 raw9032step0; decide +kernel
      have hl : raw9032step1Labels = raw9032step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9032step0 raw9032step0Labels permutation151 permutation2
    mixedMoment B raw9032step1 raw9032step1Labels = mixedMoment B raw9032step2 raw9032step2Labels := by
      have ha : raw9032step2 = -raw9032step1 := by apply Matrix.ext; change ∀ i j, raw9032step2 i j = -(raw9032step1 i j); unfold raw9032step2 raw9032step1; decide +kernel
      have hl : raw9032step2Labels = raw9032step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw9033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9033 raw9033Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw9033 raw9033Labels = mixedMoment B raw9033step0 raw9033step0Labels := by
      have hz : ∀ j, raw9033 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9033step0 = (fun i j => raw9033 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9033step0 raw9033; decide +kernel
      have hl : raw9033step0Labels = raw9033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9033 raw9033Labels permutation265 hz
    mixedMoment B raw9033step0 raw9033step0Labels = mixedMoment B raw9033step1 raw9033step1Labels := by
      have ha : raw9033step1 = (fun i j => raw9033step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9033step1 raw9033step0; decide +kernel
      have hl : raw9033step1Labels = raw9033step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9033step0 raw9033step0Labels permutation39 permutation2
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw9034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw9034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw9034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9034 raw9034Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw9034 raw9034Labels = mixedMoment B raw9034step0 raw9034step0Labels := by
      have hz : ∀ j, raw9034 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9034step0 = (fun i j => raw9034 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9034step0 raw9034; decide +kernel
      have hl : raw9034step0Labels = raw9034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9034 raw9034Labels permutation265 hz
    mixedMoment B raw9034step0 raw9034step0Labels = mixedMoment B raw9034step1 raw9034step1Labels := by
      have ha : raw9034step1 = (fun i j => raw9034step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9034step1 raw9034step0; decide +kernel
      have hl : raw9034step1Labels = raw9034step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9034step0 raw9034step0Labels permutation33 permutation2
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw9035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9035 raw9035Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw9035 raw9035Labels = mixedMoment B raw9035step0 raw9035step0Labels := by
      have hz : ∀ j, raw9035 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9035step0 = (fun i j => raw9035 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9035step0 raw9035; decide +kernel
      have hl : raw9035step0Labels = raw9035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9035 raw9035Labels permutation265 hz
    mixedMoment B raw9035step0 raw9035step0Labels = mixedMoment B raw9035step1 raw9035step1Labels := by
      have ha : raw9035step1 = (fun i j => raw9035step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9035step1 raw9035step0; decide +kernel
      have hl : raw9035step1Labels = raw9035step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9035step0 raw9035step0Labels permutation34 permutation2
    _ = mixedMoment B node3092 node3092Labels := by rfl

def raw9036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw9036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw9036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9036 raw9036Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw9036 raw9036Labels = mixedMoment B raw9036step0 raw9036step0Labels := by
      have hz : ∀ j, raw9036 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9036step0 = (fun i j => raw9036 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9036step0 raw9036; decide +kernel
      have hl : raw9036step0Labels = raw9036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9036 raw9036Labels permutation265 hz
    mixedMoment B raw9036step0 raw9036step0Labels = mixedMoment B raw9036step1 raw9036step1Labels := by
      have ha : raw9036step1 = (fun i j => raw9036step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9036step1 raw9036step0; decide +kernel
      have hl : raw9036step1Labels = raw9036step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9036step0 raw9036step0Labels permutation149 permutation2
    mixedMoment B raw9036step1 raw9036step1Labels = mixedMoment B raw9036step2 raw9036step2Labels := by
      have ha : raw9036step2 = -raw9036step1 := by apply Matrix.ext; change ∀ i j, raw9036step2 i j = -(raw9036step1 i j); unfold raw9036step2 raw9036step1; decide +kernel
      have hl : raw9036step2Labels = raw9036step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3031 node3031Labels := by rfl

def raw9037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9037step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9037 raw9037Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw9037 raw9037Labels = mixedMoment B raw9037step0 raw9037step0Labels := by
      have hz : ∀ j, raw9037 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9037step0 = (fun i j => raw9037 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9037step0 raw9037; decide +kernel
      have hl : raw9037step0Labels = raw9037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9037 raw9037Labels permutation265 hz
    mixedMoment B raw9037step0 raw9037step0Labels = mixedMoment B raw9037step1 raw9037step1Labels := by
      have ha : raw9037step1 = (fun i j => raw9037step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9037step1 raw9037step0; decide +kernel
      have hl : raw9037step1Labels = raw9037step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9037step0 raw9037step0Labels permutation149 permutation2
    mixedMoment B raw9037step1 raw9037step1Labels = mixedMoment B raw9037step2 raw9037step2Labels := by
      have ha : raw9037step2 = -raw9037step1 := by apply Matrix.ext; change ∀ i j, raw9037step2 i j = -(raw9037step1 i j); unfold raw9037step2 raw9037step1; decide +kernel
      have hl : raw9037step2Labels = raw9037step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw9038 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9038step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9038step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9038 raw9038Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw9038 raw9038Labels = mixedMoment B raw9038step0 raw9038step0Labels := by
      have hz : ∀ j, raw9038 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9038step0 = (fun i j => raw9038 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9038step0 raw9038; decide +kernel
      have hl : raw9038step0Labels = raw9038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9038 raw9038Labels permutation434 hz
    mixedMoment B raw9038step0 raw9038step0Labels = mixedMoment B raw9038step1 raw9038step1Labels := by
      have hz : ∀ j, raw9038step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9038step1 = (fun i j => raw9038step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9038step1 raw9038step0; decide +kernel
      have hl : raw9038step1Labels = raw9038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9038step0 raw9038step0Labels permutation56 hz
    mixedMoment B raw9038step1 raw9038step1Labels = mixedMoment B raw9038step2 raw9038step2Labels := by
      have ha : raw9038step2 = (fun i j => raw9038step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9038step2 raw9038step1; decide +kernel
      have hl : raw9038step2Labels = raw9038step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9038step1 raw9038step1Labels permutation8 permutation7
    mixedMoment B raw9038step2 raw9038step2Labels = mixedMoment B raw9038step3 raw9038step3Labels := by
      have ha : raw9038step3 = raw9038step2 := by apply Matrix.ext; unfold raw9038step3 raw9038step2; decide +kernel
      have hl : raw9038step2Labels = labelEmbedding10 ∘ raw9038step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9038step2 raw9038step2Labels raw9038step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw9039 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9039step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9039 raw9039Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw9039 raw9039Labels = mixedMoment B raw9039step0 raw9039step0Labels := by
      have hz : ∀ j, raw9039 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9039step0 = (fun i j => raw9039 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9039step0 raw9039; decide +kernel
      have hl : raw9039step0Labels = raw9039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9039 raw9039Labels permutation265 hz
    mixedMoment B raw9039step0 raw9039step0Labels = mixedMoment B raw9039step1 raw9039step1Labels := by
      have ha : raw9039step1 = (fun i j => raw9039step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9039step1 raw9039step0; decide +kernel
      have hl : raw9039step1Labels = raw9039step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9039step0 raw9039step0Labels permutation125 permutation3
    mixedMoment B raw9039step1 raw9039step1Labels = mixedMoment B raw9039step2 raw9039step2Labels := by
      have ha : raw9039step2 = raw9039step1 := by apply Matrix.ext; unfold raw9039step2 raw9039step1; decide +kernel
      have hl : raw9039step1Labels = labelEmbedding6 ∘ raw9039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9039step1 raw9039step1Labels raw9039step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

def raw9040 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9040step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9040 raw9040Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw9040 raw9040Labels = mixedMoment B raw9040step0 raw9040step0Labels := by
      have hz : ∀ j, raw9040 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9040step0 = (fun i j => raw9040 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9040step0 raw9040; decide +kernel
      have hl : raw9040step0Labels = raw9040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9040 raw9040Labels permutation265 hz
    mixedMoment B raw9040step0 raw9040step0Labels = mixedMoment B raw9040step1 raw9040step1Labels := by
      have ha : raw9040step1 = (fun i j => raw9040step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9040step1 raw9040step0; decide +kernel
      have hl : raw9040step1Labels = raw9040step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9040step0 raw9040step0Labels permutation32 permutation7
    mixedMoment B raw9040step1 raw9040step1Labels = mixedMoment B raw9040step2 raw9040step2Labels := by
      have ha : raw9040step2 = raw9040step1 := by apply Matrix.ext; unfold raw9040step2 raw9040step1; decide +kernel
      have hl : raw9040step1Labels = labelEmbedding10 ∘ raw9040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9040step1 raw9040step1Labels raw9040step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw9041 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9041step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9041step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9041 raw9041Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw9041 raw9041Labels = mixedMoment B raw9041step0 raw9041step0Labels := by
      have hz : ∀ j, raw9041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9041step0 = (fun i j => raw9041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9041step0 raw9041; decide +kernel
      have hl : raw9041step0Labels = raw9041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9041 raw9041Labels permutation434 hz
    mixedMoment B raw9041step0 raw9041step0Labels = mixedMoment B raw9041step1 raw9041step1Labels := by
      have ha : raw9041step1 = (fun i j => raw9041step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9041step1 raw9041step0; decide +kernel
      have hl : raw9041step1Labels = raw9041step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9041step0 raw9041step0Labels permutation32 permutation6
    mixedMoment B raw9041step1 raw9041step1Labels = mixedMoment B raw9041step2 raw9041step2Labels := by
      have ha : raw9041step2 = raw9041step1 := by apply Matrix.ext; unfold raw9041step2 raw9041step1; decide +kernel
      have hl : raw9041step1Labels = labelEmbedding9 ∘ raw9041step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9041step1 raw9041step1Labels raw9041step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw9042 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9042step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9042step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9042 raw9042Labels = mixedMoment B node5194 node5194Labels := by
  calc
    mixedMoment B raw9042 raw9042Labels = mixedMoment B raw9042step0 raw9042step0Labels := by
      have ha : raw9042step0 = (fun i j => raw9042 (permutation569 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9042step0 raw9042; decide +kernel
      have hl : raw9042step0Labels = raw9042Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9042 raw9042Labels permutation569 permutation3
    mixedMoment B raw9042step0 raw9042step0Labels = mixedMoment B raw9042step1 raw9042step1Labels := by
      have ha : raw9042step1 = raw9042step0 := by apply Matrix.ext; unfold raw9042step1 raw9042step0; decide +kernel
      have hl : raw9042step0Labels = labelEmbedding6 ∘ raw9042step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9042step0 raw9042step0Labels raw9042step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5194 node5194Labels := by rfl

def raw9043 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw9043step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9043step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9043step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9043step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9043 raw9043Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw9043 raw9043Labels = mixedMoment B raw9043step0 raw9043step0Labels := by
      have hz : ∀ j, raw9043 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9043step0 = (fun i j => raw9043 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9043step0 raw9043; decide +kernel
      have hl : raw9043step0Labels = raw9043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9043 raw9043Labels permutation265 hz
    mixedMoment B raw9043step0 raw9043step0Labels = mixedMoment B raw9043step1 raw9043step1Labels := by
      have ha : raw9043step1 = (fun i j => raw9043step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9043step1 raw9043step0; decide +kernel
      have hl : raw9043step1Labels = raw9043step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9043step0 raw9043step0Labels permutation47 permutation4
    mixedMoment B raw9043step1 raw9043step1Labels = mixedMoment B raw9043step2 raw9043step2Labels := by
      have ha : raw9043step2 = -raw9043step1 := by apply Matrix.ext; change ∀ i j, raw9043step2 i j = -(raw9043step1 i j); unfold raw9043step2 raw9043step1; decide +kernel
      have hl : raw9043step2Labels = raw9043step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9043step2 raw9043step2Labels = mixedMoment B raw9043step3 raw9043step3Labels := by
      have ha : raw9043step3 = raw9043step2 := by apply Matrix.ext; unfold raw9043step3 raw9043step2; decide +kernel
      have hl : raw9043step2Labels = labelEmbedding7 ∘ raw9043step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9043step2 raw9043step2Labels raw9043step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw9044 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9044step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9044step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9044step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9044step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9044step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9044 raw9044Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw9044 raw9044Labels = mixedMoment B raw9044step0 raw9044step0Labels := by
      have hz : ∀ j, raw9044 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9044step0 = (fun i j => raw9044 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9044step0 raw9044; decide +kernel
      have hl : raw9044step0Labels = raw9044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9044 raw9044Labels permutation434 hz
    mixedMoment B raw9044step0 raw9044step0Labels = mixedMoment B raw9044step1 raw9044step1Labels := by
      have hz : ∀ j, raw9044step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9044step1 = (fun i j => raw9044step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9044step1 raw9044step0; decide +kernel
      have hl : raw9044step1Labels = raw9044step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9044step0 raw9044step0Labels permutation56 hz
    mixedMoment B raw9044step1 raw9044step1Labels = mixedMoment B raw9044step2 raw9044step2Labels := by
      have ha : raw9044step2 = (fun i j => raw9044step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9044step2 raw9044step1; decide +kernel
      have hl : raw9044step2Labels = raw9044step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9044step1 raw9044step1Labels permutation8 permutation6
    mixedMoment B raw9044step2 raw9044step2Labels = mixedMoment B raw9044step3 raw9044step3Labels := by
      have ha : raw9044step3 = raw9044step2 := by apply Matrix.ext; unfold raw9044step3 raw9044step2; decide +kernel
      have hl : raw9044step2Labels = labelEmbedding9 ∘ raw9044step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9044step2 raw9044step2Labels raw9044step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw9045 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw9045step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw9045step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9045 raw9045Labels = mixedMoment B node5195 node5195Labels := by
  calc
    mixedMoment B raw9045 raw9045Labels = mixedMoment B raw9045step0 raw9045step0Labels := by
      have hz : ∀ j, raw9045 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9045step0 = (fun i j => raw9045 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9045step0 raw9045; decide +kernel
      have hl : raw9045step0Labels = raw9045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9045 raw9045Labels permutation265 hz
    mixedMoment B raw9045step0 raw9045step0Labels = mixedMoment B raw9045step1 raw9045step1Labels := by
      have ha : raw9045step1 = (fun i j => raw9045step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9045step1 raw9045step0; decide +kernel
      have hl : raw9045step1Labels = raw9045step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9045step0 raw9045step0Labels permutation123 permutation3
    mixedMoment B raw9045step1 raw9045step1Labels = mixedMoment B raw9045step2 raw9045step2Labels := by
      have ha : raw9045step2 = raw9045step1 := by apply Matrix.ext; unfold raw9045step2 raw9045step1; decide +kernel
      have hl : raw9045step1Labels = labelEmbedding6 ∘ raw9045step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9045step1 raw9045step1Labels raw9045step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5195 node5195Labels := by rfl

def raw9046 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw9046step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw9046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9046 raw9046Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw9046 raw9046Labels = mixedMoment B raw9046step0 raw9046step0Labels := by
      have hz : ∀ j, raw9046 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9046step0 = (fun i j => raw9046 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9046step0 raw9046; decide +kernel
      have hl : raw9046step0Labels = raw9046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9046 raw9046Labels permutation265 hz
    mixedMoment B raw9046step0 raw9046step0Labels = mixedMoment B raw9046step1 raw9046step1Labels := by
      have ha : raw9046step1 = (fun i j => raw9046step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9046step1 raw9046step0; decide +kernel
      have hl : raw9046step1Labels = raw9046step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9046step0 raw9046step0Labels permutation38 permutation6
    mixedMoment B raw9046step1 raw9046step1Labels = mixedMoment B raw9046step2 raw9046step2Labels := by
      have ha : raw9046step2 = raw9046step1 := by apply Matrix.ext; unfold raw9046step2 raw9046step1; decide +kernel
      have hl : raw9046step1Labels = labelEmbedding9 ∘ raw9046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9046step1 raw9046step1Labels raw9046step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw9047 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw9047step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9047step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9047step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9047step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9047 raw9047Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw9047 raw9047Labels = mixedMoment B raw9047step0 raw9047step0Labels := by
      have hz : ∀ j, raw9047 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9047step0 = (fun i j => raw9047 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9047step0 raw9047; decide +kernel
      have hl : raw9047step0Labels = raw9047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9047 raw9047Labels permutation265 hz
    mixedMoment B raw9047step0 raw9047step0Labels = mixedMoment B raw9047step1 raw9047step1Labels := by
      have ha : raw9047step1 = (fun i j => raw9047step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9047step1 raw9047step0; decide +kernel
      have hl : raw9047step1Labels = raw9047step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9047step0 raw9047step0Labels permutation44 permutation4
    mixedMoment B raw9047step1 raw9047step1Labels = mixedMoment B raw9047step2 raw9047step2Labels := by
      have ha : raw9047step2 = -raw9047step1 := by apply Matrix.ext; change ∀ i j, raw9047step2 i j = -(raw9047step1 i j); unfold raw9047step2 raw9047step1; decide +kernel
      have hl : raw9047step2Labels = raw9047step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9047step2 raw9047step2Labels = mixedMoment B raw9047step3 raw9047step3Labels := by
      have ha : raw9047step3 = raw9047step2 := by apply Matrix.ext; unfold raw9047step3 raw9047step2; decide +kernel
      have hl : raw9047step2Labels = labelEmbedding7 ∘ raw9047step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9047step2 raw9047step2Labels raw9047step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw9048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9048step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9048step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9048step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9048step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9048 raw9048Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw9048 raw9048Labels = mixedMoment B raw9048step0 raw9048step0Labels := by
      have hz : ∀ j, raw9048 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9048step0 = (fun i j => raw9048 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9048step0 raw9048; decide +kernel
      have hl : raw9048step0Labels = raw9048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9048 raw9048Labels permutation434 hz
    mixedMoment B raw9048step0 raw9048step0Labels = mixedMoment B raw9048step1 raw9048step1Labels := by
      have hz : ∀ j, raw9048step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9048step1 = (fun i j => raw9048step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9048step1 raw9048step0; decide +kernel
      have hl : raw9048step1Labels = raw9048step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9048step0 raw9048step0Labels permutation56 hz
    mixedMoment B raw9048step1 raw9048step1Labels = mixedMoment B raw9048step2 raw9048step2Labels := by
      have ha : raw9048step2 = (fun i j => raw9048step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9048step2 raw9048step1; decide +kernel
      have hl : raw9048step2Labels = raw9048step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9048step1 raw9048step1Labels permutation8 permutation6
    mixedMoment B raw9048step2 raw9048step2Labels = mixedMoment B raw9048step3 raw9048step3Labels := by
      have ha : raw9048step3 = raw9048step2 := by apply Matrix.ext; unfold raw9048step3 raw9048step2; decide +kernel
      have hl : raw9048step2Labels = labelEmbedding9 ∘ raw9048step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9048step2 raw9048step2Labels raw9048step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw9049 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9049step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9049step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9049 raw9049Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw9049 raw9049Labels = mixedMoment B raw9049step0 raw9049step0Labels := by
      have hz : ∀ j, raw9049 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9049step0 = (fun i j => raw9049 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9049step0 raw9049; decide +kernel
      have hl : raw9049step0Labels = raw9049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9049 raw9049Labels permutation265 hz
    mixedMoment B raw9049step0 raw9049step0Labels = mixedMoment B raw9049step1 raw9049step1Labels := by
      have ha : raw9049step1 = (fun i j => raw9049step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9049step1 raw9049step0; decide +kernel
      have hl : raw9049step1Labels = raw9049step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9049step0 raw9049step0Labels permutation32 permutation6
    mixedMoment B raw9049step1 raw9049step1Labels = mixedMoment B raw9049step2 raw9049step2Labels := by
      have ha : raw9049step2 = raw9049step1 := by apply Matrix.ext; unfold raw9049step2 raw9049step1; decide +kernel
      have hl : raw9049step1Labels = labelEmbedding9 ∘ raw9049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9049step1 raw9049step1Labels raw9049step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

def raw9050 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9050step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9050step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9050step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9050 raw9050Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw9050 raw9050Labels = mixedMoment B raw9050step0 raw9050step0Labels := by
      have hz : ∀ j, raw9050 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9050step0 = (fun i j => raw9050 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9050step0 raw9050; decide +kernel
      have hl : raw9050step0Labels = raw9050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9050 raw9050Labels permutation434 hz
    mixedMoment B raw9050step0 raw9050step0Labels = mixedMoment B raw9050step1 raw9050step1Labels := by
      have hz : ∀ j, raw9050step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9050step1 = (fun i j => raw9050step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9050step1 raw9050step0; decide +kernel
      have hl : raw9050step1Labels = raw9050step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9050step0 raw9050step0Labels permutation56 hz
    mixedMoment B raw9050step1 raw9050step1Labels = mixedMoment B raw9050step2 raw9050step2Labels := by
      have ha : raw9050step2 = (fun i j => raw9050step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9050step2 raw9050step1; decide +kernel
      have hl : raw9050step2Labels = raw9050step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9050step1 raw9050step1Labels permutation8 permutation6
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw9051 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9051step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9051 raw9051Labels = mixedMoment B node2641 node2641Labels := by
  calc
    mixedMoment B raw9051 raw9051Labels = mixedMoment B raw9051step0 raw9051step0Labels := by
      have hz : ∀ j, raw9051 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9051step0 = (fun i j => raw9051 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9051step0 raw9051; decide +kernel
      have hl : raw9051step0Labels = raw9051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9051 raw9051Labels permutation265 hz
    mixedMoment B raw9051step0 raw9051step0Labels = mixedMoment B raw9051step1 raw9051step1Labels := by
      have ha : raw9051step1 = (fun i j => raw9051step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9051step1 raw9051step0; decide +kernel
      have hl : raw9051step1Labels = raw9051step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9051step0 raw9051step0Labels permutation125 permutation3
    _ = mixedMoment B node2641 node2641Labels := by rfl

def raw9052 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw9052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9052 raw9052Labels = mixedMoment B node3106 node3106Labels := by
  calc
    mixedMoment B raw9052 raw9052Labels = mixedMoment B raw9052step0 raw9052step0Labels := by
      have hz : ∀ j, raw9052 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9052step0 = (fun i j => raw9052 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9052step0 raw9052; decide +kernel
      have hl : raw9052step0Labels = raw9052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9052 raw9052Labels permutation265 hz
    mixedMoment B raw9052step0 raw9052step0Labels = mixedMoment B raw9052step1 raw9052step1Labels := by
      have ha : raw9052step1 = (fun i j => raw9052step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9052step1 raw9052step0; decide +kernel
      have hl : raw9052step1Labels = raw9052step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9052step0 raw9052step0Labels permutation32 permutation6
    _ = mixedMoment B node3106 node3106Labels := by rfl

def raw9053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9053step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9053 raw9053Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw9053 raw9053Labels = mixedMoment B raw9053step0 raw9053step0Labels := by
      have hz : ∀ j, raw9053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9053step0 = (fun i j => raw9053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9053step0 raw9053; decide +kernel
      have hl : raw9053step0Labels = raw9053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9053 raw9053Labels permutation434 hz
    mixedMoment B raw9053step0 raw9053step0Labels = mixedMoment B raw9053step1 raw9053step1Labels := by
      have ha : raw9053step1 = (fun i j => raw9053step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9053step1 raw9053step0; decide +kernel
      have hl : raw9053step1Labels = raw9053step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9053step0 raw9053step0Labels permutation32 permutation6
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw9054 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9054 raw9054Labels = mixedMoment B node2628 node2628Labels := by
  calc
    mixedMoment B raw9054 raw9054Labels = mixedMoment B raw9054step0 raw9054step0Labels := by
      have ha : raw9054step0 = (fun i j => raw9054 (permutation569 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9054step0 raw9054; decide +kernel
      have hl : raw9054step0Labels = raw9054Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9054 raw9054Labels permutation569 permutation3
    _ = mixedMoment B node2628 node2628Labels := by rfl

def raw9055 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9055 raw9055Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw9055 raw9055Labels = mixedMoment B raw9055step0 raw9055step0Labels := by
      have hz : ∀ j, raw9055 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9055step0 = (fun i j => raw9055 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9055step0 raw9055; decide +kernel
      have hl : raw9055step0Labels = raw9055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9055 raw9055Labels permutation265 hz
    mixedMoment B raw9055step0 raw9055step0Labels = mixedMoment B raw9055step1 raw9055step1Labels := by
      have ha : raw9055step1 = (fun i j => raw9055step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9055step1 raw9055step0; decide +kernel
      have hl : raw9055step1Labels = raw9055step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9055step0 raw9055step0Labels permutation38 permutation6
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw9056 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9056step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9056 raw9056Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw9056 raw9056Labels = mixedMoment B raw9056step0 raw9056step0Labels := by
      have hz : ∀ j, raw9056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9056step0 = (fun i j => raw9056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9056step0 raw9056; decide +kernel
      have hl : raw9056step0Labels = raw9056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9056 raw9056Labels permutation434 hz
    mixedMoment B raw9056step0 raw9056step0Labels = mixedMoment B raw9056step1 raw9056step1Labels := by
      have hz : ∀ j, raw9056step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9056step1 = (fun i j => raw9056step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9056step1 raw9056step0; decide +kernel
      have hl : raw9056step1Labels = raw9056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9056step0 raw9056step0Labels permutation56 hz
    mixedMoment B raw9056step1 raw9056step1Labels = mixedMoment B raw9056step2 raw9056step2Labels := by
      have ha : raw9056step2 = (fun i j => raw9056step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9056step2 raw9056step1; decide +kernel
      have hl : raw9056step2Labels = raw9056step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9056step1 raw9056step1Labels permutation8 permutation6
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw9057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw9057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9057 raw9057Labels = mixedMoment B node2629 node2629Labels := by
  calc
    mixedMoment B raw9057 raw9057Labels = mixedMoment B raw9057step0 raw9057step0Labels := by
      have hz : ∀ j, raw9057 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9057step0 = (fun i j => raw9057 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9057step0 raw9057; decide +kernel
      have hl : raw9057step0Labels = raw9057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9057 raw9057Labels permutation265 hz
    mixedMoment B raw9057step0 raw9057step0Labels = mixedMoment B raw9057step1 raw9057step1Labels := by
      have ha : raw9057step1 = (fun i j => raw9057step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9057step1 raw9057step0; decide +kernel
      have hl : raw9057step1Labels = raw9057step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9057step0 raw9057step0Labels permutation123 permutation3
    _ = mixedMoment B node2629 node2629Labels := by rfl

def raw9058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw9058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9058 raw9058Labels = mixedMoment B node2758 node2758Labels := by
  calc
    mixedMoment B raw9058 raw9058Labels = mixedMoment B raw9058step0 raw9058step0Labels := by
      have hz : ∀ j, raw9058 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9058step0 = (fun i j => raw9058 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9058step0 raw9058; decide +kernel
      have hl : raw9058step0Labels = raw9058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9058 raw9058Labels permutation265 hz
    mixedMoment B raw9058step0 raw9058step0Labels = mixedMoment B raw9058step1 raw9058step1Labels := by
      have ha : raw9058step1 = (fun i j => raw9058step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9058step1 raw9058step0; decide +kernel
      have hl : raw9058step1Labels = raw9058step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9058step0 raw9058step0Labels permutation38 permutation6
    _ = mixedMoment B node2758 node2758Labels := by rfl

def raw9059 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9059 raw9059Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw9059 raw9059Labels = mixedMoment B raw9059step0 raw9059step0Labels := by
      have hz : ∀ j, raw9059 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9059step0 = (fun i j => raw9059 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9059step0 raw9059; decide +kernel
      have hl : raw9059step0Labels = raw9059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9059 raw9059Labels permutation265 hz
    mixedMoment B raw9059step0 raw9059step0Labels = mixedMoment B raw9059step1 raw9059step1Labels := by
      have ha : raw9059step1 = (fun i j => raw9059step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9059step1 raw9059step0; decide +kernel
      have hl : raw9059step1Labels = raw9059step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9059step0 raw9059step0Labels permutation32 permutation6
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw9060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9060step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9060step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9060step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9060 raw9060Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw9060 raw9060Labels = mixedMoment B raw9060step0 raw9060step0Labels := by
      have hz : ∀ j, raw9060 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9060step0 = (fun i j => raw9060 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9060step0 raw9060; decide +kernel
      have hl : raw9060step0Labels = raw9060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9060 raw9060Labels permutation434 hz
    mixedMoment B raw9060step0 raw9060step0Labels = mixedMoment B raw9060step1 raw9060step1Labels := by
      have hz : ∀ j, raw9060step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9060step1 = (fun i j => raw9060step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9060step1 raw9060step0; decide +kernel
      have hl : raw9060step1Labels = raw9060step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9060step0 raw9060step0Labels permutation56 hz
    mixedMoment B raw9060step1 raw9060step1Labels = mixedMoment B raw9060step2 raw9060step2Labels := by
      have ha : raw9060step2 = (fun i j => raw9060step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9060step2 raw9060step1; decide +kernel
      have hl : raw9060step2Labels = raw9060step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9060step1 raw9060step1Labels permutation8 permutation6
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw9061 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9061 raw9061Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw9061 raw9061Labels = mixedMoment B raw9061step0 raw9061step0Labels := by
      have hz : ∀ j, raw9061 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9061step0 = (fun i j => raw9061 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9061step0 raw9061; decide +kernel
      have hl : raw9061step0Labels = raw9061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9061 raw9061Labels permutation265 hz
    mixedMoment B raw9061step0 raw9061step0Labels = mixedMoment B raw9061step1 raw9061step1Labels := by
      have ha : raw9061step1 = (fun i j => raw9061step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9061step1 raw9061step0; decide +kernel
      have hl : raw9061step1Labels = raw9061step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9061step0 raw9061step0Labels permutation32 permutation6
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw9062 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9062Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9062step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9062step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9062step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9062step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9062step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9062step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9062step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9062 raw9062Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw9062 raw9062Labels = mixedMoment B raw9062step0 raw9062step0Labels := by
      have hz : ∀ j, raw9062 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9062step0 = (fun i j => raw9062 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9062step0 raw9062; decide +kernel
      have hl : raw9062step0Labels = raw9062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9062 raw9062Labels permutation434 hz
    mixedMoment B raw9062step0 raw9062step0Labels = mixedMoment B raw9062step1 raw9062step1Labels := by
      have hz : ∀ j, raw9062step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9062step1 = (fun i j => raw9062step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9062step1 raw9062step0; decide +kernel
      have hl : raw9062step1Labels = raw9062step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9062step0 raw9062step0Labels permutation56 hz
    mixedMoment B raw9062step1 raw9062step1Labels = mixedMoment B raw9062step2 raw9062step2Labels := by
      have ha : raw9062step2 = (fun i j => raw9062step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9062step2 raw9062step1; decide +kernel
      have hl : raw9062step2Labels = raw9062step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9062step1 raw9062step1Labels permutation8 permutation7
    mixedMoment B raw9062step2 raw9062step2Labels = mixedMoment B raw9062step3 raw9062step3Labels := by
      have ha : raw9062step3 = raw9062step2 := by apply Matrix.ext; unfold raw9062step3 raw9062step2; decide +kernel
      have hl : raw9062step2Labels = labelEmbedding1 ∘ raw9062step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9062step2 raw9062step2Labels raw9062step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw9063 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9063Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9063step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9063step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9063 raw9063Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw9063 raw9063Labels = mixedMoment B raw9063step0 raw9063step0Labels := by
      have hz : ∀ j, raw9063 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9063step0 = (fun i j => raw9063 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9063step0 raw9063; decide +kernel
      have hl : raw9063step0Labels = raw9063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9063 raw9063Labels permutation265 hz
    mixedMoment B raw9063step0 raw9063step0Labels = mixedMoment B raw9063step1 raw9063step1Labels := by
      have ha : raw9063step1 = (fun i j => raw9063step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9063step1 raw9063step0; decide +kernel
      have hl : raw9063step1Labels = raw9063step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9063step0 raw9063step0Labels permutation32 permutation7
    mixedMoment B raw9063step1 raw9063step1Labels = mixedMoment B raw9063step2 raw9063step2Labels := by
      have ha : raw9063step2 = raw9063step1 := by apply Matrix.ext; unfold raw9063step2 raw9063step1; decide +kernel
      have hl : raw9063step1Labels = labelEmbedding1 ∘ raw9063step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9063step1 raw9063step1Labels raw9063step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw9064 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9064Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9064step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9064step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9064 raw9064Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw9064 raw9064Labels = mixedMoment B raw9064step0 raw9064step0Labels := by
      have hz : ∀ j, raw9064 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9064step0 = (fun i j => raw9064 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9064step0 raw9064; decide +kernel
      have hl : raw9064step0Labels = raw9064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9064 raw9064Labels permutation265 hz
    mixedMoment B raw9064step0 raw9064step0Labels = mixedMoment B raw9064step1 raw9064step1Labels := by
      have ha : raw9064step1 = (fun i j => raw9064step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9064step1 raw9064step0; decide +kernel
      have hl : raw9064step1Labels = raw9064step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9064step0 raw9064step0Labels permutation32 permutation7
    mixedMoment B raw9064step1 raw9064step1Labels = mixedMoment B raw9064step2 raw9064step2Labels := by
      have ha : raw9064step2 = raw9064step1 := by apply Matrix.ext; unfold raw9064step2 raw9064step1; decide +kernel
      have hl : raw9064step1Labels = labelEmbedding1 ∘ raw9064step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9064step1 raw9064step1Labels raw9064step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw9065 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9065Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9065step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9065step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9065step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9065step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9065 raw9065Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw9065 raw9065Labels = mixedMoment B raw9065step0 raw9065step0Labels := by
      have hz : ∀ j, raw9065 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9065step0 = (fun i j => raw9065 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9065step0 raw9065; decide +kernel
      have hl : raw9065step0Labels = raw9065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9065 raw9065Labels permutation434 hz
    mixedMoment B raw9065step0 raw9065step0Labels = mixedMoment B raw9065step1 raw9065step1Labels := by
      have ha : raw9065step1 = (fun i j => raw9065step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9065step1 raw9065step0; decide +kernel
      have hl : raw9065step1Labels = raw9065step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9065step0 raw9065step0Labels permutation32 permutation7
    mixedMoment B raw9065step1 raw9065step1Labels = mixedMoment B raw9065step2 raw9065step2Labels := by
      have ha : raw9065step2 = raw9065step1 := by apply Matrix.ext; unfold raw9065step2 raw9065step1; decide +kernel
      have hl : raw9065step1Labels = labelEmbedding1 ∘ raw9065step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9065step1 raw9065step1Labels raw9065step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw9066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9066Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9066step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9066 raw9066Labels = mixedMoment B node3060 node3060Labels := by
  calc
    mixedMoment B raw9066 raw9066Labels = mixedMoment B raw9066step0 raw9066step0Labels := by
      have ha : raw9066step0 = (fun i j => raw9066 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9066step0 raw9066; decide +kernel
      have hl : raw9066step0Labels = raw9066Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9066 raw9066Labels permutation152 permutation7
    mixedMoment B raw9066step0 raw9066step0Labels = mixedMoment B raw9066step1 raw9066step1Labels := by
      have ha : raw9066step1 = raw9066step0 := by apply Matrix.ext; unfold raw9066step1 raw9066step0; decide +kernel
      have hl : raw9066step0Labels = labelEmbedding1 ∘ raw9066step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9066step0 raw9066step0Labels raw9066step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3060 node3060Labels := by rfl

def raw9067 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9067Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9067step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw9067step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9067step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9067step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9067step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9067 raw9067Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw9067 raw9067Labels = mixedMoment B raw9067step0 raw9067step0Labels := by
      have hz : ∀ j, raw9067 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9067step0 = (fun i j => raw9067 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9067step0 raw9067; decide +kernel
      have hl : raw9067step0Labels = raw9067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9067 raw9067Labels permutation265 hz
    mixedMoment B raw9067step0 raw9067step0Labels = mixedMoment B raw9067step1 raw9067step1Labels := by
      have ha : raw9067step1 = (fun i j => raw9067step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9067step1 raw9067step0; decide +kernel
      have hl : raw9067step1Labels = raw9067step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9067step0 raw9067step0Labels permutation49 permutation5
    mixedMoment B raw9067step1 raw9067step1Labels = mixedMoment B raw9067step2 raw9067step2Labels := by
      have ha : raw9067step2 = -raw9067step1 := by apply Matrix.ext; change ∀ i j, raw9067step2 i j = -(raw9067step1 i j); unfold raw9067step2 raw9067step1; decide +kernel
      have hl : raw9067step2Labels = raw9067step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9067step2 raw9067step2Labels = mixedMoment B raw9067step3 raw9067step3Labels := by
      have ha : raw9067step3 = raw9067step2 := by apply Matrix.ext; unfold raw9067step3 raw9067step2; decide +kernel
      have hl : raw9067step2Labels = labelEmbedding1 ∘ raw9067step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9067step2 raw9067step2Labels raw9067step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw9068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9068Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9068step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9068step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw9068step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9068step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw9068step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9068 raw9068Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw9068 raw9068Labels = mixedMoment B raw9068step0 raw9068step0Labels := by
      have hz : ∀ j, raw9068 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9068step0 = (fun i j => raw9068 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9068step0 raw9068; decide +kernel
      have hl : raw9068step0Labels = raw9068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9068 raw9068Labels permutation434 hz
    mixedMoment B raw9068step0 raw9068step0Labels = mixedMoment B raw9068step1 raw9068step1Labels := by
      have hz : ∀ j, raw9068step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9068step1 = (fun i j => raw9068step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9068step1 raw9068step0; decide +kernel
      have hl : raw9068step1Labels = raw9068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9068step0 raw9068step0Labels permutation56 hz
    mixedMoment B raw9068step1 raw9068step1Labels = mixedMoment B raw9068step2 raw9068step2Labels := by
      have ha : raw9068step2 = (fun i j => raw9068step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9068step2 raw9068step1; decide +kernel
      have hl : raw9068step2Labels = raw9068step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9068step1 raw9068step1Labels permutation8 permutation7
    mixedMoment B raw9068step2 raw9068step2Labels = mixedMoment B raw9068step3 raw9068step3Labels := by
      have ha : raw9068step3 = raw9068step2 := by apply Matrix.ext; unfold raw9068step3 raw9068step2; decide +kernel
      have hl : raw9068step2Labels = labelEmbedding1 ∘ raw9068step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9068step2 raw9068step2Labels raw9068step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw9069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9069Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9069step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9069step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9069step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9069 raw9069Labels = mixedMoment B node3026 node3026Labels := by
  calc
    mixedMoment B raw9069 raw9069Labels = mixedMoment B raw9069step0 raw9069step0Labels := by
      have hz : ∀ j, raw9069 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9069step0 = (fun i j => raw9069 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9069step0 raw9069; decide +kernel
      have hl : raw9069step0Labels = raw9069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9069 raw9069Labels permutation265 hz
    mixedMoment B raw9069step0 raw9069step0Labels = mixedMoment B raw9069step1 raw9069step1Labels := by
      have ha : raw9069step1 = (fun i j => raw9069step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9069step1 raw9069step0; decide +kernel
      have hl : raw9069step1Labels = raw9069step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9069step0 raw9069step0Labels permutation32 permutation7
    mixedMoment B raw9069step1 raw9069step1Labels = mixedMoment B raw9069step2 raw9069step2Labels := by
      have ha : raw9069step2 = raw9069step1 := by apply Matrix.ext; unfold raw9069step2 raw9069step1; decide +kernel
      have hl : raw9069step1Labels = labelEmbedding1 ∘ raw9069step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9069step1 raw9069step1Labels raw9069step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3026 node3026Labels := by rfl

def raw9070 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9070step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9070 raw9070Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw9070 raw9070Labels = mixedMoment B raw9070step0 raw9070step0Labels := by
      have hz : ∀ j, raw9070 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9070step0 = (fun i j => raw9070 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9070step0 raw9070; decide +kernel
      have hl : raw9070step0Labels = raw9070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9070 raw9070Labels permutation265 hz
    mixedMoment B raw9070step0 raw9070step0Labels = mixedMoment B raw9070step1 raw9070step1Labels := by
      have ha : raw9070step1 = (fun i j => raw9070step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9070step1 raw9070step0; decide +kernel
      have hl : raw9070step1Labels = raw9070step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9070step0 raw9070step0Labels permutation32 permutation7
    mixedMoment B raw9070step1 raw9070step1Labels = mixedMoment B raw9070step2 raw9070step2Labels := by
      have ha : raw9070step2 = raw9070step1 := by apply Matrix.ext; unfold raw9070step2 raw9070step1; decide +kernel
      have hl : raw9070step1Labels = labelEmbedding1 ∘ raw9070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9070step1 raw9070step1Labels raw9070step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw9071 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9071step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9071step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9071step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9071step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9071 raw9071Labels = mixedMoment B node3185 node3185Labels := by
  calc
    mixedMoment B raw9071 raw9071Labels = mixedMoment B raw9071step0 raw9071step0Labels := by
      have hz : ∀ j, raw9071 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9071step0 = (fun i j => raw9071 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9071step0 raw9071; decide +kernel
      have hl : raw9071step0Labels = raw9071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9071 raw9071Labels permutation265 hz
    mixedMoment B raw9071step0 raw9071step0Labels = mixedMoment B raw9071step1 raw9071step1Labels := by
      have ha : raw9071step1 = (fun i j => raw9071step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9071step1 raw9071step0; decide +kernel
      have hl : raw9071step1Labels = raw9071step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9071step0 raw9071step0Labels permutation44 permutation5
    mixedMoment B raw9071step1 raw9071step1Labels = mixedMoment B raw9071step2 raw9071step2Labels := by
      have ha : raw9071step2 = -raw9071step1 := by apply Matrix.ext; change ∀ i j, raw9071step2 i j = -(raw9071step1 i j); unfold raw9071step2 raw9071step1; decide +kernel
      have hl : raw9071step2Labels = raw9071step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9071step2 raw9071step2Labels = mixedMoment B raw9071step3 raw9071step3Labels := by
      have ha : raw9071step3 = raw9071step2 := by apply Matrix.ext; unfold raw9071step3 raw9071step2; decide +kernel
      have hl : raw9071step2Labels = labelEmbedding1 ∘ raw9071step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9071step2 raw9071step2Labels raw9071step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3185 node3185Labels := by rfl

def raw9072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9072step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9072step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9072step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9072 raw9072Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw9072 raw9072Labels = mixedMoment B raw9072step0 raw9072step0Labels := by
      have hz : ∀ j, raw9072 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9072step0 = (fun i j => raw9072 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9072step0 raw9072; decide +kernel
      have hl : raw9072step0Labels = raw9072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9072 raw9072Labels permutation434 hz
    mixedMoment B raw9072step0 raw9072step0Labels = mixedMoment B raw9072step1 raw9072step1Labels := by
      have hz : ∀ j, raw9072step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9072step1 = (fun i j => raw9072step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9072step1 raw9072step0; decide +kernel
      have hl : raw9072step1Labels = raw9072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9072step0 raw9072step0Labels permutation56 hz
    mixedMoment B raw9072step1 raw9072step1Labels = mixedMoment B raw9072step2 raw9072step2Labels := by
      have ha : raw9072step2 = (fun i j => raw9072step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9072step2 raw9072step1; decide +kernel
      have hl : raw9072step2Labels = raw9072step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9072step1 raw9072step1Labels permutation8 permutation7
    mixedMoment B raw9072step2 raw9072step2Labels = mixedMoment B raw9072step3 raw9072step3Labels := by
      have ha : raw9072step3 = raw9072step2 := by apply Matrix.ext; unfold raw9072step3 raw9072step2; decide +kernel
      have hl : raw9072step2Labels = labelEmbedding1 ∘ raw9072step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9072step2 raw9072step2Labels raw9072step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw9073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9073step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9073 raw9073Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw9073 raw9073Labels = mixedMoment B raw9073step0 raw9073step0Labels := by
      have hz : ∀ j, raw9073 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9073step0 = (fun i j => raw9073 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9073step0 raw9073; decide +kernel
      have hl : raw9073step0Labels = raw9073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9073 raw9073Labels permutation265 hz
    mixedMoment B raw9073step0 raw9073step0Labels = mixedMoment B raw9073step1 raw9073step1Labels := by
      have ha : raw9073step1 = (fun i j => raw9073step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9073step1 raw9073step0; decide +kernel
      have hl : raw9073step1Labels = raw9073step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9073step0 raw9073step0Labels permutation32 permutation7
    mixedMoment B raw9073step1 raw9073step1Labels = mixedMoment B raw9073step2 raw9073step2Labels := by
      have ha : raw9073step2 = raw9073step1 := by apply Matrix.ext; unfold raw9073step2 raw9073step1; decide +kernel
      have hl : raw9073step1Labels = labelEmbedding1 ∘ raw9073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9073step1 raw9073step1Labels raw9073step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3079 node3079Labels := by rfl

def raw9074 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw9074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9074step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9074step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9074 raw9074Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw9074 raw9074Labels = mixedMoment B raw9074step0 raw9074step0Labels := by
      have hz : ∀ j, raw9074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9074step0 = (fun i j => raw9074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9074step0 raw9074; decide +kernel
      have hl : raw9074step0Labels = raw9074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9074 raw9074Labels permutation434 hz
    mixedMoment B raw9074step0 raw9074step0Labels = mixedMoment B raw9074step1 raw9074step1Labels := by
      have hz : ∀ j, raw9074step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9074step1 = (fun i j => raw9074step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9074step1 raw9074step0; decide +kernel
      have hl : raw9074step1Labels = raw9074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9074step0 raw9074step0Labels permutation56 hz
    mixedMoment B raw9074step1 raw9074step1Labels = mixedMoment B raw9074step2 raw9074step2Labels := by
      have ha : raw9074step2 = (fun i j => raw9074step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9074step2 raw9074step1; decide +kernel
      have hl : raw9074step2Labels = raw9074step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9074step1 raw9074step1Labels permutation9 permutation2
    mixedMoment B raw9074step2 raw9074step2Labels = mixedMoment B raw9074step3 raw9074step3Labels := by
      have ha : raw9074step3 = -raw9074step2 := by apply Matrix.ext; change ∀ i j, raw9074step3 i j = -(raw9074step2 i j); unfold raw9074step3 raw9074step2; decide +kernel
      have hl : raw9074step3Labels = raw9074step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw9075 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9075 raw9075Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw9075 raw9075Labels = mixedMoment B raw9075step0 raw9075step0Labels := by
      have hz : ∀ j, raw9075 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9075step0 = (fun i j => raw9075 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9075step0 raw9075; decide +kernel
      have hl : raw9075step0Labels = raw9075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9075 raw9075Labels permutation265 hz
    mixedMoment B raw9075step0 raw9075step0Labels = mixedMoment B raw9075step1 raw9075step1Labels := by
      have ha : raw9075step1 = (fun i j => raw9075step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9075step1 raw9075step0; decide +kernel
      have hl : raw9075step1Labels = raw9075step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9075step0 raw9075step0Labels permutation125 permutation2
    _ = mixedMoment B node2879 node2879Labels := by rfl

def raw9076 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw9076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9076 raw9076Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw9076 raw9076Labels = mixedMoment B raw9076step0 raw9076step0Labels := by
      have hz : ∀ j, raw9076 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9076step0 = (fun i j => raw9076 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9076step0 raw9076; decide +kernel
      have hl : raw9076step0Labels = raw9076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9076 raw9076Labels permutation265 hz
    mixedMoment B raw9076step0 raw9076step0Labels = mixedMoment B raw9076step1 raw9076step1Labels := by
      have ha : raw9076step1 = -raw9076step0 := by apply Matrix.ext; change ∀ i j, raw9076step1 i j = -(raw9076step0 i j); unfold raw9076step1 raw9076step0; decide +kernel
      have hl : raw9076step1Labels = raw9076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3498 node3498Labels := by rfl

def raw9077 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw9077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9077step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9077 raw9077Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw9077 raw9077Labels = mixedMoment B raw9077step0 raw9077step0Labels := by
      have hz : ∀ j, raw9077 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9077step0 = (fun i j => raw9077 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9077step0 raw9077; decide +kernel
      have hl : raw9077step0Labels = raw9077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9077 raw9077Labels permutation265 hz
    mixedMoment B raw9077step0 raw9077step0Labels = mixedMoment B raw9077step1 raw9077step1Labels := by
      have ha : raw9077step1 = (fun i j => raw9077step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9077step1 raw9077step0; decide +kernel
      have hl : raw9077step1Labels = raw9077step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9077step0 raw9077step0Labels permutation47 permutation4
    mixedMoment B raw9077step1 raw9077step1Labels = mixedMoment B raw9077step2 raw9077step2Labels := by
      have ha : raw9077step2 = -raw9077step1 := by apply Matrix.ext; change ∀ i j, raw9077step2 i j = -(raw9077step1 i j); unfold raw9077step2 raw9077step1; decide +kernel
      have hl : raw9077step2Labels = raw9077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2108 node2108Labels := by rfl

def raw9078 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw9078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9078 raw9078Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw9078 raw9078Labels = mixedMoment B raw9078step0 raw9078step0Labels := by
      have hz : ∀ j, raw9078 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9078step0 = (fun i j => raw9078 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9078step0 raw9078; decide +kernel
      have hl : raw9078step0Labels = raw9078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9078 raw9078Labels permutation265 hz
    mixedMoment B raw9078step0 raw9078step0Labels = mixedMoment B raw9078step1 raw9078step1Labels := by
      have ha : raw9078step1 = (fun i j => raw9078step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9078step1 raw9078step0; decide +kernel
      have hl : raw9078step1Labels = raw9078step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9078step0 raw9078step0Labels permutation44 permutation4
    mixedMoment B raw9078step1 raw9078step1Labels = mixedMoment B raw9078step2 raw9078step2Labels := by
      have ha : raw9078step2 = -raw9078step1 := by apply Matrix.ext; change ∀ i j, raw9078step2 i j = -(raw9078step1 i j); unfold raw9078step2 raw9078step1; decide +kernel
      have hl : raw9078step2Labels = raw9078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2106 node2106Labels := by rfl

def raw9079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9079 raw9079Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw9079 raw9079Labels = mixedMoment B raw9079step0 raw9079step0Labels := by
      have hz : ∀ j, raw9079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9079step0 = (fun i j => raw9079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9079step0 raw9079; decide +kernel
      have hl : raw9079step0Labels = raw9079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9079 raw9079Labels permutation434 hz
    mixedMoment B raw9079step0 raw9079step0Labels = mixedMoment B raw9079step1 raw9079step1Labels := by
      have ha : raw9079step1 = (fun i j => raw9079step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9079step1 raw9079step0; decide +kernel
      have hl : raw9079step1Labels = raw9079step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9079step0 raw9079step0Labels permutation44 permutation4
    mixedMoment B raw9079step1 raw9079step1Labels = mixedMoment B raw9079step2 raw9079step2Labels := by
      have ha : raw9079step2 = -raw9079step1 := by apply Matrix.ext; change ∀ i j, raw9079step2 i j = -(raw9079step1 i j); unfold raw9079step2 raw9079step1; decide +kernel
      have hl : raw9079step2Labels = raw9079step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw9080 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9080 raw9080Labels = mixedMoment B node2877 node2877Labels := by
  calc
    mixedMoment B raw9080 raw9080Labels = mixedMoment B raw9080step0 raw9080step0Labels := by
      have ha : raw9080step0 = (fun i j => raw9080 (permutation577 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9080step0 raw9080; decide +kernel
      have hl : raw9080step0Labels = raw9080Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9080 raw9080Labels permutation577 permutation2
    _ = mixedMoment B node2877 node2877Labels := by rfl

def raw9081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw9081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9081 raw9081Labels = mixedMoment B node2883 node2883Labels := by
  calc
    mixedMoment B raw9081 raw9081Labels = mixedMoment B raw9081step0 raw9081step0Labels := by
      have hz : ∀ j, raw9081 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9081step0 = (fun i j => raw9081 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9081step0 raw9081; decide +kernel
      have hl : raw9081step0Labels = raw9081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9081 raw9081Labels permutation265 hz
    mixedMoment B raw9081step0 raw9081step0Labels = mixedMoment B raw9081step1 raw9081step1Labels := by
      have ha : raw9081step1 = (fun i j => raw9081step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9081step1 raw9081step0; decide +kernel
      have hl : raw9081step1Labels = raw9081step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9081step0 raw9081step0Labels permutation126 permutation2
    _ = mixedMoment B node2883 node2883Labels := by rfl

def raw9082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9082 raw9082Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw9082 raw9082Labels = mixedMoment B raw9082step0 raw9082step0Labels := by
      have hz : ∀ j, raw9082 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9082step0 = (fun i j => raw9082 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9082step0 raw9082; decide +kernel
      have hl : raw9082step0Labels = raw9082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9082 raw9082Labels permutation265 hz
    mixedMoment B raw9082step0 raw9082step0Labels = mixedMoment B raw9082step1 raw9082step1Labels := by
      have ha : raw9082step1 = (fun i j => raw9082step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9082step1 raw9082step0; decide +kernel
      have hl : raw9082step1Labels = raw9082step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9082step0 raw9082step0Labels permutation125 permutation2
    _ = mixedMoment B node3050 node3050Labels := by rfl

def raw9083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9083step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9083step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9083 raw9083Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw9083 raw9083Labels = mixedMoment B raw9083step0 raw9083step0Labels := by
      have hz : ∀ j, raw9083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9083step0 = (fun i j => raw9083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9083step0 raw9083; decide +kernel
      have hl : raw9083step0Labels = raw9083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9083 raw9083Labels permutation434 hz
    mixedMoment B raw9083step0 raw9083step0Labels = mixedMoment B raw9083step1 raw9083step1Labels := by
      have hz : ∀ j, raw9083step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9083step1 = (fun i j => raw9083step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9083step1 raw9083step0; decide +kernel
      have hl : raw9083step1Labels = raw9083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9083step0 raw9083step0Labels permutation56 hz
    mixedMoment B raw9083step1 raw9083step1Labels = mixedMoment B raw9083step2 raw9083step2Labels := by
      have ha : raw9083step2 = (fun i j => raw9083step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9083step2 raw9083step1; decide +kernel
      have hl : raw9083step2Labels = raw9083step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9083step1 raw9083step1Labels permutation10 permutation4
    mixedMoment B raw9083step2 raw9083step2Labels = mixedMoment B raw9083step3 raw9083step3Labels := by
      have ha : raw9083step3 = -raw9083step2 := by apply Matrix.ext; change ∀ i j, raw9083step3 i j = -(raw9083step2 i j); unfold raw9083step3 raw9083step2; decide +kernel
      have hl : raw9083step3Labels = raw9083step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw9084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw9084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw9084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9084 raw9084Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw9084 raw9084Labels = mixedMoment B raw9084step0 raw9084step0Labels := by
      have hz : ∀ j, raw9084 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9084step0 = (fun i j => raw9084 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9084step0 raw9084; decide +kernel
      have hl : raw9084step0Labels = raw9084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9084 raw9084Labels permutation265 hz
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw9085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9085step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9085 raw9085Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw9085 raw9085Labels = mixedMoment B raw9085step0 raw9085step0Labels := by
      have ha : raw9085step0 = (fun i j => raw9085 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9085step0 raw9085; decide +kernel
      have hl : raw9085step0Labels = raw9085Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9085 raw9085Labels permutation182 permutation3
    mixedMoment B raw9085step0 raw9085step0Labels = mixedMoment B raw9085step1 raw9085step1Labels := by
      have ha : raw9085step1 = raw9085step0 := by apply Matrix.ext; unfold raw9085step1 raw9085step0; decide +kernel
      have hl : raw9085step0Labels = labelEmbedding6 ∘ raw9085step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9085step0 raw9085step0Labels raw9085step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

def raw9086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw9086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9086 raw9086Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw9086 raw9086Labels = mixedMoment B raw9086step0 raw9086step0Labels := by
      have ha : raw9086step0 = (fun i j => raw9086 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9086step0 raw9086; decide +kernel
      have hl : raw9086step0Labels = raw9086Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9086 raw9086Labels permutation182 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw9087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw9087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9087 raw9087Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw9087 raw9087Labels = mixedMoment B raw9087step0 raw9087step0Labels := by
      have ha : raw9087step0 = (fun i j => raw9087 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9087step0 raw9087; decide +kernel
      have hl : raw9087step0Labels = raw9087Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9087 raw9087Labels permutation206 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
