import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40960 raw40960Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw40960 raw40960Labels = mixedMoment B raw40960step0 raw40960step0Labels := by
      have hz : ∀ j, raw40960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40960step0 = (fun i j => raw40960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40960step0 raw40960; decide +kernel
      have hl : raw40960step0Labels = raw40960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40960 raw40960Labels permutation346 hz
    mixedMoment B raw40960step0 raw40960step0Labels = mixedMoment B raw40960step1 raw40960step1Labels := by
      have ha : raw40960step1 = (fun i j => raw40960step0 (permutation136 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40960step1 raw40960step0; decide +kernel
      have hl : raw40960step1Labels = raw40960step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40960step0 raw40960step0Labels permutation136 permutation6
    _ = mixedMoment B node2817 node2817Labels := by rfl

def raw40961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40961 raw40961Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw40961 raw40961Labels = mixedMoment B raw40961step0 raw40961step0Labels := by
      have hz : ∀ j, raw40961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40961step0 = (fun i j => raw40961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40961step0 raw40961; decide +kernel
      have hl : raw40961step0Labels = raw40961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40961 raw40961Labels permutation346 hz
    mixedMoment B raw40961step0 raw40961step0Labels = mixedMoment B raw40961step1 raw40961step1Labels := by
      have ha : raw40961step1 = (fun i j => raw40961step0 (permutation71 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40961step1 raw40961step0; decide +kernel
      have hl : raw40961step1Labels = raw40961step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40961step0 raw40961step0Labels permutation71 permutation6
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw40962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40962 raw40962Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw40962 raw40962Labels = mixedMoment B raw40962step0 raw40962step0Labels := by
      have hz : ∀ j, raw40962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40962step0 = (fun i j => raw40962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40962step0 raw40962; decide +kernel
      have hl : raw40962step0Labels = raw40962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40962 raw40962Labels permutation346 hz
    mixedMoment B raw40962step0 raw40962step0Labels = mixedMoment B raw40962step1 raw40962step1Labels := by
      have ha : raw40962step1 = (fun i j => raw40962step0 (permutation72 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40962step1 raw40962step0; decide +kernel
      have hl : raw40962step1Labels = raw40962step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40962step0 raw40962step0Labels permutation72 permutation6
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw40963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw40963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw40963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40963 raw40963Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw40963 raw40963Labels = mixedMoment B raw40963step0 raw40963step0Labels := by
      have hz : ∀ j, raw40963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40963step0 = (fun i j => raw40963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40963step0 raw40963; decide +kernel
      have hl : raw40963step0Labels = raw40963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40963 raw40963Labels permutation346 hz
    mixedMoment B raw40963step0 raw40963step0Labels = mixedMoment B raw40963step1 raw40963step1Labels := by
      have ha : raw40963step1 = (fun i j => raw40963step0 (permutation85 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40963step1 raw40963step0; decide +kernel
      have hl : raw40963step1Labels = raw40963step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40963step0 raw40963step0Labels permutation85 permutation6
    mixedMoment B raw40963step1 raw40963step1Labels = mixedMoment B raw40963step2 raw40963step2Labels := by
      have ha : raw40963step2 = -raw40963step1 := by apply Matrix.ext; change ∀ i j, raw40963step2 i j = -(raw40963step1 i j); unfold raw40963step2 raw40963step1; decide +kernel
      have hl : raw40963step2Labels = raw40963step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1810 node1810Labels := by rfl

def raw40964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw40964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40964 raw40964Labels = mixedMoment B node2814 node2814Labels := by
  calc
    mixedMoment B raw40964 raw40964Labels = mixedMoment B raw40964step0 raw40964step0Labels := by
      have ha : raw40964step0 = (fun i j => raw40964 (permutation609 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40964step0 raw40964; decide +kernel
      have hl : raw40964step0Labels = raw40964Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40964 raw40964Labels permutation609 permutation6
    _ = mixedMoment B node2814 node2814Labels := by rfl

def raw40965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw40965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40965 raw40965Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw40965 raw40965Labels = mixedMoment B raw40965step0 raw40965step0Labels := by
      have ha : raw40965step0 = (fun i j => raw40965 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40965step0 raw40965; decide +kernel
      have hl : raw40965step0Labels = raw40965Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40965 raw40965Labels permutation332 permutation6
    _ = mixedMoment B node3692 node3692Labels := by rfl

def raw40966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40966 raw40966Labels = mixedMoment B node3671 node3671Labels := by
  calc
    mixedMoment B raw40966 raw40966Labels = mixedMoment B raw40966step0 raw40966step0Labels := by
      have ha : raw40966step0 = (fun i j => raw40966 (permutation331 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40966step0 raw40966; decide +kernel
      have hl : raw40966step0Labels = raw40966Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40966 raw40966Labels permutation331 permutation6
    _ = mixedMoment B node3671 node3671Labels := by rfl

def raw40967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1]]
def raw40967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw40967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw40967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw40967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40967 raw40967Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw40967 raw40967Labels = mixedMoment B raw40967step0 raw40967step0Labels := by
      have hz : ∀ j, raw40967 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40967step0 = (fun i j => raw40967 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40967step0 raw40967; decide +kernel
      have hl : raw40967step0Labels = raw40967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40967 raw40967Labels permutation520 hz
    mixedMoment B raw40967step0 raw40967step0Labels = mixedMoment B raw40967step1 raw40967step1Labels := by
      have ha : raw40967step1 = (fun i j => raw40967step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40967step1 raw40967step0; decide +kernel
      have hl : raw40967step1Labels = raw40967step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40967step0 raw40967step0Labels permutation137 permutation3
    mixedMoment B raw40967step1 raw40967step1Labels = mixedMoment B raw40967step2 raw40967step2Labels := by
      have ha : raw40967step2 = -raw40967step1 := by apply Matrix.ext; change ∀ i j, raw40967step2 i j = -(raw40967step1 i j); unfold raw40967step2 raw40967step1; decide +kernel
      have hl : raw40967step2Labels = raw40967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw40968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw40968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw40968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw40968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40968 raw40968Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw40968 raw40968Labels = mixedMoment B raw40968step0 raw40968step0Labels := by
      have ha : raw40968step0 = (fun i j => raw40968 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40968step0 raw40968; decide +kernel
      have hl : raw40968step0Labels = raw40968Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40968 raw40968Labels permutation674 permutation3
    mixedMoment B raw40968step0 raw40968step0Labels = mixedMoment B raw40968step1 raw40968step1Labels := by
      have ha : raw40968step1 = -raw40968step0 := by apply Matrix.ext; change ∀ i j, raw40968step1 i j = -(raw40968step0 i j); unfold raw40968step1 raw40968step0; decide +kernel
      have hl : raw40968step1Labels = raw40968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3899 node3899Labels := by rfl

def raw40969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1]]
def raw40969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40969 raw40969Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw40969 raw40969Labels = mixedMoment B raw40969step0 raw40969step0Labels := by
      have ha : raw40969step0 = (fun i j => raw40969 (permutation526 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40969step0 raw40969; decide +kernel
      have hl : raw40969step0Labels = raw40969Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40969 raw40969Labels permutation526 permutation6
    mixedMoment B raw40969step0 raw40969step0Labels = mixedMoment B raw40969step1 raw40969step1Labels := by
      have ha : raw40969step1 = -raw40969step0 := by apply Matrix.ext; change ∀ i j, raw40969step1 i j = -(raw40969step0 i j); unfold raw40969step1 raw40969step0; decide +kernel
      have hl : raw40969step1Labels = raw40969step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3731 node3731Labels := by rfl

def raw40970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw40970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40970step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40970 raw40970Labels = mixedMoment B node1811 node1811Labels := by
  calc
    mixedMoment B raw40970 raw40970Labels = mixedMoment B raw40970step0 raw40970step0Labels := by
      have ha : raw40970step0 = (fun i j => raw40970 (permutation520 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40970step0 raw40970; decide +kernel
      have hl : raw40970step0Labels = raw40970Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40970 raw40970Labels permutation520 permutation6
    mixedMoment B raw40970step0 raw40970step0Labels = mixedMoment B raw40970step1 raw40970step1Labels := by
      have ha : raw40970step1 = -raw40970step0 := by apply Matrix.ext; change ∀ i j, raw40970step1 i j = -(raw40970step0 i j); unfold raw40970step1 raw40970step0; decide +kernel
      have hl : raw40970step1Labels = raw40970step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1811 node1811Labels := by rfl

def raw40971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40971 raw40971Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw40971 raw40971Labels = mixedMoment B raw40971step0 raw40971step0Labels := by
      have ha : raw40971step0 = (fun i j => raw40971 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40971step0 raw40971; decide +kernel
      have hl : raw40971step0Labels = raw40971Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40971 raw40971Labels permutation260 permutation6
    mixedMoment B raw40971step0 raw40971step0Labels = mixedMoment B raw40971step1 raw40971step1Labels := by
      have ha : raw40971step1 = -raw40971step0 := by apply Matrix.ext; change ∀ i j, raw40971step1 i j = -(raw40971step0 i j); unfold raw40971step1 raw40971step0; decide +kernel
      have hl : raw40971step1Labels = raw40971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw40972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw40972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40972 raw40972Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw40972 raw40972Labels = mixedMoment B raw40972step0 raw40972step0Labels := by
      have hz : ∀ j, raw40972 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40972step0 = (fun i j => raw40972 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40972step0 raw40972; decide +kernel
      have hl : raw40972step0Labels = raw40972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40972 raw40972Labels permutation434 hz
    mixedMoment B raw40972step0 raw40972step0Labels = mixedMoment B raw40972step1 raw40972step1Labels := by
      have ha : raw40972step1 = (fun i j => raw40972step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40972step1 raw40972step0; decide +kernel
      have hl : raw40972step1Labels = raw40972step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40972step0 raw40972step0Labels permutation104 permutation6
    mixedMoment B raw40972step1 raw40972step1Labels = mixedMoment B raw40972step2 raw40972step2Labels := by
      have ha : raw40972step2 = -raw40972step1 := by apply Matrix.ext; change ∀ i j, raw40972step2 i j = -(raw40972step1 i j); unfold raw40972step2 raw40972step1; decide +kernel
      have hl : raw40972step2Labels = raw40972step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1812 node1812Labels := by rfl

def raw40973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40973 raw40973Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw40973 raw40973Labels = mixedMoment B raw40973step0 raw40973step0Labels := by
      have ha : raw40973step0 = (fun i j => raw40973 (permutation608 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40973step0 raw40973; decide +kernel
      have hl : raw40973step0Labels = raw40973Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40973 raw40973Labels permutation608 permutation6
    _ = mixedMoment B node2896 node2896Labels := by rfl

def raw40974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40974 raw40974Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw40974 raw40974Labels = mixedMoment B raw40974step0 raw40974step0Labels := by
      have ha : raw40974step0 = (fun i j => raw40974 (permutation448 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40974step0 raw40974; decide +kernel
      have hl : raw40974step0Labels = raw40974Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40974 raw40974Labels permutation448 permutation6
    mixedMoment B raw40974step0 raw40974step0Labels = mixedMoment B raw40974step1 raw40974step1Labels := by
      have ha : raw40974step1 = -raw40974step0 := by apply Matrix.ext; change ∀ i j, raw40974step1 i j = -(raw40974step0 i j); unfold raw40974step1 raw40974step0; decide +kernel
      have hl : raw40974step1Labels = raw40974step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw40975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw40975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40975 raw40975Labels = mixedMoment B node1805 node1805Labels := by
  calc
    mixedMoment B raw40975 raw40975Labels = mixedMoment B raw40975step0 raw40975step0Labels := by
      have ha : raw40975step0 = (fun i j => raw40975 (permutation448 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40975step0 raw40975; decide +kernel
      have hl : raw40975step0Labels = raw40975Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40975 raw40975Labels permutation448 permutation6
    mixedMoment B raw40975step0 raw40975step0Labels = mixedMoment B raw40975step1 raw40975step1Labels := by
      have ha : raw40975step1 = -raw40975step0 := by apply Matrix.ext; change ∀ i j, raw40975step1 i j = -(raw40975step0 i j); unfold raw40975step1 raw40975step0; decide +kernel
      have hl : raw40975step1Labels = raw40975step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1805 node1805Labels := by rfl

def raw40976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 2, -4]]
def raw40976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 2, -4]]
def raw40976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -3, 3], ![2, 2, -4]]
def raw40976step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw40976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40976 raw40976Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw40976 raw40976Labels = mixedMoment B raw40976step0 raw40976step0Labels := by
      have hz : ∀ j, raw40976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40976step0 = (fun i j => raw40976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40976step0 raw40976; decide +kernel
      have hl : raw40976step0Labels = raw40976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40976 raw40976Labels permutation434 hz
    mixedMoment B raw40976step0 raw40976step0Labels = mixedMoment B raw40976step1 raw40976step1Labels := by
      have hz : ∀ j, raw40976step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40976step1 = (fun i j => raw40976step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40976step1 raw40976step0; decide +kernel
      have hl : raw40976step1Labels = raw40976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40976step0 raw40976step0Labels permutation80 hz
    mixedMoment B raw40976step1 raw40976step1Labels = mixedMoment B raw40976step2 raw40976step2Labels := by
      have ha : raw40976step2 = (fun i j => raw40976step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40976step2 raw40976step1; decide +kernel
      have hl : raw40976step2Labels = raw40976step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40976step1 raw40976step1Labels permutation28 permutation6
    _ = mixedMoment B node1143 node1143Labels := by rfl

def raw40977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw40977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw40977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 2, -3], ![1, -3, 2]]
def raw40977step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw40977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40977 raw40977Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw40977 raw40977Labels = mixedMoment B raw40977step0 raw40977step0Labels := by
      have hz : ∀ j, raw40977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40977step0 = (fun i j => raw40977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40977step0 raw40977; decide +kernel
      have hl : raw40977step0Labels = raw40977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40977 raw40977Labels permutation434 hz
    mixedMoment B raw40977step0 raw40977step0Labels = mixedMoment B raw40977step1 raw40977step1Labels := by
      have hz : ∀ j, raw40977step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40977step1 = (fun i j => raw40977step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40977step1 raw40977step0; decide +kernel
      have hl : raw40977step1Labels = raw40977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40977step0 raw40977step0Labels permutation80 hz
    mixedMoment B raw40977step1 raw40977step1Labels = mixedMoment B raw40977step2 raw40977step2Labels := by
      have ha : raw40977step2 = (fun i j => raw40977step1 (permutation22 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40977step2 raw40977step1; decide +kernel
      have hl : raw40977step2Labels = raw40977step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40977step1 raw40977step1Labels permutation22 permutation6
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw40978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw40978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw40978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40978 raw40978Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw40978 raw40978Labels = mixedMoment B raw40978step0 raw40978step0Labels := by
      have hz : ∀ j, raw40978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40978step0 = (fun i j => raw40978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40978step0 raw40978; decide +kernel
      have hl : raw40978step0Labels = raw40978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40978 raw40978Labels permutation346 hz
    mixedMoment B raw40978step0 raw40978step0Labels = mixedMoment B raw40978step1 raw40978step1Labels := by
      have ha : raw40978step1 = (fun i j => raw40978step0 (permutation136 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40978step1 raw40978step0; decide +kernel
      have hl : raw40978step1Labels = raw40978step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40978step0 raw40978step0Labels permutation136 permutation6
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw40979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40979 raw40979Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw40979 raw40979Labels = mixedMoment B raw40979step0 raw40979step0Labels := by
      have hz : ∀ j, raw40979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40979step0 = (fun i j => raw40979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40979step0 raw40979; decide +kernel
      have hl : raw40979step0Labels = raw40979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40979 raw40979Labels permutation346 hz
    mixedMoment B raw40979step0 raw40979step0Labels = mixedMoment B raw40979step1 raw40979step1Labels := by
      have ha : raw40979step1 = (fun i j => raw40979step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40979step1 raw40979step0; decide +kernel
      have hl : raw40979step1Labels = raw40979step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40979step0 raw40979step0Labels permutation113 permutation6
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw40980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40980step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40980 raw40980Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw40980 raw40980Labels = mixedMoment B raw40980step0 raw40980step0Labels := by
      have hz : ∀ j, raw40980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40980step0 = (fun i j => raw40980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40980step0 raw40980; decide +kernel
      have hl : raw40980step0Labels = raw40980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40980 raw40980Labels permutation346 hz
    mixedMoment B raw40980step0 raw40980step0Labels = mixedMoment B raw40980step1 raw40980step1Labels := by
      have ha : raw40980step1 = (fun i j => raw40980step0 (permutation114 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40980step1 raw40980step0; decide +kernel
      have hl : raw40980step1Labels = raw40980step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40980step0 raw40980step0Labels permutation114 permutation6
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw40981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw40981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw40981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw40981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40981 raw40981Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw40981 raw40981Labels = mixedMoment B raw40981step0 raw40981step0Labels := by
      have hz : ∀ j, raw40981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40981step0 = (fun i j => raw40981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40981step0 raw40981; decide +kernel
      have hl : raw40981step0Labels = raw40981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40981 raw40981Labels permutation346 hz
    mixedMoment B raw40981step0 raw40981step0Labels = mixedMoment B raw40981step1 raw40981step1Labels := by
      have ha : raw40981step1 = (fun i j => raw40981step0 (permutation84 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40981step1 raw40981step0; decide +kernel
      have hl : raw40981step1Labels = raw40981step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40981step0 raw40981step0Labels permutation84 permutation6
    mixedMoment B raw40981step1 raw40981step1Labels = mixedMoment B raw40981step2 raw40981step2Labels := by
      have ha : raw40981step2 = -raw40981step1 := by apply Matrix.ext; change ∀ i j, raw40981step2 i j = -(raw40981step1 i j); unfold raw40981step2 raw40981step1; decide +kernel
      have hl : raw40981step2Labels = raw40981step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1807 node1807Labels := by rfl

def raw40982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]
def raw40982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]
def raw40982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40982 raw40982Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw40982 raw40982Labels = mixedMoment B raw40982step0 raw40982step0Labels := by
      have hz : ∀ j, raw40982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40982step0 = (fun i j => raw40982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40982step0 raw40982; decide +kernel
      have hl : raw40982step0Labels = raw40982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40982 raw40982Labels permutation346 hz
    mixedMoment B raw40982step0 raw40982step0Labels = mixedMoment B raw40982step1 raw40982step1Labels := by
      have ha : raw40982step1 = (fun i j => raw40982step0 (permutation80 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40982step1 raw40982step0; decide +kernel
      have hl : raw40982step1Labels = raw40982step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40982step0 raw40982step0Labels permutation80 permutation6
    mixedMoment B raw40982step1 raw40982step1Labels = mixedMoment B raw40982step2 raw40982step2Labels := by
      have ha : raw40982step2 = -raw40982step1 := by apply Matrix.ext; change ∀ i j, raw40982step2 i j = -(raw40982step1 i j); unfold raw40982step2 raw40982step1; decide +kernel
      have hl : raw40982step2Labels = raw40982step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1815 node1815Labels := by rfl

def raw40983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw40983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40983 raw40983Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw40983 raw40983Labels = mixedMoment B raw40983step0 raw40983step0Labels := by
      have ha : raw40983step0 = (fun i j => raw40983 (permutation540 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40983step0 raw40983; decide +kernel
      have hl : raw40983step0Labels = raw40983Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40983 raw40983Labels permutation540 permutation6
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw40984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw40984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40984 raw40984Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw40984 raw40984Labels = mixedMoment B raw40984step0 raw40984step0Labels := by
      have ha : raw40984step0 = (fun i j => raw40984 (permutation539 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40984step0 raw40984; decide +kernel
      have hl : raw40984step0Labels = raw40984Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40984 raw40984Labels permutation539 permutation6
    _ = mixedMoment B node2431 node2431Labels := by rfl

def raw40985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw40985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40985 raw40985Labels = mixedMoment B node3709 node3709Labels := by
  calc
    mixedMoment B raw40985 raw40985Labels = mixedMoment B raw40985step0 raw40985step0Labels := by
      have ha : raw40985step0 = (fun i j => raw40985 (permutation440 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40985step0 raw40985; decide +kernel
      have hl : raw40985step0Labels = raw40985Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40985 raw40985Labels permutation440 permutation6
    mixedMoment B raw40985step0 raw40985step0Labels = mixedMoment B raw40985step1 raw40985step1Labels := by
      have ha : raw40985step1 = -raw40985step0 := by apply Matrix.ext; change ∀ i j, raw40985step1 i j = -(raw40985step0 i j); unfold raw40985step1 raw40985step0; decide +kernel
      have hl : raw40985step1Labels = raw40985step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3709 node3709Labels := by rfl

def raw40986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw40986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw40986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw40986step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40986step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 3, -5]]
def raw40986step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40986step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw40986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40986 raw40986Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw40986 raw40986Labels = mixedMoment B raw40986step0 raw40986step0Labels := by
      have hz : ∀ j, raw40986 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40986step0 = (fun i j => raw40986 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40986step0 raw40986; decide +kernel
      have hl : raw40986step0Labels = raw40986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40986 raw40986Labels permutation434 hz
    mixedMoment B raw40986step0 raw40986step0Labels = mixedMoment B raw40986step1 raw40986step1Labels := by
      have hz : ∀ j, raw40986step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40986step1 = (fun i j => raw40986step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40986step1 raw40986step0; decide +kernel
      have hl : raw40986step1Labels = raw40986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40986step0 raw40986step0Labels permutation80 hz
    mixedMoment B raw40986step1 raw40986step1Labels = mixedMoment B raw40986step2 raw40986step2Labels := by
      have hz : ∀ j, raw40986step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40986step2 = (fun i j => raw40986step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40986step2 raw40986step1; decide +kernel
      have hl : raw40986step2Labels = raw40986step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40986step1 raw40986step1Labels permutation14 hz
    mixedMoment B raw40986step2 raw40986step2Labels = mixedMoment B raw40986step3 raw40986step3Labels := by
      have ha : raw40986step3 = (fun i j => raw40986step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40986step3 raw40986step2; decide +kernel
      have hl : raw40986step3Labels = raw40986step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40986step2 raw40986step2Labels permutation6 permutation6
    _ = mixedMoment B node618 node618Labels := by rfl

def raw40987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw40987Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw40987step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw40987step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40987 raw40987Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw40987 raw40987Labels = mixedMoment B raw40987step0 raw40987step0Labels := by
      have hz : ∀ j, raw40987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40987step0 = (fun i j => raw40987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40987step0 raw40987; decide +kernel
      have hl : raw40987step0Labels = raw40987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40987 raw40987Labels permutation346 hz
    mixedMoment B raw40987step0 raw40987step0Labels = mixedMoment B raw40987step1 raw40987step1Labels := by
      have hz : ∀ j, raw40987step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40987step1 = (fun i j => raw40987step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40987step1 raw40987step0; decide +kernel
      have hl : raw40987step1Labels = raw40987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40987step0 raw40987step0Labels permutation56 hz
    mixedMoment B raw40987step1 raw40987step1Labels = mixedMoment B raw40987step2 raw40987step2Labels := by
      have ha : raw40987step2 = (fun i j => raw40987step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40987step2 raw40987step1; decide +kernel
      have hl : raw40987step2Labels = raw40987step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40987step1 raw40987step1Labels permutation28 permutation6
    _ = mixedMoment B node613 node613Labels := by rfl

def raw40988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw40988Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw40988step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw40988step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40988 raw40988Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw40988 raw40988Labels = mixedMoment B raw40988step0 raw40988step0Labels := by
      have hz : ∀ j, raw40988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40988step0 = (fun i j => raw40988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40988step0 raw40988; decide +kernel
      have hl : raw40988step0Labels = raw40988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40988 raw40988Labels permutation346 hz
    mixedMoment B raw40988step0 raw40988step0Labels = mixedMoment B raw40988step1 raw40988step1Labels := by
      have hz : ∀ j, raw40988step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40988step1 = (fun i j => raw40988step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40988step1 raw40988step0; decide +kernel
      have hl : raw40988step1Labels = raw40988step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40988step0 raw40988step0Labels permutation56 hz
    mixedMoment B raw40988step1 raw40988step1Labels = mixedMoment B raw40988step2 raw40988step2Labels := by
      have ha : raw40988step2 = (fun i j => raw40988step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40988step2 raw40988step1; decide +kernel
      have hl : raw40988step2Labels = raw40988step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40988step1 raw40988step1Labels permutation23 permutation6
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw40989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw40989Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw40989step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw40989step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40989step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40989 raw40989Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw40989 raw40989Labels = mixedMoment B raw40989step0 raw40989step0Labels := by
      have hz : ∀ j, raw40989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40989step0 = (fun i j => raw40989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40989step0 raw40989; decide +kernel
      have hl : raw40989step0Labels = raw40989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40989 raw40989Labels permutation346 hz
    mixedMoment B raw40989step0 raw40989step0Labels = mixedMoment B raw40989step1 raw40989step1Labels := by
      have hz : ∀ j, raw40989step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40989step1 = (fun i j => raw40989step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40989step1 raw40989step0; decide +kernel
      have hl : raw40989step1Labels = raw40989step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40989step0 raw40989step0Labels permutation56 hz
    mixedMoment B raw40989step1 raw40989step1Labels = mixedMoment B raw40989step2 raw40989step2Labels := by
      have ha : raw40989step2 = (fun i j => raw40989step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40989step2 raw40989step1; decide +kernel
      have hl : raw40989step2Labels = raw40989step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40989step1 raw40989step1Labels permutation24 permutation6
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw40990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw40990Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw40990step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw40990step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw40990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40990 raw40990Labels = mixedMoment B node937 node937Labels := by
  calc
    mixedMoment B raw40990 raw40990Labels = mixedMoment B raw40990step0 raw40990step0Labels := by
      have hz : ∀ j, raw40990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40990step0 = (fun i j => raw40990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40990step0 raw40990; decide +kernel
      have hl : raw40990step0Labels = raw40990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40990 raw40990Labels permutation346 hz
    mixedMoment B raw40990step0 raw40990step0Labels = mixedMoment B raw40990step1 raw40990step1Labels := by
      have hz : ∀ j, raw40990step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40990step1 = (fun i j => raw40990step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40990step1 raw40990step0; decide +kernel
      have hl : raw40990step1Labels = raw40990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40990step0 raw40990step0Labels permutation56 hz
    mixedMoment B raw40990step1 raw40990step1Labels = mixedMoment B raw40990step2 raw40990step2Labels := by
      have ha : raw40990step2 = (fun i j => raw40990step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40990step2 raw40990step1; decide +kernel
      have hl : raw40990step2Labels = raw40990step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40990step1 raw40990step1Labels permutation24 permutation6
    _ = mixedMoment B node937 node937Labels := by rfl

def raw40991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw40991Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw40991step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw40991step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40991step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw40991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40991step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw40991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40991 raw40991Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw40991 raw40991Labels = mixedMoment B raw40991step0 raw40991step0Labels := by
      have hz : ∀ j, raw40991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40991step0 = (fun i j => raw40991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40991step0 raw40991; decide +kernel
      have hl : raw40991step0Labels = raw40991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40991 raw40991Labels permutation346 hz
    mixedMoment B raw40991step0 raw40991step0Labels = mixedMoment B raw40991step1 raw40991step1Labels := by
      have hz : ∀ j, raw40991step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40991step1 = (fun i j => raw40991step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40991step1 raw40991step0; decide +kernel
      have hl : raw40991step1Labels = raw40991step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40991step0 raw40991step0Labels permutation56 hz
    mixedMoment B raw40991step1 raw40991step1Labels = mixedMoment B raw40991step2 raw40991step2Labels := by
      have ha : raw40991step2 = (fun i j => raw40991step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40991step2 raw40991step1; decide +kernel
      have hl : raw40991step2Labels = raw40991step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40991step1 raw40991step1Labels permutation15 permutation6
    mixedMoment B raw40991step2 raw40991step2Labels = mixedMoment B raw40991step3 raw40991step3Labels := by
      have ha : raw40991step3 = -raw40991step2 := by apply Matrix.ext; change ∀ i j, raw40991step3 i j = -(raw40991step2 i j); unfold raw40991step3 raw40991step2; decide +kernel
      have hl : raw40991step3Labels = raw40991step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1818 node1818Labels := by rfl

def raw40992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw40992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw40992step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40992 raw40992Labels = mixedMoment B node610 node610Labels := by
  calc
    mixedMoment B raw40992 raw40992Labels = mixedMoment B raw40992step0 raw40992step0Labels := by
      have hz : ∀ j, raw40992 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40992step0 = (fun i j => raw40992 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40992step0 raw40992; decide +kernel
      have hl : raw40992step0Labels = raw40992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40992 raw40992Labels permutation265 hz
    mixedMoment B raw40992step0 raw40992step0Labels = mixedMoment B raw40992step1 raw40992step1Labels := by
      have ha : raw40992step1 = (fun i j => raw40992step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40992step1 raw40992step0; decide +kernel
      have hl : raw40992step1Labels = raw40992step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40992step0 raw40992step0Labels permutation137 permutation6
    _ = mixedMoment B node610 node610Labels := by rfl

def raw40993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40993step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40993 raw40993Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw40993 raw40993Labels = mixedMoment B raw40993step0 raw40993step0Labels := by
      have hz : ∀ j, raw40993 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40993step0 = (fun i j => raw40993 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40993step0 raw40993; decide +kernel
      have hl : raw40993step0Labels = raw40993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40993 raw40993Labels permutation265 hz
    mixedMoment B raw40993step0 raw40993step0Labels = mixedMoment B raw40993step1 raw40993step1Labels := by
      have ha : raw40993step1 = (fun i j => raw40993step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40993step1 raw40993step0; decide +kernel
      have hl : raw40993step1Labels = raw40993step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40993step0 raw40993step0Labels permutation125 permutation6
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw40994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw40994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw40994step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40994 raw40994Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw40994 raw40994Labels = mixedMoment B raw40994step0 raw40994step0Labels := by
      have hz : ∀ j, raw40994 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40994step0 = (fun i j => raw40994 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40994step0 raw40994; decide +kernel
      have hl : raw40994step0Labels = raw40994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40994 raw40994Labels permutation265 hz
    mixedMoment B raw40994step0 raw40994step0Labels = mixedMoment B raw40994step1 raw40994step1Labels := by
      have ha : raw40994step1 = (fun i j => raw40994step0 (permutation124 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40994step1 raw40994step0; decide +kernel
      have hl : raw40994step1Labels = raw40994step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40994step0 raw40994step0Labels permutation124 permutation6
    _ = mixedMoment B node932 node932Labels := by rfl

def raw40995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw40995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw40995step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40995 raw40995Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw40995 raw40995Labels = mixedMoment B raw40995step0 raw40995step0Labels := by
      have hz : ∀ j, raw40995 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40995step0 = (fun i j => raw40995 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40995step0 raw40995; decide +kernel
      have hl : raw40995step0Labels = raw40995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40995 raw40995Labels permutation265 hz
    mixedMoment B raw40995step0 raw40995step0Labels = mixedMoment B raw40995step1 raw40995step1Labels := by
      have ha : raw40995step1 = (fun i j => raw40995step0 (permutation124 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40995step1 raw40995step0; decide +kernel
      have hl : raw40995step1Labels = raw40995step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40995step0 raw40995step0Labels permutation124 permutation6
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw40996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40996 raw40996Labels = mixedMoment B node929 node929Labels := by
  calc
    mixedMoment B raw40996 raw40996Labels = mixedMoment B raw40996step0 raw40996step0Labels := by
      have ha : raw40996step0 = (fun i j => raw40996 (permutation577 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40996step0 raw40996; decide +kernel
      have hl : raw40996step0Labels = raw40996Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40996 raw40996Labels permutation577 permutation6
    _ = mixedMoment B node929 node929Labels := by rfl

def raw40997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw40997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40997 raw40997Labels = mixedMoment B node2338 node2338Labels := by
  calc
    mixedMoment B raw40997 raw40997Labels = mixedMoment B raw40997step0 raw40997step0Labels := by
      have ha : raw40997step0 = (fun i j => raw40997 (permutation577 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40997step0 raw40997; decide +kernel
      have hl : raw40997step0Labels = raw40997Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40997 raw40997Labels permutation577 permutation6
    _ = mixedMoment B node2338 node2338Labels := by rfl

def raw40998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40998Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40998step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![3, -2, -1]]
def raw40998step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40998step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![3, -2, -1]]
def raw40998step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40998step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -2, 3], ![-2, 3, -1]]
def raw40998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40998step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw40998step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40998 raw40998Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw40998 raw40998Labels = mixedMoment B raw40998step0 raw40998step0Labels := by
      have hz : ∀ j, raw40998 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40998step0 = (fun i j => raw40998 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40998step0 raw40998; decide +kernel
      have hl : raw40998step0Labels = raw40998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40998 raw40998Labels permutation520 hz
    mixedMoment B raw40998step0 raw40998step0Labels = mixedMoment B raw40998step1 raw40998step1Labels := by
      have hz : ∀ j, raw40998step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40998step1 = (fun i j => raw40998step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40998step1 raw40998step0; decide +kernel
      have hl : raw40998step1Labels = raw40998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40998step0 raw40998step0Labels permutation104 hz
    mixedMoment B raw40998step1 raw40998step1Labels = mixedMoment B raw40998step2 raw40998step2Labels := by
      have hz : ∀ j, raw40998step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40998step2 = (fun i j => raw40998step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40998step2 raw40998step1; decide +kernel
      have hl : raw40998step2Labels = raw40998step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40998step1 raw40998step1Labels permutation20 hz
    mixedMoment B raw40998step2 raw40998step2Labels = mixedMoment B raw40998step3 raw40998step3Labels := by
      have ha : raw40998step3 = (fun i j => raw40998step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40998step3 raw40998step2; decide +kernel
      have hl : raw40998step3Labels = raw40998step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40998step2 raw40998step2Labels permutation7 permutation3
    mixedMoment B raw40998step3 raw40998step3Labels = mixedMoment B raw40998step4 raw40998step4Labels := by
      have ha : raw40998step4 = -raw40998step3 := by apply Matrix.ext; change ∀ i j, raw40998step4 i j = -(raw40998step3 i j); unfold raw40998step4 raw40998step3; decide +kernel
      have hl : raw40998step4Labels = raw40998step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2789 node2789Labels := by rfl

def raw40999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40999Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40999step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![3, -1, -2]]
def raw40999step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-2, 3, -1], ![-2, -1, 3]]
def raw40999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40999step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw40999step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40999 raw40999Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw40999 raw40999Labels = mixedMoment B raw40999step0 raw40999step0Labels := by
      have hz : ∀ j, raw40999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40999step0 = (fun i j => raw40999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40999step0 raw40999; decide +kernel
      have hl : raw40999step0Labels = raw40999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40999 raw40999Labels permutation434 hz
    mixedMoment B raw40999step0 raw40999step0Labels = mixedMoment B raw40999step1 raw40999step1Labels := by
      have hz : ∀ j, raw40999step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40999step1 = (fun i j => raw40999step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40999step1 raw40999step0; decide +kernel
      have hl : raw40999step1Labels = raw40999step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40999step0 raw40999step0Labels permutation80 hz
    mixedMoment B raw40999step1 raw40999step1Labels = mixedMoment B raw40999step2 raw40999step2Labels := by
      have ha : raw40999step2 = (fun i j => raw40999step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40999step2 raw40999step1; decide +kernel
      have hl : raw40999step2Labels = raw40999step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40999step1 raw40999step1Labels permutation11 permutation6
    mixedMoment B raw40999step2 raw40999step2Labels = mixedMoment B raw40999step3 raw40999step3Labels := by
      have ha : raw40999step3 = -raw40999step2 := by apply Matrix.ext; change ∀ i j, raw40999step3 i j = -(raw40999step2 i j); unfold raw40999step3 raw40999step2; decide +kernel
      have hl : raw40999step3Labels = raw40999step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2967 node2967Labels := by rfl

def raw41000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41000Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41000step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41000step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41000step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-2, 2, 0], ![-2, -1, 3]]
def raw41000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41000step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw41000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41000 raw41000Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw41000 raw41000Labels = mixedMoment B raw41000step0 raw41000step0Labels := by
      have hz : ∀ j, raw41000 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41000step0 = (fun i j => raw41000 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41000step0 raw41000; decide +kernel
      have hl : raw41000step0Labels = raw41000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41000 raw41000Labels permutation434 hz
    mixedMoment B raw41000step0 raw41000step0Labels = mixedMoment B raw41000step1 raw41000step1Labels := by
      have hz : ∀ j, raw41000step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41000step1 = (fun i j => raw41000step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41000step1 raw41000step0; decide +kernel
      have hl : raw41000step1Labels = raw41000step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41000step0 raw41000step0Labels permutation80 hz
    mixedMoment B raw41000step1 raw41000step1Labels = mixedMoment B raw41000step2 raw41000step2Labels := by
      have ha : raw41000step2 = (fun i j => raw41000step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41000step2 raw41000step1; decide +kernel
      have hl : raw41000step2Labels = raw41000step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41000step1 raw41000step1Labels permutation11 permutation6
    mixedMoment B raw41000step2 raw41000step2Labels = mixedMoment B raw41000step3 raw41000step3Labels := by
      have ha : raw41000step3 = -raw41000step2 := by apply Matrix.ext; change ∀ i j, raw41000step3 i j = -(raw41000step2 i j); unfold raw41000step3 raw41000step2; decide +kernel
      have hl : raw41000step3Labels = raw41000step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2888 node2888Labels := by rfl

def raw41001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41001Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41001step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw41001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41001 raw41001Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw41001 raw41001Labels = mixedMoment B raw41001step0 raw41001step0Labels := by
      have hz : ∀ j, raw41001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41001step0 = (fun i j => raw41001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41001step0 raw41001; decide +kernel
      have hl : raw41001step0Labels = raw41001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41001 raw41001Labels permutation346 hz
    mixedMoment B raw41001step0 raw41001step0Labels = mixedMoment B raw41001step1 raw41001step1Labels := by
      have ha : raw41001step1 = (fun i j => raw41001step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41001step1 raw41001step0; decide +kernel
      have hl : raw41001step1Labels = raw41001step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41001step0 raw41001step0Labels permutation43 permutation6
    mixedMoment B raw41001step1 raw41001step1Labels = mixedMoment B raw41001step2 raw41001step2Labels := by
      have ha : raw41001step2 = -raw41001step1 := by apply Matrix.ext; change ∀ i j, raw41001step2 i j = -(raw41001step1 i j); unfold raw41001step2 raw41001step1; decide +kernel
      have hl : raw41001step2Labels = raw41001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw41002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41002Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41002step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw41002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41002 raw41002Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw41002 raw41002Labels = mixedMoment B raw41002step0 raw41002step0Labels := by
      have hz : ∀ j, raw41002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41002step0 = (fun i j => raw41002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41002step0 raw41002; decide +kernel
      have hl : raw41002step0Labels = raw41002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41002 raw41002Labels permutation346 hz
    mixedMoment B raw41002step0 raw41002step0Labels = mixedMoment B raw41002step1 raw41002step1Labels := by
      have ha : raw41002step1 = (fun i j => raw41002step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41002step1 raw41002step0; decide +kernel
      have hl : raw41002step1Labels = raw41002step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41002step0 raw41002step0Labels permutation41 permutation6
    mixedMoment B raw41002step1 raw41002step1Labels = mixedMoment B raw41002step2 raw41002step2Labels := by
      have ha : raw41002step2 = -raw41002step1 := by apply Matrix.ext; change ∀ i j, raw41002step2 i j = -(raw41002step1 i j); unfold raw41002step2 raw41002step1; decide +kernel
      have hl : raw41002step2Labels = raw41002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw41003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw41003Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw41003step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41003step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw41003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41003step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41003 raw41003Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw41003 raw41003Labels = mixedMoment B raw41003step0 raw41003step0Labels := by
      have hz : ∀ j, raw41003 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41003step0 = (fun i j => raw41003 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41003step0 raw41003; decide +kernel
      have hl : raw41003step0Labels = raw41003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41003 raw41003Labels permutation520 hz
    mixedMoment B raw41003step0 raw41003step0Labels = mixedMoment B raw41003step1 raw41003step1Labels := by
      have hz : ∀ j, raw41003step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41003step1 = (fun i j => raw41003step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41003step1 raw41003step0; decide +kernel
      have hl : raw41003step1Labels = raw41003step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41003step0 raw41003step0Labels permutation104 hz
    mixedMoment B raw41003step1 raw41003step1Labels = mixedMoment B raw41003step2 raw41003step2Labels := by
      have ha : raw41003step2 = (fun i j => raw41003step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41003step2 raw41003step1; decide +kernel
      have hl : raw41003step2Labels = raw41003step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41003step1 raw41003step1Labels permutation31 permutation3
    mixedMoment B raw41003step2 raw41003step2Labels = mixedMoment B raw41003step3 raw41003step3Labels := by
      have ha : raw41003step3 = -raw41003step2 := by apply Matrix.ext; change ∀ i j, raw41003step3 i j = -(raw41003step2 i j); unfold raw41003step3 raw41003step2; decide +kernel
      have hl : raw41003step3Labels = raw41003step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw41004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw41004Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw41004step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw41004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41004 raw41004Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw41004 raw41004Labels = mixedMoment B raw41004step0 raw41004step0Labels := by
      have hz : ∀ j, raw41004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41004step0 = (fun i j => raw41004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41004step0 raw41004; decide +kernel
      have hl : raw41004step0Labels = raw41004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41004 raw41004Labels permutation434 hz
    mixedMoment B raw41004step0 raw41004step0Labels = mixedMoment B raw41004step1 raw41004step1Labels := by
      have ha : raw41004step1 = (fun i j => raw41004step0 (permutation46 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41004step1 raw41004step0; decide +kernel
      have hl : raw41004step1Labels = raw41004step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41004step0 raw41004step0Labels permutation46 permutation6
    mixedMoment B raw41004step1 raw41004step1Labels = mixedMoment B raw41004step2 raw41004step2Labels := by
      have ha : raw41004step2 = -raw41004step1 := by apply Matrix.ext; change ∀ i j, raw41004step2 i j = -(raw41004step1 i j); unfold raw41004step2 raw41004step1; decide +kernel
      have hl : raw41004step2Labels = raw41004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw41005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41005Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41005step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41005 raw41005Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw41005 raw41005Labels = mixedMoment B raw41005step0 raw41005step0Labels := by
      have hz : ∀ j, raw41005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41005step0 = (fun i j => raw41005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41005step0 raw41005; decide +kernel
      have hl : raw41005step0Labels = raw41005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41005 raw41005Labels permutation434 hz
    mixedMoment B raw41005step0 raw41005step0Labels = mixedMoment B raw41005step1 raw41005step1Labels := by
      have ha : raw41005step1 = (fun i j => raw41005step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41005step1 raw41005step0; decide +kernel
      have hl : raw41005step1Labels = raw41005step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41005step0 raw41005step0Labels permutation55 permutation6
    mixedMoment B raw41005step1 raw41005step1Labels = mixedMoment B raw41005step2 raw41005step2Labels := by
      have ha : raw41005step2 = -raw41005step1 := by apply Matrix.ext; change ∀ i j, raw41005step2 i j = -(raw41005step1 i j); unfold raw41005step2 raw41005step1; decide +kernel
      have hl : raw41005step2Labels = raw41005step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw41006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41006Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41006step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41006 raw41006Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw41006 raw41006Labels = mixedMoment B raw41006step0 raw41006step0Labels := by
      have hz : ∀ j, raw41006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41006step0 = (fun i j => raw41006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41006step0 raw41006; decide +kernel
      have hl : raw41006step0Labels = raw41006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41006 raw41006Labels permutation434 hz
    mixedMoment B raw41006step0 raw41006step0Labels = mixedMoment B raw41006step1 raw41006step1Labels := by
      have ha : raw41006step1 = (fun i j => raw41006step0 (permutation46 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41006step1 raw41006step0; decide +kernel
      have hl : raw41006step1Labels = raw41006step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41006step0 raw41006step0Labels permutation46 permutation6
    mixedMoment B raw41006step1 raw41006step1Labels = mixedMoment B raw41006step2 raw41006step2Labels := by
      have ha : raw41006step2 = -raw41006step1 := by apply Matrix.ext; change ∀ i j, raw41006step2 i j = -(raw41006step1 i j); unfold raw41006step2 raw41006step1; decide +kernel
      have hl : raw41006step2Labels = raw41006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2885 node2885Labels := by rfl

def raw41007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41007Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41007 raw41007Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw41007 raw41007Labels = mixedMoment B raw41007step0 raw41007step0Labels := by
      have ha : raw41007step0 = (fun i j => raw41007 (permutation223 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41007step0 raw41007; decide +kernel
      have hl : raw41007step0Labels = raw41007Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41007 raw41007Labels permutation223 permutation6
    mixedMoment B raw41007step0 raw41007step0Labels = mixedMoment B raw41007step1 raw41007step1Labels := by
      have ha : raw41007step1 = -raw41007step0 := by apply Matrix.ext; change ∀ i j, raw41007step1 i j = -(raw41007step0 i j); unfold raw41007step1 raw41007step0; decide +kernel
      have hl : raw41007step1Labels = raw41007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2951 node2951Labels := by rfl

def raw41008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41008Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41008 raw41008Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw41008 raw41008Labels = mixedMoment B raw41008step0 raw41008step0Labels := by
      have ha : raw41008step0 = (fun i j => raw41008 (permutation214 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41008step0 raw41008; decide +kernel
      have hl : raw41008step0Labels = raw41008Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41008 raw41008Labels permutation214 permutation6
    mixedMoment B raw41008step0 raw41008step0Labels = mixedMoment B raw41008step1 raw41008step1Labels := by
      have ha : raw41008step1 = -raw41008step0 := by apply Matrix.ext; change ∀ i j, raw41008step1 i j = -(raw41008step0 i j); unfold raw41008step1 raw41008step0; decide +kernel
      have hl : raw41008step1Labels = raw41008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2928 node2928Labels := by rfl

def raw41009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41009Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41009step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41009 raw41009Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw41009 raw41009Labels = mixedMoment B raw41009step0 raw41009step0Labels := by
      have ha : raw41009step0 = (fun i j => raw41009 (permutation259 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41009step0 raw41009; decide +kernel
      have hl : raw41009step0Labels = raw41009Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41009 raw41009Labels permutation259 permutation6
    mixedMoment B raw41009step0 raw41009step0Labels = mixedMoment B raw41009step1 raw41009step1Labels := by
      have ha : raw41009step1 = -raw41009step0 := by apply Matrix.ext; change ∀ i j, raw41009step1 i j = -(raw41009step0 i j); unfold raw41009step1 raw41009step0; decide +kernel
      have hl : raw41009step1Labels = raw41009step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2878 node2878Labels := by rfl

def raw41010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41010Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41010 raw41010Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw41010 raw41010Labels = mixedMoment B raw41010step0 raw41010step0Labels := by
      have ha : raw41010step0 = (fun i j => raw41010 (permutation245 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41010step0 raw41010; decide +kernel
      have hl : raw41010step0Labels = raw41010Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41010 raw41010Labels permutation245 permutation6
    mixedMoment B raw41010step0 raw41010step0Labels = mixedMoment B raw41010step1 raw41010step1Labels := by
      have ha : raw41010step1 = -raw41010step0 := by apply Matrix.ext; change ∀ i j, raw41010step1 i j = -(raw41010step0 i j); unfold raw41010step1 raw41010step0; decide +kernel
      have hl : raw41010step1Labels = raw41010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw41011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41011Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41011step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41011step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw41011step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41011 raw41011Labels = mixedMoment B node2886 node2886Labels := by
  calc
    mixedMoment B raw41011 raw41011Labels = mixedMoment B raw41011step0 raw41011step0Labels := by
      have hz : ∀ j, raw41011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41011step0 = (fun i j => raw41011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41011step0 raw41011; decide +kernel
      have hl : raw41011step0Labels = raw41011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41011 raw41011Labels permutation434 hz
    mixedMoment B raw41011step0 raw41011step0Labels = mixedMoment B raw41011step1 raw41011step1Labels := by
      have hz : ∀ j, raw41011step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41011step1 = (fun i j => raw41011step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41011step1 raw41011step0; decide +kernel
      have hl : raw41011step1Labels = raw41011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41011step0 raw41011step0Labels permutation80 hz
    mixedMoment B raw41011step1 raw41011step1Labels = mixedMoment B raw41011step2 raw41011step2Labels := by
      have ha : raw41011step2 = (fun i j => raw41011step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41011step2 raw41011step1; decide +kernel
      have hl : raw41011step2Labels = raw41011step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41011step1 raw41011step1Labels permutation29 permutation6
    _ = mixedMoment B node2886 node2886Labels := by rfl

def raw41012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41012Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41012step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw41012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41012 raw41012Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw41012 raw41012Labels = mixedMoment B raw41012step0 raw41012step0Labels := by
      have hz : ∀ j, raw41012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41012step0 = (fun i j => raw41012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41012step0 raw41012; decide +kernel
      have hl : raw41012step0Labels = raw41012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41012 raw41012Labels permutation346 hz
    mixedMoment B raw41012step0 raw41012step0Labels = mixedMoment B raw41012step1 raw41012step1Labels := by
      have ha : raw41012step1 = (fun i j => raw41012step0 (permutation42 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41012step1 raw41012step0; decide +kernel
      have hl : raw41012step1Labels = raw41012step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41012step0 raw41012step0Labels permutation42 permutation6
    mixedMoment B raw41012step1 raw41012step1Labels = mixedMoment B raw41012step2 raw41012step2Labels := by
      have ha : raw41012step2 = -raw41012step1 := by apply Matrix.ext; change ∀ i j, raw41012step2 i j = -(raw41012step1 i j); unfold raw41012step2 raw41012step1; decide +kernel
      have hl : raw41012step2Labels = raw41012step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2955 node2955Labels := by rfl

def raw41013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41013Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41013step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41013 raw41013Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw41013 raw41013Labels = mixedMoment B raw41013step0 raw41013step0Labels := by
      have hz : ∀ j, raw41013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41013step0 = (fun i j => raw41013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41013step0 raw41013; decide +kernel
      have hl : raw41013step0Labels = raw41013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41013 raw41013Labels permutation346 hz
    mixedMoment B raw41013step0 raw41013step0Labels = mixedMoment B raw41013step1 raw41013step1Labels := by
      have ha : raw41013step1 = (fun i j => raw41013step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41013step1 raw41013step0; decide +kernel
      have hl : raw41013step1Labels = raw41013step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41013step0 raw41013step0Labels permutation139 permutation6
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw41014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41014Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41014step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw41014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41014step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41014 raw41014Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw41014 raw41014Labels = mixedMoment B raw41014step0 raw41014step0Labels := by
      have hz : ∀ j, raw41014 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41014step0 = (fun i j => raw41014 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41014step0 raw41014; decide +kernel
      have hl : raw41014step0Labels = raw41014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41014 raw41014Labels permutation346 hz
    mixedMoment B raw41014step0 raw41014step0Labels = mixedMoment B raw41014step1 raw41014step1Labels := by
      have ha : raw41014step1 = (fun i j => raw41014step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41014step1 raw41014step0; decide +kernel
      have hl : raw41014step1Labels = raw41014step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41014step0 raw41014step0Labels permutation54 permutation6
    mixedMoment B raw41014step1 raw41014step1Labels = mixedMoment B raw41014step2 raw41014step2Labels := by
      have ha : raw41014step2 = -raw41014step1 := by apply Matrix.ext; change ∀ i j, raw41014step2 i j = -(raw41014step1 i j); unfold raw41014step2 raw41014step1; decide +kernel
      have hl : raw41014step2Labels = raw41014step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2882 node2882Labels := by rfl

def raw41015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41015Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41015step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw41015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41015 raw41015Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw41015 raw41015Labels = mixedMoment B raw41015step0 raw41015step0Labels := by
      have hz : ∀ j, raw41015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41015step0 = (fun i j => raw41015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41015step0 raw41015; decide +kernel
      have hl : raw41015step0Labels = raw41015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41015 raw41015Labels permutation346 hz
    mixedMoment B raw41015step0 raw41015step0Labels = mixedMoment B raw41015step1 raw41015step1Labels := by
      have ha : raw41015step1 = (fun i j => raw41015step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41015step1 raw41015step0; decide +kernel
      have hl : raw41015step1Labels = raw41015step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41015step0 raw41015step0Labels permutation48 permutation6
    mixedMoment B raw41015step1 raw41015step1Labels = mixedMoment B raw41015step2 raw41015step2Labels := by
      have ha : raw41015step2 = -raw41015step1 := by apply Matrix.ext; change ∀ i j, raw41015step2 i j = -(raw41015step1 i j); unfold raw41015step2 raw41015step1; decide +kernel
      have hl : raw41015step2Labels = raw41015step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw41016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw41016Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw41016step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw41016step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw41016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41016step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41016 raw41016Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw41016 raw41016Labels = mixedMoment B raw41016step0 raw41016step0Labels := by
      have hz : ∀ j, raw41016 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41016step0 = (fun i j => raw41016 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41016step0 raw41016; decide +kernel
      have hl : raw41016step0Labels = raw41016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41016 raw41016Labels permutation520 hz
    mixedMoment B raw41016step0 raw41016step0Labels = mixedMoment B raw41016step1 raw41016step1Labels := by
      have hz : ∀ j, raw41016step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41016step1 = (fun i j => raw41016step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41016step1 raw41016step0; decide +kernel
      have hl : raw41016step1Labels = raw41016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41016step0 raw41016step0Labels permutation104 hz
    mixedMoment B raw41016step1 raw41016step1Labels = mixedMoment B raw41016step2 raw41016step2Labels := by
      have ha : raw41016step2 = (fun i j => raw41016step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41016step2 raw41016step1; decide +kernel
      have hl : raw41016step2Labels = raw41016step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41016step1 raw41016step1Labels permutation31 permutation3
    mixedMoment B raw41016step2 raw41016step2Labels = mixedMoment B raw41016step3 raw41016step3Labels := by
      have ha : raw41016step3 = -raw41016step2 := by apply Matrix.ext; change ∀ i j, raw41016step3 i j = -(raw41016step2 i j); unfold raw41016step3 raw41016step2; decide +kernel
      have hl : raw41016step3Labels = raw41016step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw41017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw41017Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![3, -1, -2]]
def raw41017step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw41017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41017 raw41017Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw41017 raw41017Labels = mixedMoment B raw41017step0 raw41017step0Labels := by
      have hz : ∀ j, raw41017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41017step0 = (fun i j => raw41017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41017step0 raw41017; decide +kernel
      have hl : raw41017step0Labels = raw41017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41017 raw41017Labels permutation434 hz
    mixedMoment B raw41017step0 raw41017step0Labels = mixedMoment B raw41017step1 raw41017step1Labels := by
      have ha : raw41017step1 = (fun i j => raw41017step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41017step1 raw41017step0; decide +kernel
      have hl : raw41017step1Labels = raw41017step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41017step0 raw41017step0Labels permutation45 permutation6
    mixedMoment B raw41017step1 raw41017step1Labels = mixedMoment B raw41017step2 raw41017step2Labels := by
      have ha : raw41017step2 = -raw41017step1 := by apply Matrix.ext; change ∀ i j, raw41017step2 i j = -(raw41017step1 i j); unfold raw41017step2 raw41017step1; decide +kernel
      have hl : raw41017step2Labels = raw41017step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2942 node2942Labels := by rfl

def raw41018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41018Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41018step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41018 raw41018Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw41018 raw41018Labels = mixedMoment B raw41018step0 raw41018step0Labels := by
      have hz : ∀ j, raw41018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41018step0 = (fun i j => raw41018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41018step0 raw41018; decide +kernel
      have hl : raw41018step0Labels = raw41018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41018 raw41018Labels permutation434 hz
    mixedMoment B raw41018step0 raw41018step0Labels = mixedMoment B raw41018step1 raw41018step1Labels := by
      have ha : raw41018step1 = (fun i j => raw41018step0 (permutation51 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41018step1 raw41018step0; decide +kernel
      have hl : raw41018step1Labels = raw41018step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41018step0 raw41018step0Labels permutation51 permutation6
    mixedMoment B raw41018step1 raw41018step1Labels = mixedMoment B raw41018step2 raw41018step2Labels := by
      have ha : raw41018step2 = -raw41018step1 := by apply Matrix.ext; change ∀ i j, raw41018step2 i j = -(raw41018step1 i j); unfold raw41018step2 raw41018step1; decide +kernel
      have hl : raw41018step2Labels = raw41018step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw41019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41019step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw41019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41019step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41019 raw41019Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw41019 raw41019Labels = mixedMoment B raw41019step0 raw41019step0Labels := by
      have hz : ∀ j, raw41019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41019step0 = (fun i j => raw41019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41019step0 raw41019; decide +kernel
      have hl : raw41019step0Labels = raw41019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41019 raw41019Labels permutation434 hz
    mixedMoment B raw41019step0 raw41019step0Labels = mixedMoment B raw41019step1 raw41019step1Labels := by
      have ha : raw41019step1 = (fun i j => raw41019step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41019step1 raw41019step0; decide +kernel
      have hl : raw41019step1Labels = raw41019step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41019step0 raw41019step0Labels permutation45 permutation6
    mixedMoment B raw41019step1 raw41019step1Labels = mixedMoment B raw41019step2 raw41019step2Labels := by
      have ha : raw41019step2 = -raw41019step1 := by apply Matrix.ext; change ∀ i j, raw41019step2 i j = -(raw41019step1 i j); unfold raw41019step2 raw41019step1; decide +kernel
      have hl : raw41019step2Labels = raw41019step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw41020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41020step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41020step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41020 raw41020Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw41020 raw41020Labels = mixedMoment B raw41020step0 raw41020step0Labels := by
      have hz : ∀ j, raw41020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41020step0 = (fun i j => raw41020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41020step0 raw41020; decide +kernel
      have hl : raw41020step0Labels = raw41020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41020 raw41020Labels permutation434 hz
    mixedMoment B raw41020step0 raw41020step0Labels = mixedMoment B raw41020step1 raw41020step1Labels := by
      have ha : raw41020step1 = (fun i j => raw41020step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41020step1 raw41020step0; decide +kernel
      have hl : raw41020step1Labels = raw41020step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41020step0 raw41020step0Labels permutation45 permutation6
    mixedMoment B raw41020step1 raw41020step1Labels = mixedMoment B raw41020step2 raw41020step2Labels := by
      have ha : raw41020step2 = -raw41020step1 := by apply Matrix.ext; change ∀ i j, raw41020step2 i j = -(raw41020step1 i j); unfold raw41020step2 raw41020step1; decide +kernel
      have hl : raw41020step2Labels = raw41020step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2867 node2867Labels := by rfl

def raw41021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41021step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41021 raw41021Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw41021 raw41021Labels = mixedMoment B raw41021step0 raw41021step0Labels := by
      have ha : raw41021step0 = (fun i j => raw41021 (permutation205 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41021step0 raw41021; decide +kernel
      have hl : raw41021step0Labels = raw41021Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41021 raw41021Labels permutation205 permutation6
    mixedMoment B raw41021step0 raw41021step0Labels = mixedMoment B raw41021step1 raw41021step1Labels := by
      have ha : raw41021step1 = -raw41021step0 := by apply Matrix.ext; change ∀ i j, raw41021step1 i j = -(raw41021step0 i j); unfold raw41021step1 raw41021step0; decide +kernel
      have hl : raw41021step1Labels = raw41021step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2933 node2933Labels := by rfl

def raw41022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41022Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41022step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41022 raw41022Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw41022 raw41022Labels = mixedMoment B raw41022step0 raw41022step0Labels := by
      have ha : raw41022step0 = (fun i j => raw41022 (permutation213 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41022step0 raw41022; decide +kernel
      have hl : raw41022step0Labels = raw41022Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41022 raw41022Labels permutation213 permutation6
    mixedMoment B raw41022step0 raw41022step0Labels = mixedMoment B raw41022step1 raw41022step1Labels := by
      have ha : raw41022step1 = -raw41022step0 := by apply Matrix.ext; change ∀ i j, raw41022step1 i j = -(raw41022step0 i j); unfold raw41022step1 raw41022step0; decide +kernel
      have hl : raw41022step1Labels = raw41022step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw41023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41023Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41023 raw41023Labels = mixedMoment B node2861 node2861Labels := by
  calc
    mixedMoment B raw41023 raw41023Labels = mixedMoment B raw41023step0 raw41023step0Labels := by
      have ha : raw41023step0 = (fun i j => raw41023 (permutation249 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41023step0 raw41023; decide +kernel
      have hl : raw41023step0Labels = raw41023Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41023 raw41023Labels permutation249 permutation6
    mixedMoment B raw41023step0 raw41023step0Labels = mixedMoment B raw41023step1 raw41023step1Labels := by
      have ha : raw41023step1 = -raw41023step0 := by apply Matrix.ext; change ∀ i j, raw41023step1 i j = -(raw41023step0 i j); unfold raw41023step1 raw41023step0; decide +kernel
      have hl : raw41023step1Labels = raw41023step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2861 node2861Labels := by rfl

def raw41024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41024Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41024step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41024 raw41024Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw41024 raw41024Labels = mixedMoment B raw41024step0 raw41024step0Labels := by
      have ha : raw41024step0 = (fun i j => raw41024 (permutation241 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41024step0 raw41024; decide +kernel
      have hl : raw41024step0Labels = raw41024Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41024 raw41024Labels permutation241 permutation6
    mixedMoment B raw41024step0 raw41024step0Labels = mixedMoment B raw41024step1 raw41024step1Labels := by
      have ha : raw41024step1 = -raw41024step0 := by apply Matrix.ext; change ∀ i j, raw41024step1 i j = -(raw41024step0 i j); unfold raw41024step1 raw41024step0; decide +kernel
      have hl : raw41024step1Labels = raw41024step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw41025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw41025Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41025step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw41025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41025step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41025step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41025 raw41025Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw41025 raw41025Labels = mixedMoment B raw41025step0 raw41025step0Labels := by
      have hz : ∀ j, raw41025 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41025step0 = (fun i j => raw41025 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41025step0 raw41025; decide +kernel
      have hl : raw41025step0Labels = raw41025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41025 raw41025Labels permutation520 hz
    mixedMoment B raw41025step0 raw41025step0Labels = mixedMoment B raw41025step1 raw41025step1Labels := by
      have ha : raw41025step1 = (fun i j => raw41025step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41025step1 raw41025step0; decide +kernel
      have hl : raw41025step1Labels = raw41025step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41025step0 raw41025step0Labels permutation145 permutation3
    mixedMoment B raw41025step1 raw41025step1Labels = mixedMoment B raw41025step2 raw41025step2Labels := by
      have ha : raw41025step2 = -raw41025step1 := by apply Matrix.ext; change ∀ i j, raw41025step2 i j = -(raw41025step1 i j); unfold raw41025step2 raw41025step1; decide +kernel
      have hl : raw41025step2Labels = raw41025step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw41026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41026Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41026step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41026step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41026 raw41026Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw41026 raw41026Labels = mixedMoment B raw41026step0 raw41026step0Labels := by
      have hz : ∀ j, raw41026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41026step0 = (fun i j => raw41026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41026step0 raw41026; decide +kernel
      have hl : raw41026step0Labels = raw41026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41026 raw41026Labels permutation434 hz
    mixedMoment B raw41026step0 raw41026step0Labels = mixedMoment B raw41026step1 raw41026step1Labels := by
      have ha : raw41026step1 = (fun i j => raw41026step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41026step1 raw41026step0; decide +kernel
      have hl : raw41026step1Labels = raw41026step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41026step0 raw41026step0Labels permutation44 permutation6
    mixedMoment B raw41026step1 raw41026step1Labels = mixedMoment B raw41026step2 raw41026step2Labels := by
      have ha : raw41026step2 = -raw41026step1 := by apply Matrix.ext; change ∀ i j, raw41026step2 i j = -(raw41026step1 i j); unfold raw41026step2 raw41026step1; decide +kernel
      have hl : raw41026step2Labels = raw41026step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw41027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41027Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41027step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41027step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw41027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41027 raw41027Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw41027 raw41027Labels = mixedMoment B raw41027step0 raw41027step0Labels := by
      have hz : ∀ j, raw41027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41027step0 = (fun i j => raw41027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41027step0 raw41027; decide +kernel
      have hl : raw41027step0Labels = raw41027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41027 raw41027Labels permutation434 hz
    mixedMoment B raw41027step0 raw41027step0Labels = mixedMoment B raw41027step1 raw41027step1Labels := by
      have hz : ∀ j, raw41027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41027step1 = (fun i j => raw41027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41027step1 raw41027step0; decide +kernel
      have hl : raw41027step1Labels = raw41027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41027step0 raw41027step0Labels permutation80 hz
    mixedMoment B raw41027step1 raw41027step1Labels = mixedMoment B raw41027step2 raw41027step2Labels := by
      have ha : raw41027step2 = (fun i j => raw41027step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41027step2 raw41027step1; decide +kernel
      have hl : raw41027step2Labels = raw41027step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41027step1 raw41027step1Labels permutation29 permutation6
    _ = mixedMoment B node1243 node1243Labels := by rfl

def raw41028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw41028Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw41028step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw41028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41028 raw41028Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw41028 raw41028Labels = mixedMoment B raw41028step0 raw41028step0Labels := by
      have hz : ∀ j, raw41028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41028step0 = (fun i j => raw41028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41028step0 raw41028; decide +kernel
      have hl : raw41028step0Labels = raw41028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41028 raw41028Labels permutation346 hz
    mixedMoment B raw41028step0 raw41028step0Labels = mixedMoment B raw41028step1 raw41028step1Labels := by
      have ha : raw41028step1 = (fun i j => raw41028step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41028step1 raw41028step0; decide +kernel
      have hl : raw41028step1Labels = raw41028step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41028step0 raw41028step0Labels permutation125 permutation6
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw41029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41029Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41029step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41029 raw41029Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw41029 raw41029Labels = mixedMoment B raw41029step0 raw41029step0Labels := by
      have hz : ∀ j, raw41029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41029step0 = (fun i j => raw41029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41029step0 raw41029; decide +kernel
      have hl : raw41029step0Labels = raw41029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41029 raw41029Labels permutation346 hz
    mixedMoment B raw41029step0 raw41029step0Labels = mixedMoment B raw41029step1 raw41029step1Labels := by
      have ha : raw41029step1 = (fun i j => raw41029step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41029step1 raw41029step0; decide +kernel
      have hl : raw41029step1Labels = raw41029step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41029step0 raw41029step0Labels permutation139 permutation6
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw41030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41030Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41030step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw41030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41030 raw41030Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw41030 raw41030Labels = mixedMoment B raw41030step0 raw41030step0Labels := by
      have hz : ∀ j, raw41030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41030step0 = (fun i j => raw41030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41030step0 raw41030; decide +kernel
      have hl : raw41030step0Labels = raw41030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41030 raw41030Labels permutation346 hz
    mixedMoment B raw41030step0 raw41030step0Labels = mixedMoment B raw41030step1 raw41030step1Labels := by
      have ha : raw41030step1 = (fun i j => raw41030step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41030step1 raw41030step0; decide +kernel
      have hl : raw41030step1Labels = raw41030step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41030step0 raw41030step0Labels permutation95 permutation6
    _ = mixedMoment B node2558 node2558Labels := by rfl

def raw41031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41031Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41031step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41031 raw41031Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw41031 raw41031Labels = mixedMoment B raw41031step0 raw41031step0Labels := by
      have hz : ∀ j, raw41031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41031step0 = (fun i j => raw41031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41031step0 raw41031; decide +kernel
      have hl : raw41031step0Labels = raw41031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41031 raw41031Labels permutation346 hz
    mixedMoment B raw41031step0 raw41031step0Labels = mixedMoment B raw41031step1 raw41031step1Labels := by
      have ha : raw41031step1 = (fun i j => raw41031step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41031step1 raw41031step0; decide +kernel
      have hl : raw41031step1Labels = raw41031step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41031step0 raw41031step0Labels permutation89 permutation6
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw41032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw41032Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -2, -1]]
def raw41032step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![3, -2, -1]]
def raw41032step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41032 raw41032Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw41032 raw41032Labels = mixedMoment B raw41032step0 raw41032step0Labels := by
      have hz : ∀ j, raw41032 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41032step0 = (fun i j => raw41032 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41032step0 raw41032; decide +kernel
      have hl : raw41032step0Labels = raw41032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41032 raw41032Labels permutation520 hz
    mixedMoment B raw41032step0 raw41032step0Labels = mixedMoment B raw41032step1 raw41032step1Labels := by
      have hz : ∀ j, raw41032step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41032step1 = (fun i j => raw41032step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41032step1 raw41032step0; decide +kernel
      have hl : raw41032step1Labels = raw41032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41032step0 raw41032step0Labels permutation104 hz
    mixedMoment B raw41032step1 raw41032step1Labels = mixedMoment B raw41032step2 raw41032step2Labels := by
      have ha : raw41032step2 = (fun i j => raw41032step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41032step2 raw41032step1; decide +kernel
      have hl : raw41032step2Labels = raw41032step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41032step1 raw41032step1Labels permutation25 permutation6
    _ = mixedMoment B node2134 node2134Labels := by rfl

def raw41033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw41033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![3, -1, -2]]
def raw41033step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41033 raw41033Labels = mixedMoment B node1825 node1825Labels := by
  calc
    mixedMoment B raw41033 raw41033Labels = mixedMoment B raw41033step0 raw41033step0Labels := by
      have hz : ∀ j, raw41033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41033step0 = (fun i j => raw41033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41033step0 raw41033; decide +kernel
      have hl : raw41033step0Labels = raw41033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41033 raw41033Labels permutation434 hz
    mixedMoment B raw41033step0 raw41033step0Labels = mixedMoment B raw41033step1 raw41033step1Labels := by
      have ha : raw41033step1 = (fun i j => raw41033step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41033step1 raw41033step0; decide +kernel
      have hl : raw41033step1Labels = raw41033step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41033step0 raw41033step0Labels permutation101 permutation6
    _ = mixedMoment B node1825 node1825Labels := by rfl

def raw41034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41034step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41034 raw41034Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw41034 raw41034Labels = mixedMoment B raw41034step0 raw41034step0Labels := by
      have hz : ∀ j, raw41034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41034step0 = (fun i j => raw41034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41034step0 raw41034; decide +kernel
      have hl : raw41034step0Labels = raw41034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41034 raw41034Labels permutation434 hz
    mixedMoment B raw41034step0 raw41034step0Labels = mixedMoment B raw41034step1 raw41034step1Labels := by
      have ha : raw41034step1 = (fun i j => raw41034step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41034step1 raw41034step0; decide +kernel
      have hl : raw41034step1Labels = raw41034step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41034step0 raw41034step0Labels permutation103 permutation6
    _ = mixedMoment B node2090 node2090Labels := by rfl

def raw41035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw41035step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw41035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41035 raw41035Labels = mixedMoment B node1808 node1808Labels := by
  calc
    mixedMoment B raw41035 raw41035Labels = mixedMoment B raw41035step0 raw41035step0Labels := by
      have hz : ∀ j, raw41035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41035step0 = (fun i j => raw41035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41035step0 raw41035; decide +kernel
      have hl : raw41035step0Labels = raw41035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41035 raw41035Labels permutation434 hz
    mixedMoment B raw41035step0 raw41035step0Labels = mixedMoment B raw41035step1 raw41035step1Labels := by
      have ha : raw41035step1 = (fun i j => raw41035step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41035step1 raw41035step0; decide +kernel
      have hl : raw41035step1Labels = raw41035step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41035step0 raw41035step0Labels permutation101 permutation6
    _ = mixedMoment B node1808 node1808Labels := by rfl

def raw41036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41036 raw41036Labels = mixedMoment B node1973 node1973Labels := by
  calc
    mixedMoment B raw41036 raw41036Labels = mixedMoment B raw41036step0 raw41036step0Labels := by
      have ha : raw41036step0 = (fun i j => raw41036 (permutation412 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41036step0 raw41036; decide +kernel
      have hl : raw41036step0Labels = raw41036Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41036 raw41036Labels permutation412 permutation6
    _ = mixedMoment B node1973 node1973Labels := by rfl

def raw41037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41037 raw41037Labels = mixedMoment B node1790 node1790Labels := by
  calc
    mixedMoment B raw41037 raw41037Labels = mixedMoment B raw41037step0 raw41037step0Labels := by
      have ha : raw41037step0 = (fun i j => raw41037 (permutation431 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41037step0 raw41037; decide +kernel
      have hl : raw41037step0Labels = raw41037Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41037 raw41037Labels permutation431 permutation6
    _ = mixedMoment B node1790 node1790Labels := by rfl

def raw41038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw41038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -2, -1]]
def raw41038step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 3, -1]]
def raw41038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw41038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41038 raw41038Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw41038 raw41038Labels = mixedMoment B raw41038step0 raw41038step0Labels := by
      have hz : ∀ j, raw41038 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41038step0 = (fun i j => raw41038 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41038step0 raw41038; decide +kernel
      have hl : raw41038step0Labels = raw41038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41038 raw41038Labels permutation520 hz
    mixedMoment B raw41038step0 raw41038step0Labels = mixedMoment B raw41038step1 raw41038step1Labels := by
      have ha : raw41038step1 = (fun i j => raw41038step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41038step1 raw41038step0; decide +kernel
      have hl : raw41038step1Labels = raw41038step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41038step0 raw41038step0Labels permutation151 permutation3
    mixedMoment B raw41038step1 raw41038step1Labels = mixedMoment B raw41038step2 raw41038step2Labels := by
      have ha : raw41038step2 = -raw41038step1 := by apply Matrix.ext; change ∀ i j, raw41038step2 i j = -(raw41038step1 i j); unfold raw41038step2 raw41038step1; decide +kernel
      have hl : raw41038step2Labels = raw41038step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2759 node2759Labels := by rfl

def raw41039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw41039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw41039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41039 raw41039Labels = mixedMoment B node2902 node2902Labels := by
  calc
    mixedMoment B raw41039 raw41039Labels = mixedMoment B raw41039step0 raw41039step0Labels := by
      have ha : raw41039step0 = (fun i j => raw41039 (permutation227 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41039step0 raw41039; decide +kernel
      have hl : raw41039step0Labels = raw41039Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41039 raw41039Labels permutation227 permutation6
    mixedMoment B raw41039step0 raw41039step0Labels = mixedMoment B raw41039step1 raw41039step1Labels := by
      have ha : raw41039step1 = -raw41039step0 := by apply Matrix.ext; change ∀ i j, raw41039step1 i j = -(raw41039step0 i j); unfold raw41039step1 raw41039step0; decide +kernel
      have hl : raw41039step1Labels = raw41039step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2902 node2902Labels := by rfl

def raw41040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw41040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41040 raw41040Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw41040 raw41040Labels = mixedMoment B raw41040step0 raw41040step0Labels := by
      have ha : raw41040step0 = (fun i j => raw41040 (permutation169 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41040step0 raw41040; decide +kernel
      have hl : raw41040step0Labels = raw41040Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41040 raw41040Labels permutation169 permutation6
    mixedMoment B raw41040step0 raw41040step0Labels = mixedMoment B raw41040step1 raw41040step1Labels := by
      have ha : raw41040step1 = -raw41040step0 := by apply Matrix.ext; change ∀ i j, raw41040step1 i j = -(raw41040step0 i j); unfold raw41040step1 raw41040step0; decide +kernel
      have hl : raw41040step1Labels = raw41040step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2984 node2984Labels := by rfl

def raw41041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41041step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41041 raw41041Labels = mixedMoment B node2848 node2848Labels := by
  calc
    mixedMoment B raw41041 raw41041Labels = mixedMoment B raw41041step0 raw41041step0Labels := by
      have ha : raw41041step0 = (fun i j => raw41041 (permutation227 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41041step0 raw41041; decide +kernel
      have hl : raw41041step0Labels = raw41041Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41041 raw41041Labels permutation227 permutation6
    mixedMoment B raw41041step0 raw41041step0Labels = mixedMoment B raw41041step1 raw41041step1Labels := by
      have ha : raw41041step1 = -raw41041step0 := by apply Matrix.ext; change ∀ i j, raw41041step1 i j = -(raw41041step0 i j); unfold raw41041step1 raw41041step0; decide +kernel
      have hl : raw41041step1Labels = raw41041step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2848 node2848Labels := by rfl

def raw41042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw41042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw41042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw41042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41042 raw41042Labels = mixedMoment B node2979 node2979Labels := by
  calc
    mixedMoment B raw41042 raw41042Labels = mixedMoment B raw41042step0 raw41042step0Labels := by
      have hz : ∀ j, raw41042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41042step0 = (fun i j => raw41042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41042step0 raw41042; decide +kernel
      have hl : raw41042step0Labels = raw41042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41042 raw41042Labels permutation434 hz
    mixedMoment B raw41042step0 raw41042step0Labels = mixedMoment B raw41042step1 raw41042step1Labels := by
      have ha : raw41042step1 = (fun i j => raw41042step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41042step1 raw41042step0; decide +kernel
      have hl : raw41042step1Labels = raw41042step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41042step0 raw41042step0Labels permutation37 permutation6
    mixedMoment B raw41042step1 raw41042step1Labels = mixedMoment B raw41042step2 raw41042step2Labels := by
      have ha : raw41042step2 = -raw41042step1 := by apply Matrix.ext; change ∀ i j, raw41042step2 i j = -(raw41042step1 i j); unfold raw41042step2 raw41042step1; decide +kernel
      have hl : raw41042step2Labels = raw41042step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2979 node2979Labels := by rfl

def raw41043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw41043step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw41043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41043 raw41043Labels = mixedMoment B node2811 node2811Labels := by
  calc
    mixedMoment B raw41043 raw41043Labels = mixedMoment B raw41043step0 raw41043step0Labels := by
      have hz : ∀ j, raw41043 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41043step0 = (fun i j => raw41043 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41043step0 raw41043; decide +kernel
      have hl : raw41043step0Labels = raw41043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41043 raw41043Labels permutation434 hz
    mixedMoment B raw41043step0 raw41043step0Labels = mixedMoment B raw41043step1 raw41043step1Labels := by
      have ha : raw41043step1 = (fun i j => raw41043step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41043step1 raw41043step0; decide +kernel
      have hl : raw41043step1Labels = raw41043step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41043step0 raw41043step0Labels permutation143 permutation6
    _ = mixedMoment B node2811 node2811Labels := by rfl

def raw41044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, -1, 0], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41044 raw41044Labels = mixedMoment B node2900 node2900Labels := by
  calc
    mixedMoment B raw41044 raw41044Labels = mixedMoment B raw41044step0 raw41044step0Labels := by
      have ha : raw41044step0 = (fun i j => raw41044 (permutation205 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41044step0 raw41044; decide +kernel
      have hl : raw41044step0Labels = raw41044Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41044 raw41044Labels permutation205 permutation6
    mixedMoment B raw41044step0 raw41044step0Labels = mixedMoment B raw41044step1 raw41044step1Labels := by
      have ha : raw41044step1 = -raw41044step0 := by apply Matrix.ext; change ∀ i j, raw41044step1 i j = -(raw41044step0 i j); unfold raw41044step1 raw41044step0; decide +kernel
      have hl : raw41044step1Labels = raw41044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2900 node2900Labels := by rfl

def raw41045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41045 raw41045Labels = mixedMoment B node2797 node2797Labels := by
  calc
    mixedMoment B raw41045 raw41045Labels = mixedMoment B raw41045step0 raw41045step0Labels := by
      have ha : raw41045step0 = (fun i j => raw41045 (permutation644 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41045step0 raw41045; decide +kernel
      have hl : raw41045step0Labels = raw41045Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41045 raw41045Labels permutation644 permutation6
    _ = mixedMoment B node2797 node2797Labels := by rfl

def raw41046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41046 raw41046Labels = mixedMoment B node2846 node2846Labels := by
  calc
    mixedMoment B raw41046 raw41046Labels = mixedMoment B raw41046step0 raw41046step0Labels := by
      have ha : raw41046step0 = (fun i j => raw41046 (permutation251 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41046step0 raw41046; decide +kernel
      have hl : raw41046step0Labels = raw41046Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41046 raw41046Labels permutation251 permutation6
    mixedMoment B raw41046step0 raw41046step0Labels = mixedMoment B raw41046step1 raw41046step1Labels := by
      have ha : raw41046step1 = -raw41046step0 := by apply Matrix.ext; change ∀ i j, raw41046step1 i j = -(raw41046step0 i j); unfold raw41046step1 raw41046step0; decide +kernel
      have hl : raw41046step1Labels = raw41046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2846 node2846Labels := by rfl

def raw41047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41047 raw41047Labels = mixedMoment B node2981 node2981Labels := by
  calc
    mixedMoment B raw41047 raw41047Labels = mixedMoment B raw41047step0 raw41047step0Labels := by
      have ha : raw41047step0 = (fun i j => raw41047 (permutation169 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41047step0 raw41047; decide +kernel
      have hl : raw41047step0Labels = raw41047Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41047 raw41047Labels permutation169 permutation6
    mixedMoment B raw41047step0 raw41047step0Labels = mixedMoment B raw41047step1 raw41047step1Labels := by
      have ha : raw41047step1 = -raw41047step0 := by apply Matrix.ext; change ∀ i j, raw41047step1 i j = -(raw41047step0 i j); unfold raw41047step1 raw41047step0; decide +kernel
      have hl : raw41047step1Labels = raw41047step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2981 node2981Labels := by rfl

def raw41048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 3, -1]]
def raw41048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -3, 1]]
def raw41048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41048 raw41048Labels = mixedMoment B node2746 node2746Labels := by
  calc
    mixedMoment B raw41048 raw41048Labels = mixedMoment B raw41048step0 raw41048step0Labels := by
      have ha : raw41048step0 = (fun i j => raw41048 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41048step0 raw41048; decide +kernel
      have hl : raw41048step0Labels = raw41048Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41048 raw41048Labels permutation640 permutation3
    mixedMoment B raw41048step0 raw41048step0Labels = mixedMoment B raw41048step1 raw41048step1Labels := by
      have ha : raw41048step1 = -raw41048step0 := by apply Matrix.ext; change ∀ i j, raw41048step1 i j = -(raw41048step0 i j); unfold raw41048step1 raw41048step0; decide +kernel
      have hl : raw41048step1Labels = raw41048step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2746 node2746Labels := by rfl

def raw41049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41049Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41049 raw41049Labels = mixedMoment B node2847 node2847Labels := by
  calc
    mixedMoment B raw41049 raw41049Labels = mixedMoment B raw41049step0 raw41049step0Labels := by
      have ha : raw41049step0 = (fun i j => raw41049 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41049step0 raw41049; decide +kernel
      have hl : raw41049step0Labels = raw41049Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41049 raw41049Labels permutation224 permutation6
    mixedMoment B raw41049step0 raw41049step0Labels = mixedMoment B raw41049step1 raw41049step1Labels := by
      have ha : raw41049step1 = -raw41049step0 := by apply Matrix.ext; change ∀ i j, raw41049step1 i j = -(raw41049step0 i j); unfold raw41049step1 raw41049step0; decide +kernel
      have hl : raw41049step1Labels = raw41049step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2847 node2847Labels := by rfl

def raw41050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw41050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw41050step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41050 raw41050Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw41050 raw41050Labels = mixedMoment B raw41050step0 raw41050step0Labels := by
      have hz : ∀ j, raw41050 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41050step0 = (fun i j => raw41050 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41050step0 raw41050; decide +kernel
      have hl : raw41050step0Labels = raw41050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41050 raw41050Labels permutation434 hz
    mixedMoment B raw41050step0 raw41050step0Labels = mixedMoment B raw41050step1 raw41050step1Labels := by
      have ha : raw41050step1 = (fun i j => raw41050step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41050step1 raw41050step0; decide +kernel
      have hl : raw41050step1Labels = raw41050step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41050step0 raw41050step0Labels permutation121 permutation6
    _ = mixedMoment B node2495 node2495Labels := by rfl

def raw41051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw41051step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw41051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41051 raw41051Labels = mixedMoment B node1132 node1132Labels := by
  calc
    mixedMoment B raw41051 raw41051Labels = mixedMoment B raw41051step0 raw41051step0Labels := by
      have hz : ∀ j, raw41051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41051step0 = (fun i j => raw41051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41051step0 raw41051; decide +kernel
      have hl : raw41051step0Labels = raw41051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41051 raw41051Labels permutation434 hz
    mixedMoment B raw41051step0 raw41051step0Labels = mixedMoment B raw41051step1 raw41051step1Labels := by
      have ha : raw41051step1 = (fun i j => raw41051step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41051step1 raw41051step0; decide +kernel
      have hl : raw41051step1Labels = raw41051step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41051step0 raw41051step0Labels permutation143 permutation6
    _ = mixedMoment B node1132 node1132Labels := by rfl

def raw41052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw41052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41052 raw41052Labels = mixedMoment B node2437 node2437Labels := by
  calc
    mixedMoment B raw41052 raw41052Labels = mixedMoment B raw41052step0 raw41052step0Labels := by
      have ha : raw41052step0 = (fun i j => raw41052 (permutation550 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41052step0 raw41052; decide +kernel
      have hl : raw41052step0Labels = raw41052Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41052 raw41052Labels permutation550 permutation6
    _ = mixedMoment B node2437 node2437Labels := by rfl

def raw41053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41053 raw41053Labels = mixedMoment B node1112 node1112Labels := by
  calc
    mixedMoment B raw41053 raw41053Labels = mixedMoment B raw41053step0 raw41053step0Labels := by
      have ha : raw41053step0 = (fun i j => raw41053 (permutation644 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41053step0 raw41053; decide +kernel
      have hl : raw41053step0Labels = raw41053Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41053 raw41053Labels permutation644 permutation6
    _ = mixedMoment B node1112 node1112Labels := by rfl

def raw41054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw41054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41054 raw41054Labels = mixedMoment B node2426 node2426Labels := by
  calc
    mixedMoment B raw41054 raw41054Labels = mixedMoment B raw41054step0 raw41054step0Labels := by
      have ha : raw41054step0 = (fun i j => raw41054 (permutation478 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41054step0 raw41054; decide +kernel
      have hl : raw41054step0Labels = raw41054Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41054 raw41054Labels permutation478 permutation6
    _ = mixedMoment B node2426 node2426Labels := by rfl

def raw41055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41055 raw41055Labels = mixedMoment B node2470 node2470Labels := by
  calc
    mixedMoment B raw41055 raw41055Labels = mixedMoment B raw41055step0 raw41055step0Labels := by
      have ha : raw41055step0 = (fun i j => raw41055 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41055step0 raw41055; decide +kernel
      have hl : raw41055step0Labels = raw41055Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41055 raw41055Labels permutation480 permutation6
    _ = mixedMoment B node2470 node2470Labels := by rfl

def raw41056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41056step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw41056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41056 raw41056Labels = mixedMoment B node606 node606Labels := by
  calc
    mixedMoment B raw41056 raw41056Labels = mixedMoment B raw41056step0 raw41056step0Labels := by
      have hz : ∀ j, raw41056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41056step0 = (fun i j => raw41056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41056step0 raw41056; decide +kernel
      have hl : raw41056step0Labels = raw41056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41056 raw41056Labels permutation434 hz
    mixedMoment B raw41056step0 raw41056step0Labels = mixedMoment B raw41056step1 raw41056step1Labels := by
      have hz : ∀ j, raw41056step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41056step1 = (fun i j => raw41056step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41056step1 raw41056step0; decide +kernel
      have hl : raw41056step1Labels = raw41056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41056step0 raw41056step0Labels permutation80 hz
    mixedMoment B raw41056step1 raw41056step1Labels = mixedMoment B raw41056step2 raw41056step2Labels := by
      have ha : raw41056step2 = (fun i j => raw41056step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41056step2 raw41056step1; decide +kernel
      have hl : raw41056step2Labels = raw41056step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41056step1 raw41056step1Labels permutation29 permutation6
    _ = mixedMoment B node606 node606Labels := by rfl

def raw41057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw41057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw41057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41057 raw41057Labels = mixedMoment B node945 node945Labels := by
  calc
    mixedMoment B raw41057 raw41057Labels = mixedMoment B raw41057step0 raw41057step0Labels := by
      have hz : ∀ j, raw41057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41057step0 = (fun i j => raw41057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41057step0 raw41057; decide +kernel
      have hl : raw41057step0Labels = raw41057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41057 raw41057Labels permutation346 hz
    mixedMoment B raw41057step0 raw41057step0Labels = mixedMoment B raw41057step1 raw41057step1Labels := by
      have ha : raw41057step1 = (fun i j => raw41057step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41057step1 raw41057step0; decide +kernel
      have hl : raw41057step1Labels = raw41057step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41057step0 raw41057step0Labels permutation125 permutation6
    _ = mixedMoment B node945 node945Labels := by rfl

def raw41058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41058 raw41058Labels = mixedMoment B node581 node581Labels := by
  calc
    mixedMoment B raw41058 raw41058Labels = mixedMoment B raw41058step0 raw41058step0Labels := by
      have hz : ∀ j, raw41058 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41058step0 = (fun i j => raw41058 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41058step0 raw41058; decide +kernel
      have hl : raw41058step0Labels = raw41058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41058 raw41058Labels permutation346 hz
    mixedMoment B raw41058step0 raw41058step0Labels = mixedMoment B raw41058step1 raw41058step1Labels := by
      have ha : raw41058step1 = (fun i j => raw41058step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41058step1 raw41058step0; decide +kernel
      have hl : raw41058step1Labels = raw41058step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41058step0 raw41058step0Labels permutation149 permutation6
    _ = mixedMoment B node581 node581Labels := by rfl

def raw41059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![3, -1, -2]]
def raw41059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41059step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![3, -1, -2]]
def raw41059step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41059step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41059 raw41059Labels = mixedMoment B node1831 node1831Labels := by
  calc
    mixedMoment B raw41059 raw41059Labels = mixedMoment B raw41059step0 raw41059step0Labels := by
      have hz : ∀ j, raw41059 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41059step0 = (fun i j => raw41059 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41059step0 raw41059; decide +kernel
      have hl : raw41059step0Labels = raw41059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41059 raw41059Labels permutation520 hz
    mixedMoment B raw41059step0 raw41059step0Labels = mixedMoment B raw41059step1 raw41059step1Labels := by
      have hz : ∀ j, raw41059step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41059step1 = (fun i j => raw41059step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41059step1 raw41059step0; decide +kernel
      have hl : raw41059step1Labels = raw41059step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41059step0 raw41059step0Labels permutation104 hz
    mixedMoment B raw41059step1 raw41059step1Labels = mixedMoment B raw41059step2 raw41059step2Labels := by
      have ha : raw41059step2 = (fun i j => raw41059step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41059step2 raw41059step1; decide +kernel
      have hl : raw41059step2Labels = raw41059step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41059step1 raw41059step1Labels permutation25 permutation6
    _ = mixedMoment B node1831 node1831Labels := by rfl

def raw41060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw41060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41060 raw41060Labels = mixedMoment B node1979 node1979Labels := by
  calc
    mixedMoment B raw41060 raw41060Labels = mixedMoment B raw41060step0 raw41060step0Labels := by
      have hz : ∀ j, raw41060 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41060step0 = (fun i j => raw41060 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41060step0 raw41060; decide +kernel
      have hl : raw41060step0Labels = raw41060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41060 raw41060Labels permutation434 hz
    mixedMoment B raw41060step0 raw41060step0Labels = mixedMoment B raw41060step1 raw41060step1Labels := by
      have ha : raw41060step1 = (fun i j => raw41060step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41060step1 raw41060step0; decide +kernel
      have hl : raw41060step1Labels = raw41060step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41060step0 raw41060step0Labels permutation97 permutation6
    _ = mixedMoment B node1979 node1979Labels := by rfl

def raw41061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41061 raw41061Labels = mixedMoment B node1796 node1796Labels := by
  calc
    mixedMoment B raw41061 raw41061Labels = mixedMoment B raw41061step0 raw41061step0Labels := by
      have hz : ∀ j, raw41061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41061step0 = (fun i j => raw41061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41061step0 raw41061; decide +kernel
      have hl : raw41061step0Labels = raw41061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41061 raw41061Labels permutation434 hz
    mixedMoment B raw41061step0 raw41061step0Labels = mixedMoment B raw41061step1 raw41061step1Labels := by
      have ha : raw41061step1 = (fun i j => raw41061step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41061step1 raw41061step0; decide +kernel
      have hl : raw41061step1Labels = raw41061step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41061step0 raw41061step0Labels permutation103 permutation6
    _ = mixedMoment B node1796 node1796Labels := by rfl

def raw41062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41062 raw41062Labels = mixedMoment B node2826 node2826Labels := by
  calc
    mixedMoment B raw41062 raw41062Labels = mixedMoment B raw41062step0 raw41062step0Labels := by
      have ha : raw41062step0 = (fun i j => raw41062 (permutation175 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41062step0 raw41062; decide +kernel
      have hl : raw41062step0Labels = raw41062Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41062 raw41062Labels permutation175 permutation6
    mixedMoment B raw41062step0 raw41062step0Labels = mixedMoment B raw41062step1 raw41062step1Labels := by
      have ha : raw41062step1 = -raw41062step0 := by apply Matrix.ext; change ∀ i j, raw41062step1 i j = -(raw41062step0 i j); unfold raw41062step1 raw41062step0; decide +kernel
      have hl : raw41062step1Labels = raw41062step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2826 node2826Labels := by rfl

def raw41063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41063 raw41063Labels = mixedMoment B node2824 node2824Labels := by
  calc
    mixedMoment B raw41063 raw41063Labels = mixedMoment B raw41063step0 raw41063step0Labels := by
      have ha : raw41063step0 = (fun i j => raw41063 (permutation167 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41063step0 raw41063; decide +kernel
      have hl : raw41063step0Labels = raw41063Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41063 raw41063Labels permutation167 permutation6
    mixedMoment B raw41063step0 raw41063step0Labels = mixedMoment B raw41063step1 raw41063step1Labels := by
      have ha : raw41063step1 = -raw41063step0 := by apply Matrix.ext; change ∀ i j, raw41063step1 i j = -(raw41063step0 i j); unfold raw41063step1 raw41063step0; decide +kernel
      have hl : raw41063step1Labels = raw41063step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2824 node2824Labels := by rfl

def raw41064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw41064step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41064 raw41064Labels = mixedMoment B node2827 node2827Labels := by
  calc
    mixedMoment B raw41064 raw41064Labels = mixedMoment B raw41064step0 raw41064step0Labels := by
      have hz : ∀ j, raw41064 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41064step0 = (fun i j => raw41064 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41064step0 raw41064; decide +kernel
      have hl : raw41064step0Labels = raw41064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41064 raw41064Labels permutation434 hz
    mixedMoment B raw41064step0 raw41064step0Labels = mixedMoment B raw41064step1 raw41064step1Labels := by
      have ha : raw41064step1 = (fun i j => raw41064step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41064step1 raw41064step0; decide +kernel
      have hl : raw41064step1Labels = raw41064step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41064step0 raw41064step0Labels permutation37 permutation6
    mixedMoment B raw41064step1 raw41064step1Labels = mixedMoment B raw41064step2 raw41064step2Labels := by
      have ha : raw41064step2 = -raw41064step1 := by apply Matrix.ext; change ∀ i j, raw41064step2 i j = -(raw41064step1 i j); unfold raw41064step2 raw41064step1; decide +kernel
      have hl : raw41064step2Labels = raw41064step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2827 node2827Labels := by rfl

def raw41065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41065 raw41065Labels = mixedMoment B node2802 node2802Labels := by
  calc
    mixedMoment B raw41065 raw41065Labels = mixedMoment B raw41065step0 raw41065step0Labels := by
      have hz : ∀ j, raw41065 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41065step0 = (fun i j => raw41065 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41065step0 raw41065; decide +kernel
      have hl : raw41065step0Labels = raw41065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41065 raw41065Labels permutation434 hz
    mixedMoment B raw41065step0 raw41065step0Labels = mixedMoment B raw41065step1 raw41065step1Labels := by
      have ha : raw41065step1 = (fun i j => raw41065step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41065step1 raw41065step0; decide +kernel
      have hl : raw41065step1Labels = raw41065step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41065step0 raw41065step0Labels permutation145 permutation6
    _ = mixedMoment B node2802 node2802Labels := by rfl

def raw41066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw41066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw41066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41066 raw41066Labels = mixedMoment B node2442 node2442Labels := by
  calc
    mixedMoment B raw41066 raw41066Labels = mixedMoment B raw41066step0 raw41066step0Labels := by
      have hz : ∀ j, raw41066 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41066step0 = (fun i j => raw41066 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41066step0 raw41066; decide +kernel
      have hl : raw41066step0Labels = raw41066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41066 raw41066Labels permutation434 hz
    mixedMoment B raw41066step0 raw41066step0Labels = mixedMoment B raw41066step1 raw41066step1Labels := by
      have ha : raw41066step1 = (fun i j => raw41066step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41066step1 raw41066step0; decide +kernel
      have hl : raw41066step1Labels = raw41066step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41066step0 raw41066step0Labels permutation121 permutation6
    _ = mixedMoment B node2442 node2442Labels := by rfl

def raw41067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41067 raw41067Labels = mixedMoment B node1120 node1120Labels := by
  calc
    mixedMoment B raw41067 raw41067Labels = mixedMoment B raw41067step0 raw41067step0Labels := by
      have hz : ∀ j, raw41067 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41067step0 = (fun i j => raw41067 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41067step0 raw41067; decide +kernel
      have hl : raw41067step0Labels = raw41067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41067 raw41067Labels permutation434 hz
    mixedMoment B raw41067step0 raw41067step0Labels = mixedMoment B raw41067step1 raw41067step1Labels := by
      have ha : raw41067step1 = (fun i j => raw41067step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41067step1 raw41067step0; decide +kernel
      have hl : raw41067step1Labels = raw41067step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41067step0 raw41067step0Labels permutation145 permutation6
    _ = mixedMoment B node1120 node1120Labels := by rfl

def raw41068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw41068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw41068step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 3, -4], ![2, -1, -1]]
def raw41068step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41068 raw41068Labels = mixedMoment B node953 node953Labels := by
  calc
    mixedMoment B raw41068 raw41068Labels = mixedMoment B raw41068step0 raw41068step0Labels := by
      have hz : ∀ j, raw41068 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41068step0 = (fun i j => raw41068 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41068step0 raw41068; decide +kernel
      have hl : raw41068step0Labels = raw41068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41068 raw41068Labels permutation434 hz
    mixedMoment B raw41068step0 raw41068step0Labels = mixedMoment B raw41068step1 raw41068step1Labels := by
      have hz : ∀ j, raw41068step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41068step1 = (fun i j => raw41068step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41068step1 raw41068step0; decide +kernel
      have hl : raw41068step1Labels = raw41068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41068step0 raw41068step0Labels permutation80 hz
    mixedMoment B raw41068step1 raw41068step1Labels = mixedMoment B raw41068step2 raw41068step2Labels := by
      have ha : raw41068step2 = (fun i j => raw41068step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41068step2 raw41068step1; decide +kernel
      have hl : raw41068step2Labels = raw41068step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41068step1 raw41068step1Labels permutation25 permutation6
    _ = mixedMoment B node953 node953Labels := by rfl

def raw41069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41069step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41069 raw41069Labels = mixedMoment B node589 node589Labels := by
  calc
    mixedMoment B raw41069 raw41069Labels = mixedMoment B raw41069step0 raw41069step0Labels := by
      have hz : ∀ j, raw41069 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41069step0 = (fun i j => raw41069 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41069step0 raw41069; decide +kernel
      have hl : raw41069step0Labels = raw41069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41069 raw41069Labels permutation434 hz
    mixedMoment B raw41069step0 raw41069step0Labels = mixedMoment B raw41069step1 raw41069step1Labels := by
      have hz : ∀ j, raw41069step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41069step1 = (fun i j => raw41069step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41069step1 raw41069step0; decide +kernel
      have hl : raw41069step1Labels = raw41069step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41069step0 raw41069step0Labels permutation80 hz
    mixedMoment B raw41069step1 raw41069step1Labels = mixedMoment B raw41069step2 raw41069step2Labels := by
      have ha : raw41069step2 = (fun i j => raw41069step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41069step2 raw41069step1; decide +kernel
      have hl : raw41069step2Labels = raw41069step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41069step1 raw41069step1Labels permutation31 permutation6
    _ = mixedMoment B node589 node589Labels := by rfl

def raw41070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41070step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![2, -2, 0]]
def raw41070step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41070step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]
def raw41070step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41070step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw41070step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41070 raw41070Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw41070 raw41070Labels = mixedMoment B raw41070step0 raw41070step0Labels := by
      have hz : ∀ j, raw41070 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41070step0 = (fun i j => raw41070 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41070step0 raw41070; decide +kernel
      have hl : raw41070step0Labels = raw41070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41070 raw41070Labels permutation520 hz
    mixedMoment B raw41070step0 raw41070step0Labels = mixedMoment B raw41070step1 raw41070step1Labels := by
      have hz : ∀ j, raw41070step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41070step1 = (fun i j => raw41070step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41070step1 raw41070step0; decide +kernel
      have hl : raw41070step1Labels = raw41070step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41070step0 raw41070step0Labels permutation104 hz
    mixedMoment B raw41070step1 raw41070step1Labels = mixedMoment B raw41070step2 raw41070step2Labels := by
      have hz : ∀ j, raw41070step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41070step2 = (fun i j => raw41070step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41070step2 raw41070step1; decide +kernel
      have hl : raw41070step2Labels = raw41070step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41070step1 raw41070step1Labels permutation20 hz
    mixedMoment B raw41070step2 raw41070step2Labels = mixedMoment B raw41070step3 raw41070step3Labels := by
      have ha : raw41070step3 = (fun i j => raw41070step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41070step3 raw41070step2; decide +kernel
      have hl : raw41070step3Labels = raw41070step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41070step2 raw41070step2Labels permutation5 permutation6
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw41071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41071step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![2, -1, -1]]
def raw41071step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41071step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41071 raw41071Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw41071 raw41071Labels = mixedMoment B raw41071step0 raw41071step0Labels := by
      have hz : ∀ j, raw41071 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41071step0 = (fun i j => raw41071 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41071step0 raw41071; decide +kernel
      have hl : raw41071step0Labels = raw41071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41071 raw41071Labels permutation434 hz
    mixedMoment B raw41071step0 raw41071step0Labels = mixedMoment B raw41071step1 raw41071step1Labels := by
      have hz : ∀ j, raw41071step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41071step1 = (fun i j => raw41071step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41071step1 raw41071step0; decide +kernel
      have hl : raw41071step1Labels = raw41071step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41071step0 raw41071step0Labels permutation80 hz
    mixedMoment B raw41071step1 raw41071step1Labels = mixedMoment B raw41071step2 raw41071step2Labels := by
      have ha : raw41071step2 = (fun i j => raw41071step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41071step2 raw41071step1; decide +kernel
      have hl : raw41071step2Labels = raw41071step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41071step1 raw41071step1Labels permutation19 permutation6
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw41072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41072step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -2, 2], ![2, 0, -2]]
def raw41072step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41072step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw41072step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41072 raw41072Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw41072 raw41072Labels = mixedMoment B raw41072step0 raw41072step0Labels := by
      have hz : ∀ j, raw41072 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41072step0 = (fun i j => raw41072 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41072step0 raw41072; decide +kernel
      have hl : raw41072step0Labels = raw41072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41072 raw41072Labels permutation434 hz
    mixedMoment B raw41072step0 raw41072step0Labels = mixedMoment B raw41072step1 raw41072step1Labels := by
      have hz : ∀ j, raw41072step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41072step1 = (fun i j => raw41072step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41072step1 raw41072step0; decide +kernel
      have hl : raw41072step1Labels = raw41072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41072step0 raw41072step0Labels permutation80 hz
    mixedMoment B raw41072step1 raw41072step1Labels = mixedMoment B raw41072step2 raw41072step2Labels := by
      have ha : raw41072step2 = (fun i j => raw41072step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41072step2 raw41072step1; decide +kernel
      have hl : raw41072step2Labels = raw41072step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41072step1 raw41072step1Labels permutation19 permutation6
    _ = mixedMoment B node1819 node1819Labels := by rfl

def raw41073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41073step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41073step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw41073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41073 raw41073Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw41073 raw41073Labels = mixedMoment B raw41073step0 raw41073step0Labels := by
      have hz : ∀ j, raw41073 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41073step0 = (fun i j => raw41073 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41073step0 raw41073; decide +kernel
      have hl : raw41073step0Labels = raw41073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41073 raw41073Labels permutation434 hz
    mixedMoment B raw41073step0 raw41073step0Labels = mixedMoment B raw41073step1 raw41073step1Labels := by
      have hz : ∀ j, raw41073step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41073step1 = (fun i j => raw41073step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41073step1 raw41073step0; decide +kernel
      have hl : raw41073step1Labels = raw41073step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41073step0 raw41073step0Labels permutation80 hz
    mixedMoment B raw41073step1 raw41073step1Labels = mixedMoment B raw41073step2 raw41073step2Labels := by
      have ha : raw41073step2 = (fun i j => raw41073step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41073step2 raw41073step1; decide +kernel
      have hl : raw41073step2Labels = raw41073step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41073step1 raw41073step1Labels permutation17 permutation6
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw41074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41074step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41074 raw41074Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw41074 raw41074Labels = mixedMoment B raw41074step0 raw41074step0Labels := by
      have hz : ∀ j, raw41074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41074step0 = (fun i j => raw41074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41074step0 raw41074; decide +kernel
      have hl : raw41074step0Labels = raw41074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41074 raw41074Labels permutation434 hz
    mixedMoment B raw41074step0 raw41074step0Labels = mixedMoment B raw41074step1 raw41074step1Labels := by
      have hz : ∀ j, raw41074step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41074step1 = (fun i j => raw41074step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41074step1 raw41074step0; decide +kernel
      have hl : raw41074step1Labels = raw41074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41074step0 raw41074step0Labels permutation80 hz
    mixedMoment B raw41074step1 raw41074step1Labels = mixedMoment B raw41074step2 raw41074step2Labels := by
      have ha : raw41074step2 = (fun i j => raw41074step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41074step2 raw41074step1; decide +kernel
      have hl : raw41074step2Labels = raw41074step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41074step1 raw41074step1Labels permutation17 permutation6
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw41075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41075step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41075 raw41075Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw41075 raw41075Labels = mixedMoment B raw41075step0 raw41075step0Labels := by
      have hz : ∀ j, raw41075 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41075step0 = (fun i j => raw41075 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41075step0 raw41075; decide +kernel
      have hl : raw41075step0Labels = raw41075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41075 raw41075Labels permutation346 hz
    mixedMoment B raw41075step0 raw41075step0Labels = mixedMoment B raw41075step1 raw41075step1Labels := by
      have ha : raw41075step1 = (fun i j => raw41075step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41075step1 raw41075step0; decide +kernel
      have hl : raw41075step1Labels = raw41075step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41075step0 raw41075step0Labels permutation77 permutation6
    _ = mixedMoment B node1812 node1812Labels := by rfl

def raw41076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41076step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41076 raw41076Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw41076 raw41076Labels = mixedMoment B raw41076step0 raw41076step0Labels := by
      have hz : ∀ j, raw41076 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41076step0 = (fun i j => raw41076 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41076step0 raw41076; decide +kernel
      have hl : raw41076step0Labels = raw41076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41076 raw41076Labels permutation346 hz
    mixedMoment B raw41076step0 raw41076step0Labels = mixedMoment B raw41076step1 raw41076step1Labels := by
      have ha : raw41076step1 = (fun i j => raw41076step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41076step1 raw41076step0; decide +kernel
      have hl : raw41076step1Labels = raw41076step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41076step0 raw41076step0Labels permutation73 permutation6
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw41077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41077step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw41077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41077 raw41077Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw41077 raw41077Labels = mixedMoment B raw41077step0 raw41077step0Labels := by
      have hz : ∀ j, raw41077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41077step0 = (fun i j => raw41077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41077step0 raw41077; decide +kernel
      have hl : raw41077step0Labels = raw41077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41077 raw41077Labels permutation346 hz
    mixedMoment B raw41077step0 raw41077step0Labels = mixedMoment B raw41077step1 raw41077step1Labels := by
      have ha : raw41077step1 = (fun i j => raw41077step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41077step1 raw41077step0; decide +kernel
      have hl : raw41077step1Labels = raw41077step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41077step0 raw41077step0Labels permutation73 permutation6
    _ = mixedMoment B node1970 node1970Labels := by rfl

def raw41078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41078 raw41078Labels = mixedMoment B node1964 node1964Labels := by
  calc
    mixedMoment B raw41078 raw41078Labels = mixedMoment B raw41078step0 raw41078step0Labels := by
      have ha : raw41078step0 = (fun i j => raw41078 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41078step0 raw41078; decide +kernel
      have hl : raw41078step0Labels = raw41078Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41078 raw41078Labels permutation332 permutation6
    _ = mixedMoment B node1964 node1964Labels := by rfl

def raw41079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw41079step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw41079step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw41079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41079step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw41079step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41079 raw41079Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw41079 raw41079Labels = mixedMoment B raw41079step0 raw41079step0Labels := by
      have hz : ∀ j, raw41079 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41079step0 = (fun i j => raw41079 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41079step0 raw41079; decide +kernel
      have hl : raw41079step0Labels = raw41079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41079 raw41079Labels permutation520 hz
    mixedMoment B raw41079step0 raw41079step0Labels = mixedMoment B raw41079step1 raw41079step1Labels := by
      have hz : ∀ j, raw41079step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41079step1 = (fun i j => raw41079step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41079step1 raw41079step0; decide +kernel
      have hl : raw41079step1Labels = raw41079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41079step0 raw41079step0Labels permutation104 hz
    mixedMoment B raw41079step1 raw41079step1Labels = mixedMoment B raw41079step2 raw41079step2Labels := by
      have ha : raw41079step2 = (fun i j => raw41079step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41079step2 raw41079step1; decide +kernel
      have hl : raw41079step2Labels = raw41079step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41079step1 raw41079step1Labels permutation13 permutation6
    mixedMoment B raw41079step2 raw41079step2Labels = mixedMoment B raw41079step3 raw41079step3Labels := by
      have ha : raw41079step3 = -raw41079step2 := by apply Matrix.ext; change ∀ i j, raw41079step3 i j = -(raw41079step2 i j); unfold raw41079step3 raw41079step2; decide +kernel
      have hl : raw41079step3Labels = raw41079step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw41080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41080Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw41080step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw41080step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41080 raw41080Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw41080 raw41080Labels = mixedMoment B raw41080step0 raw41080step0Labels := by
      have hz : ∀ j, raw41080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41080step0 = (fun i j => raw41080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41080step0 raw41080; decide +kernel
      have hl : raw41080step0Labels = raw41080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41080 raw41080Labels permutation434 hz
    mixedMoment B raw41080step0 raw41080step0Labels = mixedMoment B raw41080step1 raw41080step1Labels := by
      have ha : raw41080step1 = (fun i j => raw41080step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41080step1 raw41080step0; decide +kernel
      have hl : raw41080step1Labels = raw41080step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41080step0 raw41080step0Labels permutation49 permutation6
    mixedMoment B raw41080step1 raw41080step1Labels = mixedMoment B raw41080step2 raw41080step2Labels := by
      have ha : raw41080step2 = -raw41080step1 := by apply Matrix.ext; change ∀ i j, raw41080step2 i j = -(raw41080step1 i j); unfold raw41080step2 raw41080step1; decide +kernel
      have hl : raw41080step2Labels = raw41080step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw41081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw41081step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41081 raw41081Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw41081 raw41081Labels = mixedMoment B raw41081step0 raw41081step0Labels := by
      have hz : ∀ j, raw41081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41081step0 = (fun i j => raw41081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41081step0 raw41081; decide +kernel
      have hl : raw41081step0Labels = raw41081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41081 raw41081Labels permutation434 hz
    mixedMoment B raw41081step0 raw41081step0Labels = mixedMoment B raw41081step1 raw41081step1Labels := by
      have ha : raw41081step1 = (fun i j => raw41081step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41081step1 raw41081step0; decide +kernel
      have hl : raw41081step1Labels = raw41081step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41081step0 raw41081step0Labels permutation47 permutation6
    mixedMoment B raw41081step1 raw41081step1Labels = mixedMoment B raw41081step2 raw41081step2Labels := by
      have ha : raw41081step2 = -raw41081step1 := by apply Matrix.ext; change ∀ i j, raw41081step2 i j = -(raw41081step1 i j); unfold raw41081step2 raw41081step1; decide +kernel
      have hl : raw41081step2Labels = raw41081step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2817 node2817Labels := by rfl

def raw41082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41082step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41082 raw41082Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw41082 raw41082Labels = mixedMoment B raw41082step0 raw41082step0Labels := by
      have hz : ∀ j, raw41082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41082step0 = (fun i j => raw41082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41082step0 raw41082; decide +kernel
      have hl : raw41082step0Labels = raw41082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41082 raw41082Labels permutation434 hz
    mixedMoment B raw41082step0 raw41082step0Labels = mixedMoment B raw41082step1 raw41082step1Labels := by
      have ha : raw41082step1 = (fun i j => raw41082step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41082step1 raw41082step0; decide +kernel
      have hl : raw41082step1Labels = raw41082step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41082step0 raw41082step0Labels permutation55 permutation6
    mixedMoment B raw41082step1 raw41082step1Labels = mixedMoment B raw41082step2 raw41082step2Labels := by
      have ha : raw41082step2 = -raw41082step1 := by apply Matrix.ext; change ∀ i j, raw41082step2 i j = -(raw41082step1 i j); unfold raw41082step2 raw41082step1; decide +kernel
      have hl : raw41082step2Labels = raw41082step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw41083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41083step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw41083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41083 raw41083Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw41083 raw41083Labels = mixedMoment B raw41083step0 raw41083step0Labels := by
      have hz : ∀ j, raw41083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41083step0 = (fun i j => raw41083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41083step0 raw41083; decide +kernel
      have hl : raw41083step0Labels = raw41083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41083 raw41083Labels permutation434 hz
    mixedMoment B raw41083step0 raw41083step0Labels = mixedMoment B raw41083step1 raw41083step1Labels := by
      have ha : raw41083step1 = (fun i j => raw41083step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41083step1 raw41083step0; decide +kernel
      have hl : raw41083step1Labels = raw41083step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41083step0 raw41083step0Labels permutation49 permutation6
    mixedMoment B raw41083step1 raw41083step1Labels = mixedMoment B raw41083step2 raw41083step2Labels := by
      have ha : raw41083step2 = -raw41083step1 := by apply Matrix.ext; change ∀ i j, raw41083step2 i j = -(raw41083step1 i j); unfold raw41083step2 raw41083step1; decide +kernel
      have hl : raw41083step2Labels = raw41083step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw41084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41084 raw41084Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw41084 raw41084Labels = mixedMoment B raw41084step0 raw41084step0Labels := by
      have ha : raw41084step0 = (fun i j => raw41084 (permutation215 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41084step0 raw41084; decide +kernel
      have hl : raw41084step0Labels = raw41084Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41084 raw41084Labels permutation215 permutation6
    mixedMoment B raw41084step0 raw41084step0Labels = mixedMoment B raw41084step1 raw41084step1Labels := by
      have ha : raw41084step1 = -raw41084step0 := by apply Matrix.ext; change ∀ i j, raw41084step1 i j = -(raw41084step0 i j); unfold raw41084step1 raw41084step0; decide +kernel
      have hl : raw41084step1Labels = raw41084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2896 node2896Labels := by rfl

def raw41085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41085Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41085 raw41085Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw41085 raw41085Labels = mixedMoment B raw41085step0 raw41085step0Labels := by
      have ha : raw41085step0 = (fun i j => raw41085 (permutation223 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41085step0 raw41085; decide +kernel
      have hl : raw41085step0Labels = raw41085Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41085 raw41085Labels permutation223 permutation6
    mixedMoment B raw41085step0 raw41085step0Labels = mixedMoment B raw41085step1 raw41085step1Labels := by
      have ha : raw41085step1 = -raw41085step0 := by apply Matrix.ext; change ∀ i j, raw41085step1 i j = -(raw41085step0 i j); unfold raw41085step1 raw41085step0; decide +kernel
      have hl : raw41085step1Labels = raw41085step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw41086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41086Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41086 raw41086Labels = mixedMoment B node2807 node2807Labels := by
  calc
    mixedMoment B raw41086 raw41086Labels = mixedMoment B raw41086step0 raw41086step0Labels := by
      have ha : raw41086step0 = (fun i j => raw41086 (permutation217 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41086step0 raw41086; decide +kernel
      have hl : raw41086step0Labels = raw41086Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41086 raw41086Labels permutation217 permutation6
    mixedMoment B raw41086step0 raw41086step0Labels = mixedMoment B raw41086step1 raw41086step1Labels := by
      have ha : raw41086step1 = -raw41086step0 := by apply Matrix.ext; change ∀ i j, raw41086step1 i j = -(raw41086step0 i j); unfold raw41086step1 raw41086step0; decide +kernel
      have hl : raw41086step1Labels = raw41086step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2807 node2807Labels := by rfl

def raw41087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41087Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41087step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41087step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -2, 2], ![2, 1, -3]]
def raw41087step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41087step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw41087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41087 raw41087Labels = mixedMoment B node2820 node2820Labels := by
  calc
    mixedMoment B raw41087 raw41087Labels = mixedMoment B raw41087step0 raw41087step0Labels := by
      have hz : ∀ j, raw41087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41087step0 = (fun i j => raw41087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41087step0 raw41087; decide +kernel
      have hl : raw41087step0Labels = raw41087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41087 raw41087Labels permutation434 hz
    mixedMoment B raw41087step0 raw41087step0Labels = mixedMoment B raw41087step1 raw41087step1Labels := by
      have hz : ∀ j, raw41087step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41087step1 = (fun i j => raw41087step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41087step1 raw41087step0; decide +kernel
      have hl : raw41087step1Labels = raw41087step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41087step0 raw41087step0Labels permutation80 hz
    mixedMoment B raw41087step1 raw41087step1Labels = mixedMoment B raw41087step2 raw41087step2Labels := by
      have ha : raw41087step2 = (fun i j => raw41087step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41087step2 raw41087step1; decide +kernel
      have hl : raw41087step2Labels = raw41087step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41087step1 raw41087step1Labels permutation29 permutation6
    _ = mixedMoment B node2820 node2820Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
