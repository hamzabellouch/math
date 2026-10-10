import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8320 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8320step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8320step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw8320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8320step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8320step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8320 raw8320Labels = mixedMoment B node2138 node2138Labels := by
  calc
    mixedMoment B raw8320 raw8320Labels = mixedMoment B raw8320step0 raw8320step0Labels := by
      have hz : ∀ j, raw8320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8320step0 = (fun i j => raw8320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8320step0 raw8320; decide +kernel
      have hl : raw8320step0Labels = raw8320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8320 raw8320Labels permutation346 hz
    mixedMoment B raw8320step0 raw8320step0Labels = mixedMoment B raw8320step1 raw8320step1Labels := by
      have hz : ∀ j, raw8320step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8320step1 = (fun i j => raw8320step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8320step1 raw8320step0; decide +kernel
      have hl : raw8320step1Labels = raw8320step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8320step0 raw8320step0Labels permutation56 hz
    mixedMoment B raw8320step1 raw8320step1Labels = mixedMoment B raw8320step2 raw8320step2Labels := by
      have ha : raw8320step2 = (fun i j => raw8320step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8320step2 raw8320step1; decide +kernel
      have hl : raw8320step2Labels = raw8320step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8320step1 raw8320step1Labels permutation12 permutation4
    mixedMoment B raw8320step2 raw8320step2Labels = mixedMoment B raw8320step3 raw8320step3Labels := by
      have ha : raw8320step3 = -raw8320step2 := by apply Matrix.ext; change ∀ i j, raw8320step3 i j = -(raw8320step2 i j); unfold raw8320step3 raw8320step2; decide +kernel
      have hl : raw8320step3Labels = raw8320step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2138 node2138Labels := by rfl

def raw8321 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8321step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw8321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8321step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8321step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8321 raw8321Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw8321 raw8321Labels = mixedMoment B raw8321step0 raw8321step0Labels := by
      have hz : ∀ j, raw8321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8321step0 = (fun i j => raw8321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8321step0 raw8321; decide +kernel
      have hl : raw8321step0Labels = raw8321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8321 raw8321Labels permutation346 hz
    mixedMoment B raw8321step0 raw8321step0Labels = mixedMoment B raw8321step1 raw8321step1Labels := by
      have hz : ∀ j, raw8321step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8321step1 = (fun i j => raw8321step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8321step1 raw8321step0; decide +kernel
      have hl : raw8321step1Labels = raw8321step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8321step0 raw8321step0Labels permutation56 hz
    mixedMoment B raw8321step1 raw8321step1Labels = mixedMoment B raw8321step2 raw8321step2Labels := by
      have ha : raw8321step2 = (fun i j => raw8321step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8321step2 raw8321step1; decide +kernel
      have hl : raw8321step2Labels = raw8321step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8321step1 raw8321step1Labels permutation12 permutation4
    mixedMoment B raw8321step2 raw8321step2Labels = mixedMoment B raw8321step3 raw8321step3Labels := by
      have ha : raw8321step3 = -raw8321step2 := by apply Matrix.ext; change ∀ i j, raw8321step3 i j = -(raw8321step2 i j); unfold raw8321step3 raw8321step2; decide +kernel
      have hl : raw8321step3Labels = raw8321step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2134 node2134Labels := by rfl

def raw8322 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8322 raw8322Labels = mixedMoment B node2586 node2586Labels := by
  calc
    mixedMoment B raw8322 raw8322Labels = mixedMoment B raw8322step0 raw8322step0Labels := by
      have ha : raw8322step0 = (fun i j => raw8322 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8322step0 raw8322; decide +kernel
      have hl : raw8322step0Labels = raw8322Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8322 raw8322Labels permutation644 permutation2
    _ = mixedMoment B node2586 node2586Labels := by rfl

def raw8323 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8323 raw8323Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw8323 raw8323Labels = mixedMoment B raw8323step0 raw8323step0Labels := by
      have hz : ∀ j, raw8323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw8323step0 = (fun i j => raw8323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw8323step0 raw8323; decide +kernel
      have hl : raw8323step0Labels = raw8323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8323 raw8323Labels permutation434 hz
    mixedMoment B raw8323step0 raw8323step0Labels = mixedMoment B raw8323step1 raw8323step1Labels := by
      have hz : ∀ j, raw8323step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw8323step1 = (fun i j => raw8323step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw8323step1 raw8323step0; decide +kernel
      have hl : raw8323step1Labels = raw8323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8323step0 raw8323step0Labels permutation80 hz
    mixedMoment B raw8323step1 raw8323step1Labels = mixedMoment B raw8323step2 raw8323step2Labels := by
      have ha : raw8323step2 = (fun i j => raw8323step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8323step2 raw8323step1; decide +kernel
      have hl : raw8323step2Labels = raw8323step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8323step1 raw8323step1Labels permutation31 permutation2
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw8324 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8324 raw8324Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw8324 raw8324Labels = mixedMoment B raw8324step0 raw8324step0Labels := by
      have hz : ∀ j, raw8324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8324step0 = (fun i j => raw8324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8324step0 raw8324; decide +kernel
      have hl : raw8324step0Labels = raw8324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8324 raw8324Labels permutation346 hz
    mixedMoment B raw8324step0 raw8324step0Labels = mixedMoment B raw8324step1 raw8324step1Labels := by
      have ha : raw8324step1 = (fun i j => raw8324step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8324step1 raw8324step0; decide +kernel
      have hl : raw8324step1Labels = raw8324step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8324step0 raw8324step0Labels permutation149 permutation2
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw8325 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8325 raw8325Labels = mixedMoment B node1290 node1290Labels := by
  calc
    mixedMoment B raw8325 raw8325Labels = mixedMoment B raw8325step0 raw8325step0Labels := by
      have hz : ∀ j, raw8325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8325step0 = (fun i j => raw8325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8325step0 raw8325; decide +kernel
      have hl : raw8325step0Labels = raw8325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8325 raw8325Labels permutation346 hz
    mixedMoment B raw8325step0 raw8325step0Labels = mixedMoment B raw8325step1 raw8325step1Labels := by
      have ha : raw8325step1 = (fun i j => raw8325step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8325step1 raw8325step0; decide +kernel
      have hl : raw8325step1Labels = raw8325step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8325step0 raw8325step0Labels permutation149 permutation2
    _ = mixedMoment B node1290 node1290Labels := by rfl

def raw8326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8326 raw8326Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw8326 raw8326Labels = mixedMoment B raw8326step0 raw8326step0Labels := by
      have hz : ∀ j, raw8326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8326step0 = (fun i j => raw8326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8326step0 raw8326; decide +kernel
      have hl : raw8326step0Labels = raw8326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8326 raw8326Labels permutation346 hz
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw8327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8327 raw8327Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw8327 raw8327Labels = mixedMoment B raw8327step0 raw8327step0Labels := by
      have hz : ∀ j, raw8327 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8327step0 = (fun i j => raw8327 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8327step0 raw8327; decide +kernel
      have hl : raw8327step0Labels = raw8327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8327 raw8327Labels permutation265 hz
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw8328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8328step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8328step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw8328step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8328step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8328step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8328step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8328step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8328 raw8328Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw8328 raw8328Labels = mixedMoment B raw8328step0 raw8328step0Labels := by
      have hz : ∀ j, raw8328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8328step0 = (fun i j => raw8328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8328step0 raw8328; decide +kernel
      have hl : raw8328step0Labels = raw8328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8328 raw8328Labels permutation346 hz
    mixedMoment B raw8328step0 raw8328step0Labels = mixedMoment B raw8328step1 raw8328step1Labels := by
      have hz : ∀ j, raw8328step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8328step1 = (fun i j => raw8328step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8328step1 raw8328step0; decide +kernel
      have hl : raw8328step1Labels = raw8328step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8328step0 raw8328step0Labels permutation56 hz
    mixedMoment B raw8328step1 raw8328step1Labels = mixedMoment B raw8328step2 raw8328step2Labels := by
      have ha : raw8328step2 = (fun i j => raw8328step1 (permutation15 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8328step2 raw8328step1; decide +kernel
      have hl : raw8328step2Labels = raw8328step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8328step1 raw8328step1Labels permutation15 permutation4
    mixedMoment B raw8328step2 raw8328step2Labels = mixedMoment B raw8328step3 raw8328step3Labels := by
      have ha : raw8328step3 = -raw8328step2 := by apply Matrix.ext; change ∀ i j, raw8328step3 i j = -(raw8328step2 i j); unfold raw8328step3 raw8328step2; decide +kernel
      have hl : raw8328step3Labels = raw8328step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8328step3 raw8328step3Labels = mixedMoment B raw8328step4 raw8328step4Labels := by
      have ha : raw8328step4 = raw8328step3 := by apply Matrix.ext; unfold raw8328step4 raw8328step3; decide +kernel
      have hl : raw8328step3Labels = labelEmbedding7 ∘ raw8328step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8328step3 raw8328step3Labels raw8328step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw8329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8329step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw8329step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8329step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8329step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8329step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8329step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8329 raw8329Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw8329 raw8329Labels = mixedMoment B raw8329step0 raw8329step0Labels := by
      have hz : ∀ j, raw8329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8329step0 = (fun i j => raw8329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8329step0 raw8329; decide +kernel
      have hl : raw8329step0Labels = raw8329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8329 raw8329Labels permutation346 hz
    mixedMoment B raw8329step0 raw8329step0Labels = mixedMoment B raw8329step1 raw8329step1Labels := by
      have hz : ∀ j, raw8329step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8329step1 = (fun i j => raw8329step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8329step1 raw8329step0; decide +kernel
      have hl : raw8329step1Labels = raw8329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8329step0 raw8329step0Labels permutation56 hz
    mixedMoment B raw8329step1 raw8329step1Labels = mixedMoment B raw8329step2 raw8329step2Labels := by
      have ha : raw8329step2 = (fun i j => raw8329step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8329step2 raw8329step1; decide +kernel
      have hl : raw8329step2Labels = raw8329step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8329step1 raw8329step1Labels permutation11 permutation7
    mixedMoment B raw8329step2 raw8329step2Labels = mixedMoment B raw8329step3 raw8329step3Labels := by
      have ha : raw8329step3 = -raw8329step2 := by apply Matrix.ext; change ∀ i j, raw8329step3 i j = -(raw8329step2 i j); unfold raw8329step3 raw8329step2; decide +kernel
      have hl : raw8329step3Labels = raw8329step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8329step3 raw8329step3Labels = mixedMoment B raw8329step4 raw8329step4Labels := by
      have ha : raw8329step4 = raw8329step3 := by apply Matrix.ext; unfold raw8329step4 raw8329step3; decide +kernel
      have hl : raw8329step3Labels = labelEmbedding10 ∘ raw8329step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8329step3 raw8329step3Labels raw8329step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw8330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8330step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8330step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8330step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8330 raw8330Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw8330 raw8330Labels = mixedMoment B raw8330step0 raw8330step0Labels := by
      have hz : ∀ j, raw8330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8330step0 = (fun i j => raw8330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8330step0 raw8330; decide +kernel
      have hl : raw8330step0Labels = raw8330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8330 raw8330Labels permutation346 hz
    mixedMoment B raw8330step0 raw8330step0Labels = mixedMoment B raw8330step1 raw8330step1Labels := by
      have hz : ∀ j, raw8330step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8330step1 = (fun i j => raw8330step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8330step1 raw8330step0; decide +kernel
      have hl : raw8330step1Labels = raw8330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8330step0 raw8330step0Labels permutation56 hz
    mixedMoment B raw8330step1 raw8330step1Labels = mixedMoment B raw8330step2 raw8330step2Labels := by
      have ha : raw8330step2 = (fun i j => raw8330step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8330step2 raw8330step1; decide +kernel
      have hl : raw8330step2Labels = raw8330step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8330step1 raw8330step1Labels permutation19 permutation6
    mixedMoment B raw8330step2 raw8330step2Labels = mixedMoment B raw8330step3 raw8330step3Labels := by
      have ha : raw8330step3 = raw8330step2 := by apply Matrix.ext; unfold raw8330step3 raw8330step2; decide +kernel
      have hl : raw8330step2Labels = labelEmbedding9 ∘ raw8330step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8330step2 raw8330step2Labels raw8330step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw8331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8331step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8331step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8331 raw8331Labels = mixedMoment B node4571 node4571Labels := by
  calc
    mixedMoment B raw8331 raw8331Labels = mixedMoment B raw8331step0 raw8331step0Labels := by
      have hz : ∀ j, raw8331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8331step0 = (fun i j => raw8331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8331step0 raw8331; decide +kernel
      have hl : raw8331step0Labels = raw8331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8331 raw8331Labels permutation346 hz
    mixedMoment B raw8331step0 raw8331step0Labels = mixedMoment B raw8331step1 raw8331step1Labels := by
      have ha : raw8331step1 = (fun i j => raw8331step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8331step1 raw8331step0; decide +kernel
      have hl : raw8331step1Labels = raw8331step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8331step0 raw8331step0Labels permutation38 permutation3
    mixedMoment B raw8331step1 raw8331step1Labels = mixedMoment B raw8331step2 raw8331step2Labels := by
      have ha : raw8331step2 = raw8331step1 := by apply Matrix.ext; unfold raw8331step2 raw8331step1; decide +kernel
      have hl : raw8331step1Labels = labelEmbedding6 ∘ raw8331step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8331step1 raw8331step1Labels raw8331step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4571 node4571Labels := by rfl

def raw8332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw8332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8332 raw8332Labels = mixedMoment B node5153 node5153Labels := by
  calc
    mixedMoment B raw8332 raw8332Labels = mixedMoment B raw8332step0 raw8332step0Labels := by
      have ha : raw8332step0 = (fun i j => raw8332 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8332step0 raw8332; decide +kernel
      have hl : raw8332step0Labels = raw8332Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8332 raw8332Labels permutation184 permutation2
    _ = mixedMoment B node5153 node5153Labels := by rfl

def raw8333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw8333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8333 raw8333Labels = mixedMoment B node5211 node5211Labels := by
  calc
    mixedMoment B raw8333 raw8333Labels = mixedMoment B raw8333step0 raw8333step0Labels := by
      have hz : ∀ j, raw8333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8333step0 = (fun i j => raw8333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8333step0 raw8333; decide +kernel
      have hl : raw8333step0Labels = raw8333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8333 raw8333Labels permutation346 hz
    mixedMoment B raw8333step0 raw8333step0Labels = mixedMoment B raw8333step1 raw8333step1Labels := by
      have ha : raw8333step1 = (fun i j => raw8333step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8333step1 raw8333step0; decide +kernel
      have hl : raw8333step1Labels = raw8333step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8333step0 raw8333step0Labels permutation40 permutation2
    _ = mixedMoment B node5211 node5211Labels := by rfl

def raw8334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw8334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8334 raw8334Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw8334 raw8334Labels = mixedMoment B raw8334step0 raw8334step0Labels := by
      have hz : ∀ j, raw8334 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8334step0 = (fun i j => raw8334 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8334step0 raw8334; decide +kernel
      have hl : raw8334step0Labels = raw8334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8334 raw8334Labels permutation346 hz
    mixedMoment B raw8334step0 raw8334step0Labels = mixedMoment B raw8334step1 raw8334step1Labels := by
      have ha : raw8334step1 = (fun i j => raw8334step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8334step1 raw8334step0; decide +kernel
      have hl : raw8334step1Labels = raw8334step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8334step0 raw8334step0Labels permutation46 permutation2
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw8335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8335step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8335 raw8335Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw8335 raw8335Labels = mixedMoment B raw8335step0 raw8335step0Labels := by
      have hz : ∀ j, raw8335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8335step0 = (fun i j => raw8335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8335step0 raw8335; decide +kernel
      have hl : raw8335step0Labels = raw8335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8335 raw8335Labels permutation346 hz
    mixedMoment B raw8335step0 raw8335step0Labels = mixedMoment B raw8335step1 raw8335step1Labels := by
      have ha : raw8335step1 = (fun i j => raw8335step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8335step1 raw8335step0; decide +kernel
      have hl : raw8335step1Labels = raw8335step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8335step0 raw8335step0Labels permutation40 permutation2
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw8336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8336step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8336step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8336 raw8336Labels = mixedMoment B node4571 node4571Labels := by
  calc
    mixedMoment B raw8336 raw8336Labels = mixedMoment B raw8336step0 raw8336step0Labels := by
      have hz : ∀ j, raw8336 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8336step0 = (fun i j => raw8336 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8336step0 raw8336; decide +kernel
      have hl : raw8336step0Labels = raw8336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8336 raw8336Labels permutation265 hz
    mixedMoment B raw8336step0 raw8336step0Labels = mixedMoment B raw8336step1 raw8336step1Labels := by
      have ha : raw8336step1 = (fun i j => raw8336step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8336step1 raw8336step0; decide +kernel
      have hl : raw8336step1Labels = raw8336step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8336step0 raw8336step0Labels permutation38 permutation3
    mixedMoment B raw8336step1 raw8336step1Labels = mixedMoment B raw8336step2 raw8336step2Labels := by
      have ha : raw8336step2 = raw8336step1 := by apply Matrix.ext; unfold raw8336step2 raw8336step1; decide +kernel
      have hl : raw8336step1Labels = labelEmbedding6 ∘ raw8336step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8336step1 raw8336step1Labels raw8336step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4571 node4571Labels := by rfl

def raw8337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw8337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8337 raw8337Labels = mixedMoment B node5153 node5153Labels := by
  calc
    mixedMoment B raw8337 raw8337Labels = mixedMoment B raw8337step0 raw8337step0Labels := by
      have ha : raw8337step0 = (fun i j => raw8337 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8337step0 raw8337; decide +kernel
      have hl : raw8337step0Labels = raw8337Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8337 raw8337Labels permutation160 permutation2
    _ = mixedMoment B node5153 node5153Labels := by rfl

def raw8338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw8338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8338 raw8338Labels = mixedMoment B node5211 node5211Labels := by
  calc
    mixedMoment B raw8338 raw8338Labels = mixedMoment B raw8338step0 raw8338step0Labels := by
      have hz : ∀ j, raw8338 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8338step0 = (fun i j => raw8338 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8338step0 raw8338; decide +kernel
      have hl : raw8338step0Labels = raw8338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8338 raw8338Labels permutation265 hz
    mixedMoment B raw8338step0 raw8338step0Labels = mixedMoment B raw8338step1 raw8338step1Labels := by
      have ha : raw8338step1 = (fun i j => raw8338step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8338step1 raw8338step0; decide +kernel
      have hl : raw8338step1Labels = raw8338step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8338step0 raw8338step0Labels permutation40 permutation2
    _ = mixedMoment B node5211 node5211Labels := by rfl

def raw8339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw8339step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8339 raw8339Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw8339 raw8339Labels = mixedMoment B raw8339step0 raw8339step0Labels := by
      have hz : ∀ j, raw8339 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8339step0 = (fun i j => raw8339 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8339step0 raw8339; decide +kernel
      have hl : raw8339step0Labels = raw8339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8339 raw8339Labels permutation265 hz
    mixedMoment B raw8339step0 raw8339step0Labels = mixedMoment B raw8339step1 raw8339step1Labels := by
      have ha : raw8339step1 = (fun i j => raw8339step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8339step1 raw8339step0; decide +kernel
      have hl : raw8339step1Labels = raw8339step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8339step0 raw8339step0Labels permutation46 permutation2
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw8340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8340step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8340 raw8340Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw8340 raw8340Labels = mixedMoment B raw8340step0 raw8340step0Labels := by
      have hz : ∀ j, raw8340 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8340step0 = (fun i j => raw8340 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8340step0 raw8340; decide +kernel
      have hl : raw8340step0Labels = raw8340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8340 raw8340Labels permutation265 hz
    mixedMoment B raw8340step0 raw8340step0Labels = mixedMoment B raw8340step1 raw8340step1Labels := by
      have ha : raw8340step1 = (fun i j => raw8340step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8340step1 raw8340step0; decide +kernel
      have hl : raw8340step1Labels = raw8340step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8340step0 raw8340step0Labels permutation40 permutation2
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw8341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8341step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8341 raw8341Labels = mixedMoment B node4620 node4620Labels := by
  calc
    mixedMoment B raw8341 raw8341Labels = mixedMoment B raw8341step0 raw8341step0Labels := by
      have hz : ∀ j, raw8341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8341step0 = (fun i j => raw8341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8341step0 raw8341; decide +kernel
      have hl : raw8341step0Labels = raw8341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8341 raw8341Labels permutation346 hz
    mixedMoment B raw8341step0 raw8341step0Labels = mixedMoment B raw8341step1 raw8341step1Labels := by
      have hz : ∀ j, raw8341step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8341step1 = (fun i j => raw8341step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8341step1 raw8341step0; decide +kernel
      have hl : raw8341step1Labels = raw8341step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8341step0 raw8341step0Labels permutation56 hz
    mixedMoment B raw8341step1 raw8341step1Labels = mixedMoment B raw8341step2 raw8341step2Labels := by
      have ha : raw8341step2 = (fun i j => raw8341step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8341step2 raw8341step1; decide +kernel
      have hl : raw8341step2Labels = raw8341step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8341step1 raw8341step1Labels permutation10 permutation2
    _ = mixedMoment B node4620 node4620Labels := by rfl

def raw8342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8342step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8342 raw8342Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw8342 raw8342Labels = mixedMoment B raw8342step0 raw8342step0Labels := by
      have hz : ∀ j, raw8342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8342step0 = (fun i j => raw8342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8342step0 raw8342; decide +kernel
      have hl : raw8342step0Labels = raw8342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8342 raw8342Labels permutation346 hz
    mixedMoment B raw8342step0 raw8342step0Labels = mixedMoment B raw8342step1 raw8342step1Labels := by
      have ha : raw8342step1 = (fun i j => raw8342step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8342step1 raw8342step0; decide +kernel
      have hl : raw8342step1Labels = raw8342step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8342step0 raw8342step0Labels permutation34 permutation2
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw8343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8343step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8343 raw8343Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw8343 raw8343Labels = mixedMoment B raw8343step0 raw8343step0Labels := by
      have hz : ∀ j, raw8343 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8343step0 = (fun i j => raw8343 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8343step0 raw8343; decide +kernel
      have hl : raw8343step0Labels = raw8343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8343 raw8343Labels permutation265 hz
    mixedMoment B raw8343step0 raw8343step0Labels = mixedMoment B raw8343step1 raw8343step1Labels := by
      have ha : raw8343step1 = (fun i j => raw8343step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8343step1 raw8343step0; decide +kernel
      have hl : raw8343step1Labels = raw8343step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8343step0 raw8343step0Labels permutation34 permutation2
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw8344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8344step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8344step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8344 raw8344Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw8344 raw8344Labels = mixedMoment B raw8344step0 raw8344step0Labels := by
      have hz : ∀ j, raw8344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8344step0 = (fun i j => raw8344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8344step0 raw8344; decide +kernel
      have hl : raw8344step0Labels = raw8344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8344 raw8344Labels permutation346 hz
    mixedMoment B raw8344step0 raw8344step0Labels = mixedMoment B raw8344step1 raw8344step1Labels := by
      have hz : ∀ j, raw8344step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8344step1 = (fun i j => raw8344step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8344step1 raw8344step0; decide +kernel
      have hl : raw8344step1Labels = raw8344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8344step0 raw8344step0Labels permutation56 hz
    mixedMoment B raw8344step1 raw8344step1Labels = mixedMoment B raw8344step2 raw8344step2Labels := by
      have ha : raw8344step2 = (fun i j => raw8344step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8344step2 raw8344step1; decide +kernel
      have hl : raw8344step2Labels = raw8344step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8344step1 raw8344step1Labels permutation10 permutation2
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw8345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8345step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8345step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8345 raw8345Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw8345 raw8345Labels = mixedMoment B raw8345step0 raw8345step0Labels := by
      have hz : ∀ j, raw8345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8345step0 = (fun i j => raw8345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8345step0 raw8345; decide +kernel
      have hl : raw8345step0Labels = raw8345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8345 raw8345Labels permutation346 hz
    mixedMoment B raw8345step0 raw8345step0Labels = mixedMoment B raw8345step1 raw8345step1Labels := by
      have hz : ∀ j, raw8345step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8345step1 = (fun i j => raw8345step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8345step1 raw8345step0; decide +kernel
      have hl : raw8345step1Labels = raw8345step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8345step0 raw8345step0Labels permutation56 hz
    mixedMoment B raw8345step1 raw8345step1Labels = mixedMoment B raw8345step2 raw8345step2Labels := by
      have ha : raw8345step2 = (fun i j => raw8345step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8345step2 raw8345step1; decide +kernel
      have hl : raw8345step2Labels = raw8345step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8345step1 raw8345step1Labels permutation11 permutation2
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw8346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8346step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw8346step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8346step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw8346step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8346 raw8346Labels = mixedMoment B node4574 node4574Labels := by
  calc
    mixedMoment B raw8346 raw8346Labels = mixedMoment B raw8346step0 raw8346step0Labels := by
      have hz : ∀ j, raw8346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8346step0 = (fun i j => raw8346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8346step0 raw8346; decide +kernel
      have hl : raw8346step0Labels = raw8346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8346 raw8346Labels permutation346 hz
    mixedMoment B raw8346step0 raw8346step0Labels = mixedMoment B raw8346step1 raw8346step1Labels := by
      have hz : ∀ j, raw8346step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8346step1 = (fun i j => raw8346step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8346step1 raw8346step0; decide +kernel
      have hl : raw8346step1Labels = raw8346step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8346step0 raw8346step0Labels permutation56 hz
    mixedMoment B raw8346step1 raw8346step1Labels = mixedMoment B raw8346step2 raw8346step2Labels := by
      have ha : raw8346step2 = (fun i j => raw8346step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8346step2 raw8346step1; decide +kernel
      have hl : raw8346step2Labels = raw8346step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8346step1 raw8346step1Labels permutation9 permutation3
    mixedMoment B raw8346step2 raw8346step2Labels = mixedMoment B raw8346step3 raw8346step3Labels := by
      have ha : raw8346step3 = raw8346step2 := by apply Matrix.ext; unfold raw8346step3 raw8346step2; decide +kernel
      have hl : raw8346step2Labels = labelEmbedding6 ∘ raw8346step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8346step2 raw8346step2Labels raw8346step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4574 node4574Labels := by rfl

def raw8347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8347step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8347 raw8347Labels = mixedMoment B node5019 node5019Labels := by
  calc
    mixedMoment B raw8347 raw8347Labels = mixedMoment B raw8347step0 raw8347step0Labels := by
      have hz : ∀ j, raw8347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8347step0 = (fun i j => raw8347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8347step0 raw8347; decide +kernel
      have hl : raw8347step0Labels = raw8347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8347 raw8347Labels permutation346 hz
    mixedMoment B raw8347step0 raw8347step0Labels = mixedMoment B raw8347step1 raw8347step1Labels := by
      have ha : raw8347step1 = (fun i j => raw8347step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8347step1 raw8347step0; decide +kernel
      have hl : raw8347step1Labels = raw8347step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8347step0 raw8347step0Labels permutation124 permutation5
    mixedMoment B raw8347step1 raw8347step1Labels = mixedMoment B raw8347step2 raw8347step2Labels := by
      have ha : raw8347step2 = raw8347step1 := by apply Matrix.ext; unfold raw8347step2 raw8347step1; decide +kernel
      have hl : raw8347step1Labels = labelEmbedding8 ∘ raw8347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8347step1 raw8347step1Labels raw8347step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5019 node5019Labels := by rfl

def raw8348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8348step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8348step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8348 raw8348Labels = mixedMoment B node5019 node5019Labels := by
  calc
    mixedMoment B raw8348 raw8348Labels = mixedMoment B raw8348step0 raw8348step0Labels := by
      have hz : ∀ j, raw8348 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8348step0 = (fun i j => raw8348 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8348step0 raw8348; decide +kernel
      have hl : raw8348step0Labels = raw8348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8348 raw8348Labels permutation265 hz
    mixedMoment B raw8348step0 raw8348step0Labels = mixedMoment B raw8348step1 raw8348step1Labels := by
      have ha : raw8348step1 = (fun i j => raw8348step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8348step1 raw8348step0; decide +kernel
      have hl : raw8348step1Labels = raw8348step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8348step0 raw8348step0Labels permutation124 permutation5
    mixedMoment B raw8348step1 raw8348step1Labels = mixedMoment B raw8348step2 raw8348step2Labels := by
      have ha : raw8348step2 = raw8348step1 := by apply Matrix.ext; unfold raw8348step2 raw8348step1; decide +kernel
      have hl : raw8348step1Labels = labelEmbedding8 ∘ raw8348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8348step1 raw8348step1Labels raw8348step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5019 node5019Labels := by rfl

def raw8349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8349step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw8349step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8349step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw8349step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8349 raw8349Labels = mixedMoment B node5022 node5022Labels := by
  calc
    mixedMoment B raw8349 raw8349Labels = mixedMoment B raw8349step0 raw8349step0Labels := by
      have hz : ∀ j, raw8349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8349step0 = (fun i j => raw8349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8349step0 raw8349; decide +kernel
      have hl : raw8349step0Labels = raw8349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8349 raw8349Labels permutation346 hz
    mixedMoment B raw8349step0 raw8349step0Labels = mixedMoment B raw8349step1 raw8349step1Labels := by
      have hz : ∀ j, raw8349step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8349step1 = (fun i j => raw8349step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8349step1 raw8349step0; decide +kernel
      have hl : raw8349step1Labels = raw8349step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8349step0 raw8349step0Labels permutation56 hz
    mixedMoment B raw8349step1 raw8349step1Labels = mixedMoment B raw8349step2 raw8349step2Labels := by
      have ha : raw8349step2 = (fun i j => raw8349step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8349step2 raw8349step1; decide +kernel
      have hl : raw8349step2Labels = raw8349step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8349step1 raw8349step1Labels permutation24 permutation5
    mixedMoment B raw8349step2 raw8349step2Labels = mixedMoment B raw8349step3 raw8349step3Labels := by
      have ha : raw8349step3 = raw8349step2 := by apply Matrix.ext; unfold raw8349step3 raw8349step2; decide +kernel
      have hl : raw8349step2Labels = labelEmbedding8 ∘ raw8349step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8349step2 raw8349step2Labels raw8349step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5022 node5022Labels := by rfl

def raw8350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8350step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8350step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8350step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8350step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8350 raw8350Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw8350 raw8350Labels = mixedMoment B raw8350step0 raw8350step0Labels := by
      have hz : ∀ j, raw8350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8350step0 = (fun i j => raw8350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8350step0 raw8350; decide +kernel
      have hl : raw8350step0Labels = raw8350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8350 raw8350Labels permutation346 hz
    mixedMoment B raw8350step0 raw8350step0Labels = mixedMoment B raw8350step1 raw8350step1Labels := by
      have hz : ∀ j, raw8350step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8350step1 = (fun i j => raw8350step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8350step1 raw8350step0; decide +kernel
      have hl : raw8350step1Labels = raw8350step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8350step0 raw8350step0Labels permutation56 hz
    mixedMoment B raw8350step1 raw8350step1Labels = mixedMoment B raw8350step2 raw8350step2Labels := by
      have ha : raw8350step2 = (fun i j => raw8350step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8350step2 raw8350step1; decide +kernel
      have hl : raw8350step2Labels = raw8350step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8350step1 raw8350step1Labels permutation24 permutation5
    mixedMoment B raw8350step2 raw8350step2Labels = mixedMoment B raw8350step3 raw8350step3Labels := by
      have ha : raw8350step3 = raw8350step2 := by apply Matrix.ext; unfold raw8350step3 raw8350step2; decide +kernel
      have hl : raw8350step2Labels = labelEmbedding8 ∘ raw8350step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8350step2 raw8350step2Labels raw8350step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw8351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8351step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8351step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8351step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw8351step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8351step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw8351step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8351 raw8351Labels = mixedMoment B node4573 node4573Labels := by
  calc
    mixedMoment B raw8351 raw8351Labels = mixedMoment B raw8351step0 raw8351step0Labels := by
      have hz : ∀ j, raw8351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8351step0 = (fun i j => raw8351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8351step0 raw8351; decide +kernel
      have hl : raw8351step0Labels = raw8351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8351 raw8351Labels permutation346 hz
    mixedMoment B raw8351step0 raw8351step0Labels = mixedMoment B raw8351step1 raw8351step1Labels := by
      have hz : ∀ j, raw8351step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8351step1 = (fun i j => raw8351step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8351step1 raw8351step0; decide +kernel
      have hl : raw8351step1Labels = raw8351step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8351step0 raw8351step0Labels permutation56 hz
    mixedMoment B raw8351step1 raw8351step1Labels = mixedMoment B raw8351step2 raw8351step2Labels := by
      have ha : raw8351step2 = (fun i j => raw8351step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8351step2 raw8351step1; decide +kernel
      have hl : raw8351step2Labels = raw8351step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8351step1 raw8351step1Labels permutation8 permutation3
    mixedMoment B raw8351step2 raw8351step2Labels = mixedMoment B raw8351step3 raw8351step3Labels := by
      have ha : raw8351step3 = raw8351step2 := by apply Matrix.ext; unfold raw8351step3 raw8351step2; decide +kernel
      have hl : raw8351step2Labels = labelEmbedding6 ∘ raw8351step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8351step2 raw8351step2Labels raw8351step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4573 node4573Labels := by rfl

def raw8352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw8352step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8352step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8352step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8352step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8352 raw8352Labels = mixedMoment B node5008 node5008Labels := by
  calc
    mixedMoment B raw8352 raw8352Labels = mixedMoment B raw8352step0 raw8352step0Labels := by
      have hz : ∀ j, raw8352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8352step0 = (fun i j => raw8352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8352step0 raw8352; decide +kernel
      have hl : raw8352step0Labels = raw8352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8352 raw8352Labels permutation346 hz
    mixedMoment B raw8352step0 raw8352step0Labels = mixedMoment B raw8352step1 raw8352step1Labels := by
      have ha : raw8352step1 = (fun i j => raw8352step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8352step1 raw8352step0; decide +kernel
      have hl : raw8352step1Labels = raw8352step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8352step0 raw8352step0Labels permutation151 permutation3
    mixedMoment B raw8352step1 raw8352step1Labels = mixedMoment B raw8352step2 raw8352step2Labels := by
      have ha : raw8352step2 = -raw8352step1 := by apply Matrix.ext; change ∀ i j, raw8352step2 i j = -(raw8352step1 i j); unfold raw8352step2 raw8352step1; decide +kernel
      have hl : raw8352step2Labels = raw8352step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8352step2 raw8352step2Labels = mixedMoment B raw8352step3 raw8352step3Labels := by
      have ha : raw8352step3 = raw8352step2 := by apply Matrix.ext; unfold raw8352step3 raw8352step2; decide +kernel
      have hl : raw8352step2Labels = labelEmbedding6 ∘ raw8352step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8352step2 raw8352step2Labels raw8352step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5008 node5008Labels := by rfl

def raw8353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw8353step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8353step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8353step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8353step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8353 raw8353Labels = mixedMoment B node5008 node5008Labels := by
  calc
    mixedMoment B raw8353 raw8353Labels = mixedMoment B raw8353step0 raw8353step0Labels := by
      have hz : ∀ j, raw8353 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8353step0 = (fun i j => raw8353 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8353step0 raw8353; decide +kernel
      have hl : raw8353step0Labels = raw8353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8353 raw8353Labels permutation265 hz
    mixedMoment B raw8353step0 raw8353step0Labels = mixedMoment B raw8353step1 raw8353step1Labels := by
      have ha : raw8353step1 = (fun i j => raw8353step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8353step1 raw8353step0; decide +kernel
      have hl : raw8353step1Labels = raw8353step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8353step0 raw8353step0Labels permutation151 permutation3
    mixedMoment B raw8353step1 raw8353step1Labels = mixedMoment B raw8353step2 raw8353step2Labels := by
      have ha : raw8353step2 = -raw8353step1 := by apply Matrix.ext; change ∀ i j, raw8353step2 i j = -(raw8353step1 i j); unfold raw8353step2 raw8353step1; decide +kernel
      have hl : raw8353step2Labels = raw8353step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8353step2 raw8353step2Labels = mixedMoment B raw8353step3 raw8353step3Labels := by
      have ha : raw8353step3 = raw8353step2 := by apply Matrix.ext; unfold raw8353step3 raw8353step2; decide +kernel
      have hl : raw8353step2Labels = labelEmbedding6 ∘ raw8353step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8353step2 raw8353step2Labels raw8353step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5008 node5008Labels := by rfl

def raw8354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, -2, 3], ![-3, 2, 1]]
def raw8354step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8354step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw8354step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8354step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw8354step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8354 raw8354Labels = mixedMoment B node5022 node5022Labels := by
  calc
    mixedMoment B raw8354 raw8354Labels = mixedMoment B raw8354step0 raw8354step0Labels := by
      have hz : ∀ j, raw8354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8354step0 = (fun i j => raw8354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8354step0 raw8354; decide +kernel
      have hl : raw8354step0Labels = raw8354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8354 raw8354Labels permutation346 hz
    mixedMoment B raw8354step0 raw8354step0Labels = mixedMoment B raw8354step1 raw8354step1Labels := by
      have hz : ∀ j, raw8354step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8354step1 = (fun i j => raw8354step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8354step1 raw8354step0; decide +kernel
      have hl : raw8354step1Labels = raw8354step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8354step0 raw8354step0Labels permutation56 hz
    mixedMoment B raw8354step1 raw8354step1Labels = mixedMoment B raw8354step2 raw8354step2Labels := by
      have ha : raw8354step2 = (fun i j => raw8354step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8354step2 raw8354step1; decide +kernel
      have hl : raw8354step2Labels = raw8354step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8354step1 raw8354step1Labels permutation31 permutation3
    mixedMoment B raw8354step2 raw8354step2Labels = mixedMoment B raw8354step3 raw8354step3Labels := by
      have ha : raw8354step3 = -raw8354step2 := by apply Matrix.ext; change ∀ i j, raw8354step3 i j = -(raw8354step2 i j); unfold raw8354step3 raw8354step2; decide +kernel
      have hl : raw8354step3Labels = raw8354step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8354step3 raw8354step3Labels = mixedMoment B raw8354step4 raw8354step4Labels := by
      have ha : raw8354step4 = raw8354step3 := by apply Matrix.ext; unfold raw8354step4 raw8354step3; decide +kernel
      have hl : raw8354step3Labels = labelEmbedding6 ∘ raw8354step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8354step3 raw8354step3Labels raw8354step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5022 node5022Labels := by rfl

def raw8355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8355step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8355 raw8355Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw8355 raw8355Labels = mixedMoment B raw8355step0 raw8355step0Labels := by
      have hz : ∀ j, raw8355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8355step0 = (fun i j => raw8355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8355step0 raw8355; decide +kernel
      have hl : raw8355step0Labels = raw8355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8355 raw8355Labels permutation346 hz
    mixedMoment B raw8355step0 raw8355step0Labels = mixedMoment B raw8355step1 raw8355step1Labels := by
      have hz : ∀ j, raw8355step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8355step1 = (fun i j => raw8355step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8355step1 raw8355step0; decide +kernel
      have hl : raw8355step1Labels = raw8355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8355step0 raw8355step0Labels permutation56 hz
    mixedMoment B raw8355step1 raw8355step1Labels = mixedMoment B raw8355step2 raw8355step2Labels := by
      have ha : raw8355step2 = (fun i j => raw8355step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8355step2 raw8355step1; decide +kernel
      have hl : raw8355step2Labels = raw8355step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8355step1 raw8355step1Labels permutation10 permutation2
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw8356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8356step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8356 raw8356Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw8356 raw8356Labels = mixedMoment B raw8356step0 raw8356step0Labels := by
      have hz : ∀ j, raw8356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8356step0 = (fun i j => raw8356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8356step0 raw8356; decide +kernel
      have hl : raw8356step0Labels = raw8356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8356 raw8356Labels permutation346 hz
    mixedMoment B raw8356step0 raw8356step0Labels = mixedMoment B raw8356step1 raw8356step1Labels := by
      have ha : raw8356step1 = (fun i j => raw8356step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8356step1 raw8356step0; decide +kernel
      have hl : raw8356step1Labels = raw8356step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8356step0 raw8356step0Labels permutation101 permutation6
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw8357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8357 raw8357Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw8357 raw8357Labels = mixedMoment B raw8357step0 raw8357step0Labels := by
      have hz : ∀ j, raw8357 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8357step0 = (fun i j => raw8357 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8357step0 raw8357; decide +kernel
      have hl : raw8357step0Labels = raw8357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8357 raw8357Labels permutation265 hz
    mixedMoment B raw8357step0 raw8357step0Labels = mixedMoment B raw8357step1 raw8357step1Labels := by
      have ha : raw8357step1 = (fun i j => raw8357step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8357step1 raw8357step0; decide +kernel
      have hl : raw8357step1Labels = raw8357step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8357step0 raw8357step0Labels permutation101 permutation6
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw8358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8358step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8358step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8358 raw8358Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw8358 raw8358Labels = mixedMoment B raw8358step0 raw8358step0Labels := by
      have hz : ∀ j, raw8358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8358step0 = (fun i j => raw8358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8358step0 raw8358; decide +kernel
      have hl : raw8358step0Labels = raw8358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8358 raw8358Labels permutation346 hz
    mixedMoment B raw8358step0 raw8358step0Labels = mixedMoment B raw8358step1 raw8358step1Labels := by
      have hz : ∀ j, raw8358step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8358step1 = (fun i j => raw8358step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8358step1 raw8358step0; decide +kernel
      have hl : raw8358step1Labels = raw8358step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8358step0 raw8358step0Labels permutation56 hz
    mixedMoment B raw8358step1 raw8358step1Labels = mixedMoment B raw8358step2 raw8358step2Labels := by
      have ha : raw8358step2 = (fun i j => raw8358step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8358step2 raw8358step1; decide +kernel
      have hl : raw8358step2Labels = raw8358step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8358step1 raw8358step1Labels permutation19 permutation6
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw8359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8359step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8359step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8359step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8359 raw8359Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw8359 raw8359Labels = mixedMoment B raw8359step0 raw8359step0Labels := by
      have hz : ∀ j, raw8359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8359step0 = (fun i j => raw8359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8359step0 raw8359; decide +kernel
      have hl : raw8359step0Labels = raw8359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8359 raw8359Labels permutation346 hz
    mixedMoment B raw8359step0 raw8359step0Labels = mixedMoment B raw8359step1 raw8359step1Labels := by
      have hz : ∀ j, raw8359step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8359step1 = (fun i j => raw8359step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8359step1 raw8359step0; decide +kernel
      have hl : raw8359step1Labels = raw8359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8359step0 raw8359step0Labels permutation56 hz
    mixedMoment B raw8359step1 raw8359step1Labels = mixedMoment B raw8359step2 raw8359step2Labels := by
      have ha : raw8359step2 = (fun i j => raw8359step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8359step2 raw8359step1; decide +kernel
      have hl : raw8359step2Labels = raw8359step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8359step1 raw8359step1Labels permutation19 permutation6
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw8360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8360step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8360step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8360step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8360 raw8360Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw8360 raw8360Labels = mixedMoment B raw8360step0 raw8360step0Labels := by
      have hz : ∀ j, raw8360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8360step0 = (fun i j => raw8360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8360step0 raw8360; decide +kernel
      have hl : raw8360step0Labels = raw8360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8360 raw8360Labels permutation346 hz
    mixedMoment B raw8360step0 raw8360step0Labels = mixedMoment B raw8360step1 raw8360step1Labels := by
      have hz : ∀ j, raw8360step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8360step1 = (fun i j => raw8360step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8360step1 raw8360step0; decide +kernel
      have hl : raw8360step1Labels = raw8360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8360step0 raw8360step0Labels permutation56 hz
    mixedMoment B raw8360step1 raw8360step1Labels = mixedMoment B raw8360step2 raw8360step2Labels := by
      have ha : raw8360step2 = (fun i j => raw8360step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8360step2 raw8360step1; decide +kernel
      have hl : raw8360step2Labels = raw8360step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8360step1 raw8360step1Labels permutation19 permutation6
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw8361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8361 raw8361Labels = mixedMoment B node1189 node1189Labels := by
  calc
    mixedMoment B raw8361 raw8361Labels = mixedMoment B raw8361step0 raw8361step0Labels := by
      have hz : ∀ j, raw8361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8361step0 = (fun i j => raw8361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8361step0 raw8361; decide +kernel
      have hl : raw8361step0Labels = raw8361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8361 raw8361Labels permutation346 hz
    mixedMoment B raw8361step0 raw8361step0Labels = mixedMoment B raw8361step1 raw8361step1Labels := by
      have ha : raw8361step1 = (fun i j => raw8361step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8361step1 raw8361step0; decide +kernel
      have hl : raw8361step1Labels = raw8361step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8361step0 raw8361step0Labels permutation38 permutation3
    _ = mixedMoment B node1189 node1189Labels := by rfl

def raw8362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8362 raw8362Labels = mixedMoment B node2909 node2909Labels := by
  calc
    mixedMoment B raw8362 raw8362Labels = mixedMoment B raw8362step0 raw8362step0Labels := by
      have ha : raw8362step0 = (fun i j => raw8362 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8362step0 raw8362; decide +kernel
      have hl : raw8362step0Labels = raw8362Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8362 raw8362Labels permutation182 permutation3
    _ = mixedMoment B node2909 node2909Labels := by rfl

def raw8363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8363 raw8363Labels = mixedMoment B node2841 node2841Labels := by
  calc
    mixedMoment B raw8363 raw8363Labels = mixedMoment B raw8363step0 raw8363step0Labels := by
      have hz : ∀ j, raw8363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8363step0 = (fun i j => raw8363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8363step0 raw8363; decide +kernel
      have hl : raw8363step0Labels = raw8363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8363 raw8363Labels permutation346 hz
    mixedMoment B raw8363step0 raw8363step0Labels = mixedMoment B raw8363step1 raw8363step1Labels := by
      have ha : raw8363step1 = (fun i j => raw8363step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8363step1 raw8363step0; decide +kernel
      have hl : raw8363step1Labels = raw8363step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8363step0 raw8363step0Labels permutation38 permutation3
    _ = mixedMoment B node2841 node2841Labels := by rfl

def raw8364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8364 raw8364Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw8364 raw8364Labels = mixedMoment B raw8364step0 raw8364step0Labels := by
      have hz : ∀ j, raw8364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8364step0 = (fun i j => raw8364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8364step0 raw8364; decide +kernel
      have hl : raw8364step0Labels = raw8364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8364 raw8364Labels permutation346 hz
    mixedMoment B raw8364step0 raw8364step0Labels = mixedMoment B raw8364step1 raw8364step1Labels := by
      have ha : raw8364step1 = (fun i j => raw8364step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8364step1 raw8364step0; decide +kernel
      have hl : raw8364step1Labels = raw8364step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8364step0 raw8364step0Labels permutation40 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw8365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8365 raw8365Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw8365 raw8365Labels = mixedMoment B raw8365step0 raw8365step0Labels := by
      have hz : ∀ j, raw8365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8365step0 = (fun i j => raw8365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8365step0 raw8365; decide +kernel
      have hl : raw8365step0Labels = raw8365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8365 raw8365Labels permutation346 hz
    mixedMoment B raw8365step0 raw8365step0Labels = mixedMoment B raw8365step1 raw8365step1Labels := by
      have ha : raw8365step1 = (fun i j => raw8365step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8365step1 raw8365step0; decide +kernel
      have hl : raw8365step1Labels = raw8365step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8365step0 raw8365step0Labels permutation42 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw8366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8366 raw8366Labels = mixedMoment B node1189 node1189Labels := by
  calc
    mixedMoment B raw8366 raw8366Labels = mixedMoment B raw8366step0 raw8366step0Labels := by
      have hz : ∀ j, raw8366 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8366step0 = (fun i j => raw8366 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8366step0 raw8366; decide +kernel
      have hl : raw8366step0Labels = raw8366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8366 raw8366Labels permutation265 hz
    mixedMoment B raw8366step0 raw8366step0Labels = mixedMoment B raw8366step1 raw8366step1Labels := by
      have ha : raw8366step1 = (fun i j => raw8366step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8366step1 raw8366step0; decide +kernel
      have hl : raw8366step1Labels = raw8366step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8366step0 raw8366step0Labels permutation38 permutation3
    _ = mixedMoment B node1189 node1189Labels := by rfl

def raw8367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8367 raw8367Labels = mixedMoment B node2909 node2909Labels := by
  calc
    mixedMoment B raw8367 raw8367Labels = mixedMoment B raw8367step0 raw8367step0Labels := by
      have ha : raw8367step0 = (fun i j => raw8367 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8367step0 raw8367; decide +kernel
      have hl : raw8367step0Labels = raw8367Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8367 raw8367Labels permutation158 permutation3
    _ = mixedMoment B node2909 node2909Labels := by rfl

def raw8368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8368 raw8368Labels = mixedMoment B node2841 node2841Labels := by
  calc
    mixedMoment B raw8368 raw8368Labels = mixedMoment B raw8368step0 raw8368step0Labels := by
      have hz : ∀ j, raw8368 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8368step0 = (fun i j => raw8368 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8368step0 raw8368; decide +kernel
      have hl : raw8368step0Labels = raw8368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8368 raw8368Labels permutation265 hz
    mixedMoment B raw8368step0 raw8368step0Labels = mixedMoment B raw8368step1 raw8368step1Labels := by
      have ha : raw8368step1 = (fun i j => raw8368step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8368step1 raw8368step0; decide +kernel
      have hl : raw8368step1Labels = raw8368step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8368step0 raw8368step0Labels permutation38 permutation3
    _ = mixedMoment B node2841 node2841Labels := by rfl

def raw8369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8369 raw8369Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw8369 raw8369Labels = mixedMoment B raw8369step0 raw8369step0Labels := by
      have hz : ∀ j, raw8369 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8369step0 = (fun i j => raw8369 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8369step0 raw8369; decide +kernel
      have hl : raw8369step0Labels = raw8369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8369 raw8369Labels permutation265 hz
    mixedMoment B raw8369step0 raw8369step0Labels = mixedMoment B raw8369step1 raw8369step1Labels := by
      have ha : raw8369step1 = (fun i j => raw8369step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8369step1 raw8369step0; decide +kernel
      have hl : raw8369step1Labels = raw8369step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8369step0 raw8369step0Labels permutation40 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw8370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8370 raw8370Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw8370 raw8370Labels = mixedMoment B raw8370step0 raw8370step0Labels := by
      have hz : ∀ j, raw8370 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8370step0 = (fun i j => raw8370 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8370step0 raw8370; decide +kernel
      have hl : raw8370step0Labels = raw8370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8370 raw8370Labels permutation265 hz
    mixedMoment B raw8370step0 raw8370step0Labels = mixedMoment B raw8370step1 raw8370step1Labels := by
      have ha : raw8370step1 = (fun i j => raw8370step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8370step1 raw8370step0; decide +kernel
      have hl : raw8370step1Labels = raw8370step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8370step0 raw8370step0Labels permutation42 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw8371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8371step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8371 raw8371Labels = mixedMoment B node1295 node1295Labels := by
  calc
    mixedMoment B raw8371 raw8371Labels = mixedMoment B raw8371step0 raw8371step0Labels := by
      have hz : ∀ j, raw8371 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8371step0 = (fun i j => raw8371 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8371step0 raw8371; decide +kernel
      have hl : raw8371step0Labels = raw8371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8371 raw8371Labels permutation346 hz
    mixedMoment B raw8371step0 raw8371step0Labels = mixedMoment B raw8371step1 raw8371step1Labels := by
      have hz : ∀ j, raw8371step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8371step1 = (fun i j => raw8371step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8371step1 raw8371step0; decide +kernel
      have hl : raw8371step1Labels = raw8371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8371step0 raw8371step0Labels permutation56 hz
    mixedMoment B raw8371step1 raw8371step1Labels = mixedMoment B raw8371step2 raw8371step2Labels := by
      have ha : raw8371step2 = (fun i j => raw8371step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8371step2 raw8371step1; decide +kernel
      have hl : raw8371step2Labels = raw8371step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8371step1 raw8371step1Labels permutation8 permutation3
    _ = mixedMoment B node1295 node1295Labels := by rfl

def raw8372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8372 raw8372Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw8372 raw8372Labels = mixedMoment B raw8372step0 raw8372step0Labels := by
      have hz : ∀ j, raw8372 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8372step0 = (fun i j => raw8372 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8372step0 raw8372; decide +kernel
      have hl : raw8372step0Labels = raw8372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8372 raw8372Labels permutation346 hz
    mixedMoment B raw8372step0 raw8372step0Labels = mixedMoment B raw8372step1 raw8372step1Labels := by
      have ha : raw8372step1 = (fun i j => raw8372step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8372step1 raw8372step0; decide +kernel
      have hl : raw8372step1Labels = raw8372step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8372step0 raw8372step0Labels permutation32 permutation3
    _ = mixedMoment B node2955 node2955Labels := by rfl

def raw8373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8373 raw8373Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw8373 raw8373Labels = mixedMoment B raw8373step0 raw8373step0Labels := by
      have hz : ∀ j, raw8373 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8373step0 = (fun i j => raw8373 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8373step0 raw8373; decide +kernel
      have hl : raw8373step0Labels = raw8373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8373 raw8373Labels permutation265 hz
    mixedMoment B raw8373step0 raw8373step0Labels = mixedMoment B raw8373step1 raw8373step1Labels := by
      have ha : raw8373step1 = (fun i j => raw8373step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8373step1 raw8373step0; decide +kernel
      have hl : raw8373step1Labels = raw8373step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8373step0 raw8373step0Labels permutation32 permutation3
    _ = mixedMoment B node2955 node2955Labels := by rfl

def raw8374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8374step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8374 raw8374Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw8374 raw8374Labels = mixedMoment B raw8374step0 raw8374step0Labels := by
      have hz : ∀ j, raw8374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8374step0 = (fun i j => raw8374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8374step0 raw8374; decide +kernel
      have hl : raw8374step0Labels = raw8374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8374 raw8374Labels permutation346 hz
    mixedMoment B raw8374step0 raw8374step0Labels = mixedMoment B raw8374step1 raw8374step1Labels := by
      have hz : ∀ j, raw8374step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8374step1 = (fun i j => raw8374step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8374step1 raw8374step0; decide +kernel
      have hl : raw8374step1Labels = raw8374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8374step0 raw8374step0Labels permutation56 hz
    mixedMoment B raw8374step1 raw8374step1Labels = mixedMoment B raw8374step2 raw8374step2Labels := by
      have ha : raw8374step2 = (fun i j => raw8374step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8374step2 raw8374step1; decide +kernel
      have hl : raw8374step2Labels = raw8374step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8374step1 raw8374step1Labels permutation10 permutation3
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw8375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8375 raw8375Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw8375 raw8375Labels = mixedMoment B raw8375step0 raw8375step0Labels := by
      have hz : ∀ j, raw8375 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8375step0 = (fun i j => raw8375 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8375step0 raw8375; decide +kernel
      have hl : raw8375step0Labels = raw8375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8375 raw8375Labels permutation346 hz
    mixedMoment B raw8375step0 raw8375step0Labels = mixedMoment B raw8375step1 raw8375step1Labels := by
      have hz : ∀ j, raw8375step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8375step1 = (fun i j => raw8375step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8375step1 raw8375step0; decide +kernel
      have hl : raw8375step1Labels = raw8375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8375step0 raw8375step0Labels permutation56 hz
    mixedMoment B raw8375step1 raw8375step1Labels = mixedMoment B raw8375step2 raw8375step2Labels := by
      have ha : raw8375step2 = (fun i j => raw8375step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8375step2 raw8375step1; decide +kernel
      have hl : raw8375step2Labels = raw8375step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8375step1 raw8375step1Labels permutation9 permutation3
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw8376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8376step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8376step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw8376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8376 raw8376Labels = mixedMoment B node1192 node1192Labels := by
  calc
    mixedMoment B raw8376 raw8376Labels = mixedMoment B raw8376step0 raw8376step0Labels := by
      have hz : ∀ j, raw8376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8376step0 = (fun i j => raw8376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8376step0 raw8376; decide +kernel
      have hl : raw8376step0Labels = raw8376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8376 raw8376Labels permutation346 hz
    mixedMoment B raw8376step0 raw8376step0Labels = mixedMoment B raw8376step1 raw8376step1Labels := by
      have hz : ∀ j, raw8376step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8376step1 = (fun i j => raw8376step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8376step1 raw8376step0; decide +kernel
      have hl : raw8376step1Labels = raw8376step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8376step0 raw8376step0Labels permutation56 hz
    mixedMoment B raw8376step1 raw8376step1Labels = mixedMoment B raw8376step2 raw8376step2Labels := by
      have ha : raw8376step2 = (fun i j => raw8376step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8376step2 raw8376step1; decide +kernel
      have hl : raw8376step2Labels = raw8376step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8376step1 raw8376step1Labels permutation9 permutation3
    _ = mixedMoment B node1192 node1192Labels := by rfl

def raw8377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw8377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8377 raw8377Labels = mixedMoment B node2910 node2910Labels := by
  calc
    mixedMoment B raw8377 raw8377Labels = mixedMoment B raw8377step0 raw8377step0Labels := by
      have hz : ∀ j, raw8377 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8377step0 = (fun i j => raw8377 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8377step0 raw8377; decide +kernel
      have hl : raw8377step0Labels = raw8377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8377 raw8377Labels permutation346 hz
    mixedMoment B raw8377step0 raw8377step0Labels = mixedMoment B raw8377step1 raw8377step1Labels := by
      have ha : raw8377step1 = (fun i j => raw8377step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8377step1 raw8377step0; decide +kernel
      have hl : raw8377step1Labels = raw8377step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8377step0 raw8377step0Labels permutation33 permutation3
    _ = mixedMoment B node2910 node2910Labels := by rfl

def raw8378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8378step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw8378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8378 raw8378Labels = mixedMoment B node2910 node2910Labels := by
  calc
    mixedMoment B raw8378 raw8378Labels = mixedMoment B raw8378step0 raw8378step0Labels := by
      have hz : ∀ j, raw8378 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8378step0 = (fun i j => raw8378 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8378step0 raw8378; decide +kernel
      have hl : raw8378step0Labels = raw8378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8378 raw8378Labels permutation265 hz
    mixedMoment B raw8378step0 raw8378step0Labels = mixedMoment B raw8378step1 raw8378step1Labels := by
      have ha : raw8378step1 = (fun i j => raw8378step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8378step1 raw8378step0; decide +kernel
      have hl : raw8378step1Labels = raw8378step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8378step0 raw8378step0Labels permutation33 permutation3
    _ = mixedMoment B node2910 node2910Labels := by rfl

def raw8379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8379step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw8379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8379 raw8379Labels = mixedMoment B node2842 node2842Labels := by
  calc
    mixedMoment B raw8379 raw8379Labels = mixedMoment B raw8379step0 raw8379step0Labels := by
      have hz : ∀ j, raw8379 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8379step0 = (fun i j => raw8379 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8379step0 raw8379; decide +kernel
      have hl : raw8379step0Labels = raw8379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8379 raw8379Labels permutation346 hz
    mixedMoment B raw8379step0 raw8379step0Labels = mixedMoment B raw8379step1 raw8379step1Labels := by
      have hz : ∀ j, raw8379step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8379step1 = (fun i j => raw8379step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8379step1 raw8379step0; decide +kernel
      have hl : raw8379step1Labels = raw8379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8379step0 raw8379step0Labels permutation56 hz
    mixedMoment B raw8379step1 raw8379step1Labels = mixedMoment B raw8379step2 raw8379step2Labels := by
      have ha : raw8379step2 = (fun i j => raw8379step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8379step2 raw8379step1; decide +kernel
      have hl : raw8379step2Labels = raw8379step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8379step1 raw8379step1Labels permutation9 permutation3
    _ = mixedMoment B node2842 node2842Labels := by rfl

def raw8380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8380step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8380step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw8380step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8380 raw8380Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw8380 raw8380Labels = mixedMoment B raw8380step0 raw8380step0Labels := by
      have hz : ∀ j, raw8380 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8380step0 = (fun i j => raw8380 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8380step0 raw8380; decide +kernel
      have hl : raw8380step0Labels = raw8380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8380 raw8380Labels permutation346 hz
    mixedMoment B raw8380step0 raw8380step0Labels = mixedMoment B raw8380step1 raw8380step1Labels := by
      have hz : ∀ j, raw8380step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8380step1 = (fun i j => raw8380step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8380step1 raw8380step0; decide +kernel
      have hl : raw8380step1Labels = raw8380step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8380step0 raw8380step0Labels permutation56 hz
    mixedMoment B raw8380step1 raw8380step1Labels = mixedMoment B raw8380step2 raw8380step2Labels := by
      have ha : raw8380step2 = (fun i j => raw8380step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8380step2 raw8380step1; decide +kernel
      have hl : raw8380step2Labels = raw8380step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8380step1 raw8380step1Labels permutation9 permutation3
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw8381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8381step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8381step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8381step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw8381step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8381 raw8381Labels = mixedMoment B node1191 node1191Labels := by
  calc
    mixedMoment B raw8381 raw8381Labels = mixedMoment B raw8381step0 raw8381step0Labels := by
      have hz : ∀ j, raw8381 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8381step0 = (fun i j => raw8381 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8381step0 raw8381; decide +kernel
      have hl : raw8381step0Labels = raw8381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8381 raw8381Labels permutation346 hz
    mixedMoment B raw8381step0 raw8381step0Labels = mixedMoment B raw8381step1 raw8381step1Labels := by
      have hz : ∀ j, raw8381step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8381step1 = (fun i j => raw8381step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8381step1 raw8381step0; decide +kernel
      have hl : raw8381step1Labels = raw8381step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8381step0 raw8381step0Labels permutation56 hz
    mixedMoment B raw8381step1 raw8381step1Labels = mixedMoment B raw8381step2 raw8381step2Labels := by
      have ha : raw8381step2 = (fun i j => raw8381step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8381step2 raw8381step1; decide +kernel
      have hl : raw8381step2Labels = raw8381step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8381step1 raw8381step1Labels permutation8 permutation3
    _ = mixedMoment B node1191 node1191Labels := by rfl

def raw8382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw8382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8382 raw8382Labels = mixedMoment B node2393 node2393Labels := by
  calc
    mixedMoment B raw8382 raw8382Labels = mixedMoment B raw8382step0 raw8382step0Labels := by
      have hz : ∀ j, raw8382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8382step0 = (fun i j => raw8382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8382step0 raw8382; decide +kernel
      have hl : raw8382step0Labels = raw8382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8382 raw8382Labels permutation346 hz
    mixedMoment B raw8382step0 raw8382step0Labels = mixedMoment B raw8382step1 raw8382step1Labels := by
      have ha : raw8382step1 = (fun i j => raw8382step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8382step1 raw8382step0; decide +kernel
      have hl : raw8382step1Labels = raw8382step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8382step0 raw8382step0Labels permutation151 permutation3
    mixedMoment B raw8382step1 raw8382step1Labels = mixedMoment B raw8382step2 raw8382step2Labels := by
      have ha : raw8382step2 = -raw8382step1 := by apply Matrix.ext; change ∀ i j, raw8382step2 i j = -(raw8382step1 i j); unfold raw8382step2 raw8382step1; decide +kernel
      have hl : raw8382step2Labels = raw8382step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2393 node2393Labels := by rfl

def raw8383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw8383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8383step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8383step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8383 raw8383Labels = mixedMoment B node2393 node2393Labels := by
  calc
    mixedMoment B raw8383 raw8383Labels = mixedMoment B raw8383step0 raw8383step0Labels := by
      have hz : ∀ j, raw8383 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8383step0 = (fun i j => raw8383 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8383step0 raw8383; decide +kernel
      have hl : raw8383step0Labels = raw8383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8383 raw8383Labels permutation265 hz
    mixedMoment B raw8383step0 raw8383step0Labels = mixedMoment B raw8383step1 raw8383step1Labels := by
      have ha : raw8383step1 = (fun i j => raw8383step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8383step1 raw8383step0; decide +kernel
      have hl : raw8383step1Labels = raw8383step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8383step0 raw8383step0Labels permutation151 permutation3
    mixedMoment B raw8383step1 raw8383step1Labels = mixedMoment B raw8383step2 raw8383step2Labels := by
      have ha : raw8383step2 = -raw8383step1 := by apply Matrix.ext; change ∀ i j, raw8383step2 i j = -(raw8383step1 i j); unfold raw8383step2 raw8383step1; decide +kernel
      have hl : raw8383step2Labels = raw8383step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2393 node2393Labels := by rfl

def raw8384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8384step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, -2, 3], ![-3, 2, 1]]
def raw8384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8384step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw8384step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8384 raw8384Labels = mixedMoment B node2408 node2408Labels := by
  calc
    mixedMoment B raw8384 raw8384Labels = mixedMoment B raw8384step0 raw8384step0Labels := by
      have hz : ∀ j, raw8384 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8384step0 = (fun i j => raw8384 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8384step0 raw8384; decide +kernel
      have hl : raw8384step0Labels = raw8384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8384 raw8384Labels permutation346 hz
    mixedMoment B raw8384step0 raw8384step0Labels = mixedMoment B raw8384step1 raw8384step1Labels := by
      have hz : ∀ j, raw8384step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8384step1 = (fun i j => raw8384step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8384step1 raw8384step0; decide +kernel
      have hl : raw8384step1Labels = raw8384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8384step0 raw8384step0Labels permutation56 hz
    mixedMoment B raw8384step1 raw8384step1Labels = mixedMoment B raw8384step2 raw8384step2Labels := by
      have ha : raw8384step2 = (fun i j => raw8384step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8384step2 raw8384step1; decide +kernel
      have hl : raw8384step2Labels = raw8384step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8384step1 raw8384step1Labels permutation31 permutation3
    mixedMoment B raw8384step2 raw8384step2Labels = mixedMoment B raw8384step3 raw8384step3Labels := by
      have ha : raw8384step3 = -raw8384step2 := by apply Matrix.ext; change ∀ i j, raw8384step3 i j = -(raw8384step2 i j); unfold raw8384step3 raw8384step2; decide +kernel
      have hl : raw8384step3Labels = raw8384step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2408 node2408Labels := by rfl

def raw8385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8385step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8385step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw8385step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8385step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8385step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8385 raw8385Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw8385 raw8385Labels = mixedMoment B raw8385step0 raw8385step0Labels := by
      have hz : ∀ j, raw8385 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8385step0 = (fun i j => raw8385 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8385step0 raw8385; decide +kernel
      have hl : raw8385step0Labels = raw8385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8385 raw8385Labels permutation346 hz
    mixedMoment B raw8385step0 raw8385step0Labels = mixedMoment B raw8385step1 raw8385step1Labels := by
      have hz : ∀ j, raw8385step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8385step1 = (fun i j => raw8385step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8385step1 raw8385step0; decide +kernel
      have hl : raw8385step1Labels = raw8385step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8385step0 raw8385step0Labels permutation56 hz
    mixedMoment B raw8385step1 raw8385step1Labels = mixedMoment B raw8385step2 raw8385step2Labels := by
      have ha : raw8385step2 = (fun i j => raw8385step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8385step2 raw8385step1; decide +kernel
      have hl : raw8385step2Labels = raw8385step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8385step1 raw8385step1Labels permutation31 permutation3
    mixedMoment B raw8385step2 raw8385step2Labels = mixedMoment B raw8385step3 raw8385step3Labels := by
      have ha : raw8385step3 = -raw8385step2 := by apply Matrix.ext; change ∀ i j, raw8385step3 i j = -(raw8385step2 i j); unfold raw8385step3 raw8385step2; decide +kernel
      have hl : raw8385step3Labels = raw8385step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw8386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8386Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8386step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8386step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8386step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8386step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8386step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8386 raw8386Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw8386 raw8386Labels = mixedMoment B raw8386step0 raw8386step0Labels := by
      have hz : ∀ j, raw8386 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8386step0 = (fun i j => raw8386 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8386step0 raw8386; decide +kernel
      have hl : raw8386step0Labels = raw8386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8386 raw8386Labels permutation346 hz
    mixedMoment B raw8386step0 raw8386step0Labels = mixedMoment B raw8386step1 raw8386step1Labels := by
      have ha : raw8386step1 = (fun i j => raw8386step0 (permutation45 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8386step1 raw8386step0; decide +kernel
      have hl : raw8386step1Labels = raw8386step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8386step0 raw8386step0Labels permutation45 permutation7
    mixedMoment B raw8386step1 raw8386step1Labels = mixedMoment B raw8386step2 raw8386step2Labels := by
      have ha : raw8386step2 = -raw8386step1 := by apply Matrix.ext; change ∀ i j, raw8386step2 i j = -(raw8386step1 i j); unfold raw8386step2 raw8386step1; decide +kernel
      have hl : raw8386step2Labels = raw8386step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8386step2 raw8386step2Labels = mixedMoment B raw8386step3 raw8386step3Labels := by
      have ha : raw8386step3 = raw8386step2 := by apply Matrix.ext; unfold raw8386step3 raw8386step2; decide +kernel
      have hl : raw8386step2Labels = labelEmbedding1 ∘ raw8386step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8386step2 raw8386step2Labels raw8386step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw8387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8387Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8387step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8387step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8387step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8387step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8387step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8387step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8387 raw8387Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw8387 raw8387Labels = mixedMoment B raw8387step0 raw8387step0Labels := by
      have hz : ∀ j, raw8387 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8387step0 = (fun i j => raw8387 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8387step0 raw8387; decide +kernel
      have hl : raw8387step0Labels = raw8387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8387 raw8387Labels permutation265 hz
    mixedMoment B raw8387step0 raw8387step0Labels = mixedMoment B raw8387step1 raw8387step1Labels := by
      have ha : raw8387step1 = (fun i j => raw8387step0 (permutation45 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8387step1 raw8387step0; decide +kernel
      have hl : raw8387step1Labels = raw8387step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8387step0 raw8387step0Labels permutation45 permutation7
    mixedMoment B raw8387step1 raw8387step1Labels = mixedMoment B raw8387step2 raw8387step2Labels := by
      have ha : raw8387step2 = -raw8387step1 := by apply Matrix.ext; change ∀ i j, raw8387step2 i j = -(raw8387step1 i j); unfold raw8387step2 raw8387step1; decide +kernel
      have hl : raw8387step2Labels = raw8387step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8387step2 raw8387step2Labels = mixedMoment B raw8387step3 raw8387step3Labels := by
      have ha : raw8387step3 = raw8387step2 := by apply Matrix.ext; unfold raw8387step3 raw8387step2; decide +kernel
      have hl : raw8387step2Labels = labelEmbedding1 ∘ raw8387step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8387step2 raw8387step2Labels raw8387step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw8388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8388Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8388step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8388step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw8388step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8388step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8388step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8388step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8388step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8388 raw8388Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw8388 raw8388Labels = mixedMoment B raw8388step0 raw8388step0Labels := by
      have hz : ∀ j, raw8388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8388step0 = (fun i j => raw8388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8388step0 raw8388; decide +kernel
      have hl : raw8388step0Labels = raw8388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8388 raw8388Labels permutation346 hz
    mixedMoment B raw8388step0 raw8388step0Labels = mixedMoment B raw8388step1 raw8388step1Labels := by
      have hz : ∀ j, raw8388step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8388step1 = (fun i j => raw8388step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8388step1 raw8388step0; decide +kernel
      have hl : raw8388step1Labels = raw8388step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8388step0 raw8388step0Labels permutation56 hz
    mixedMoment B raw8388step1 raw8388step1Labels = mixedMoment B raw8388step2 raw8388step2Labels := by
      have ha : raw8388step2 = (fun i j => raw8388step1 (permutation15 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8388step2 raw8388step1; decide +kernel
      have hl : raw8388step2Labels = raw8388step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8388step1 raw8388step1Labels permutation15 permutation5
    mixedMoment B raw8388step2 raw8388step2Labels = mixedMoment B raw8388step3 raw8388step3Labels := by
      have ha : raw8388step3 = -raw8388step2 := by apply Matrix.ext; change ∀ i j, raw8388step3 i j = -(raw8388step2 i j); unfold raw8388step3 raw8388step2; decide +kernel
      have hl : raw8388step3Labels = raw8388step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8388step3 raw8388step3Labels = mixedMoment B raw8388step4 raw8388step4Labels := by
      have ha : raw8388step4 = raw8388step3 := by apply Matrix.ext; unfold raw8388step4 raw8388step3; decide +kernel
      have hl : raw8388step3Labels = labelEmbedding1 ∘ raw8388step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8388step3 raw8388step3Labels raw8388step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw8389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8389Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8389step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8389step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw8389step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8389step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8389step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8389step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8389step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8389 raw8389Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw8389 raw8389Labels = mixedMoment B raw8389step0 raw8389step0Labels := by
      have hz : ∀ j, raw8389 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8389step0 = (fun i j => raw8389 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8389step0 raw8389; decide +kernel
      have hl : raw8389step0Labels = raw8389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8389 raw8389Labels permutation346 hz
    mixedMoment B raw8389step0 raw8389step0Labels = mixedMoment B raw8389step1 raw8389step1Labels := by
      have hz : ∀ j, raw8389step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8389step1 = (fun i j => raw8389step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8389step1 raw8389step0; decide +kernel
      have hl : raw8389step1Labels = raw8389step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8389step0 raw8389step0Labels permutation56 hz
    mixedMoment B raw8389step1 raw8389step1Labels = mixedMoment B raw8389step2 raw8389step2Labels := by
      have ha : raw8389step2 = (fun i j => raw8389step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8389step2 raw8389step1; decide +kernel
      have hl : raw8389step2Labels = raw8389step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8389step1 raw8389step1Labels permutation11 permutation7
    mixedMoment B raw8389step2 raw8389step2Labels = mixedMoment B raw8389step3 raw8389step3Labels := by
      have ha : raw8389step3 = -raw8389step2 := by apply Matrix.ext; change ∀ i j, raw8389step3 i j = -(raw8389step2 i j); unfold raw8389step3 raw8389step2; decide +kernel
      have hl : raw8389step3Labels = raw8389step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8389step3 raw8389step3Labels = mixedMoment B raw8389step4 raw8389step4Labels := by
      have ha : raw8389step4 = raw8389step3 := by apply Matrix.ext; unfold raw8389step4 raw8389step3; decide +kernel
      have hl : raw8389step3Labels = labelEmbedding1 ∘ raw8389step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8389step3 raw8389step3Labels raw8389step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw8390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8390Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8390step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8390step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8390step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8390step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8390step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8390step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8390step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8390 raw8390Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw8390 raw8390Labels = mixedMoment B raw8390step0 raw8390step0Labels := by
      have hz : ∀ j, raw8390 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8390step0 = (fun i j => raw8390 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8390step0 raw8390; decide +kernel
      have hl : raw8390step0Labels = raw8390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8390 raw8390Labels permutation346 hz
    mixedMoment B raw8390step0 raw8390step0Labels = mixedMoment B raw8390step1 raw8390step1Labels := by
      have hz : ∀ j, raw8390step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8390step1 = (fun i j => raw8390step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8390step1 raw8390step0; decide +kernel
      have hl : raw8390step1Labels = raw8390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8390step0 raw8390step0Labels permutation56 hz
    mixedMoment B raw8390step1 raw8390step1Labels = mixedMoment B raw8390step2 raw8390step2Labels := by
      have ha : raw8390step2 = (fun i j => raw8390step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8390step2 raw8390step1; decide +kernel
      have hl : raw8390step2Labels = raw8390step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8390step1 raw8390step1Labels permutation11 permutation7
    mixedMoment B raw8390step2 raw8390step2Labels = mixedMoment B raw8390step3 raw8390step3Labels := by
      have ha : raw8390step3 = -raw8390step2 := by apply Matrix.ext; change ∀ i j, raw8390step3 i j = -(raw8390step2 i j); unfold raw8390step3 raw8390step2; decide +kernel
      have hl : raw8390step3Labels = raw8390step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8390step3 raw8390step3Labels = mixedMoment B raw8390step4 raw8390step4Labels := by
      have ha : raw8390step4 = raw8390step3 := by apply Matrix.ext; unfold raw8390step4 raw8390step3; decide +kernel
      have hl : raw8390step3Labels = labelEmbedding1 ∘ raw8390step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8390step3 raw8390step3Labels raw8390step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw8391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8391Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8391step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8391step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8391step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8391step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8391step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8391 raw8391Labels = mixedMoment B node3246 node3246Labels := by
  calc
    mixedMoment B raw8391 raw8391Labels = mixedMoment B raw8391step0 raw8391step0Labels := by
      have hz : ∀ j, raw8391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8391step0 = (fun i j => raw8391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8391step0 raw8391; decide +kernel
      have hl : raw8391step0Labels = raw8391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8391 raw8391Labels permutation346 hz
    mixedMoment B raw8391step0 raw8391step0Labels = mixedMoment B raw8391step1 raw8391step1Labels := by
      have ha : raw8391step1 = (fun i j => raw8391step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8391step1 raw8391step0; decide +kernel
      have hl : raw8391step1Labels = raw8391step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8391step0 raw8391step0Labels permutation39 permutation5
    mixedMoment B raw8391step1 raw8391step1Labels = mixedMoment B raw8391step2 raw8391step2Labels := by
      have ha : raw8391step2 = -raw8391step1 := by apply Matrix.ext; change ∀ i j, raw8391step2 i j = -(raw8391step1 i j); unfold raw8391step2 raw8391step1; decide +kernel
      have hl : raw8391step2Labels = raw8391step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8391step2 raw8391step2Labels = mixedMoment B raw8391step3 raw8391step3Labels := by
      have ha : raw8391step3 = raw8391step2 := by apply Matrix.ext; unfold raw8391step3 raw8391step2; decide +kernel
      have hl : raw8391step2Labels = labelEmbedding1 ∘ raw8391step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8391step2 raw8391step2Labels raw8391step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3246 node3246Labels := by rfl

def raw8392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8392step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8392step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8392step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8392 raw8392Labels = mixedMoment B node3559 node3559Labels := by
  calc
    mixedMoment B raw8392 raw8392Labels = mixedMoment B raw8392step0 raw8392step0Labels := by
      have ha : raw8392step0 = (fun i j => raw8392 (permutation231 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8392step0 raw8392; decide +kernel
      have hl : raw8392step0Labels = raw8392Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8392 raw8392Labels permutation231 permutation7
    mixedMoment B raw8392step0 raw8392step0Labels = mixedMoment B raw8392step1 raw8392step1Labels := by
      have ha : raw8392step1 = -raw8392step0 := by apply Matrix.ext; change ∀ i j, raw8392step1 i j = -(raw8392step0 i j); unfold raw8392step1 raw8392step0; decide +kernel
      have hl : raw8392step1Labels = raw8392step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8392step1 raw8392step1Labels = mixedMoment B raw8392step2 raw8392step2Labels := by
      have ha : raw8392step2 = raw8392step1 := by apply Matrix.ext; unfold raw8392step2 raw8392step1; decide +kernel
      have hl : raw8392step1Labels = labelEmbedding1 ∘ raw8392step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8392step1 raw8392step1Labels raw8392step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3559 node3559Labels := by rfl

def raw8393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8393Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8393step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8393step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8393step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8393step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8393step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8393 raw8393Labels = mixedMoment B node2841 node2841Labels := by
  calc
    mixedMoment B raw8393 raw8393Labels = mixedMoment B raw8393step0 raw8393step0Labels := by
      have hz : ∀ j, raw8393 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8393step0 = (fun i j => raw8393 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8393step0 raw8393; decide +kernel
      have hl : raw8393step0Labels = raw8393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8393 raw8393Labels permutation346 hz
    mixedMoment B raw8393step0 raw8393step0Labels = mixedMoment B raw8393step1 raw8393step1Labels := by
      have ha : raw8393step1 = (fun i j => raw8393step0 (permutation81 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8393step1 raw8393step0; decide +kernel
      have hl : raw8393step1Labels = raw8393step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8393step0 raw8393step0Labels permutation81 permutation5
    mixedMoment B raw8393step1 raw8393step1Labels = mixedMoment B raw8393step2 raw8393step2Labels := by
      have ha : raw8393step2 = -raw8393step1 := by apply Matrix.ext; change ∀ i j, raw8393step2 i j = -(raw8393step1 i j); unfold raw8393step2 raw8393step1; decide +kernel
      have hl : raw8393step2Labels = raw8393step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8393step2 raw8393step2Labels = mixedMoment B raw8393step3 raw8393step3Labels := by
      have ha : raw8393step3 = raw8393step2 := by apply Matrix.ext; unfold raw8393step3 raw8393step2; decide +kernel
      have hl : raw8393step2Labels = labelEmbedding1 ∘ raw8393step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8393step2 raw8393step2Labels raw8393step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2841 node2841Labels := by rfl

def raw8394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8394Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8394step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8394step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8394step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8394step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8394step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8394 raw8394Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw8394 raw8394Labels = mixedMoment B raw8394step0 raw8394step0Labels := by
      have hz : ∀ j, raw8394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8394step0 = (fun i j => raw8394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8394step0 raw8394; decide +kernel
      have hl : raw8394step0Labels = raw8394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8394 raw8394Labels permutation346 hz
    mixedMoment B raw8394step0 raw8394step0Labels = mixedMoment B raw8394step1 raw8394step1Labels := by
      have ha : raw8394step1 = (fun i j => raw8394step0 (permutation45 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8394step1 raw8394step0; decide +kernel
      have hl : raw8394step1Labels = raw8394step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8394step0 raw8394step0Labels permutation45 permutation7
    mixedMoment B raw8394step1 raw8394step1Labels = mixedMoment B raw8394step2 raw8394step2Labels := by
      have ha : raw8394step2 = -raw8394step1 := by apply Matrix.ext; change ∀ i j, raw8394step2 i j = -(raw8394step1 i j); unfold raw8394step2 raw8394step1; decide +kernel
      have hl : raw8394step2Labels = raw8394step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8394step2 raw8394step2Labels = mixedMoment B raw8394step3 raw8394step3Labels := by
      have ha : raw8394step3 = raw8394step2 := by apply Matrix.ext; unfold raw8394step3 raw8394step2; decide +kernel
      have hl : raw8394step2Labels = labelEmbedding1 ∘ raw8394step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8394step2 raw8394step2Labels raw8394step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw8395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8395Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8395step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8395step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8395step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8395step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8395step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8395 raw8395Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw8395 raw8395Labels = mixedMoment B raw8395step0 raw8395step0Labels := by
      have hz : ∀ j, raw8395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8395step0 = (fun i j => raw8395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8395step0 raw8395; decide +kernel
      have hl : raw8395step0Labels = raw8395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8395 raw8395Labels permutation346 hz
    mixedMoment B raw8395step0 raw8395step0Labels = mixedMoment B raw8395step1 raw8395step1Labels := by
      have ha : raw8395step1 = (fun i j => raw8395step0 (permutation45 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8395step1 raw8395step0; decide +kernel
      have hl : raw8395step1Labels = raw8395step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8395step0 raw8395step0Labels permutation45 permutation7
    mixedMoment B raw8395step1 raw8395step1Labels = mixedMoment B raw8395step2 raw8395step2Labels := by
      have ha : raw8395step2 = -raw8395step1 := by apply Matrix.ext; change ∀ i j, raw8395step2 i j = -(raw8395step1 i j); unfold raw8395step2 raw8395step1; decide +kernel
      have hl : raw8395step2Labels = raw8395step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8395step2 raw8395step2Labels = mixedMoment B raw8395step3 raw8395step3Labels := by
      have ha : raw8395step3 = raw8395step2 := by apply Matrix.ext; unfold raw8395step3 raw8395step2; decide +kernel
      have hl : raw8395step2Labels = labelEmbedding1 ∘ raw8395step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8395step2 raw8395step2Labels raw8395step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw8396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8396Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8396step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8396step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8396step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8396step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8396step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8396 raw8396Labels = mixedMoment B node3246 node3246Labels := by
  calc
    mixedMoment B raw8396 raw8396Labels = mixedMoment B raw8396step0 raw8396step0Labels := by
      have hz : ∀ j, raw8396 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8396step0 = (fun i j => raw8396 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8396step0 raw8396; decide +kernel
      have hl : raw8396step0Labels = raw8396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8396 raw8396Labels permutation265 hz
    mixedMoment B raw8396step0 raw8396step0Labels = mixedMoment B raw8396step1 raw8396step1Labels := by
      have ha : raw8396step1 = (fun i j => raw8396step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8396step1 raw8396step0; decide +kernel
      have hl : raw8396step1Labels = raw8396step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8396step0 raw8396step0Labels permutation39 permutation5
    mixedMoment B raw8396step1 raw8396step1Labels = mixedMoment B raw8396step2 raw8396step2Labels := by
      have ha : raw8396step2 = -raw8396step1 := by apply Matrix.ext; change ∀ i j, raw8396step2 i j = -(raw8396step1 i j); unfold raw8396step2 raw8396step1; decide +kernel
      have hl : raw8396step2Labels = raw8396step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8396step2 raw8396step2Labels = mixedMoment B raw8396step3 raw8396step3Labels := by
      have ha : raw8396step3 = raw8396step2 := by apply Matrix.ext; unfold raw8396step3 raw8396step2; decide +kernel
      have hl : raw8396step2Labels = labelEmbedding1 ∘ raw8396step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8396step2 raw8396step2Labels raw8396step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3246 node3246Labels := by rfl

def raw8397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8397Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8397step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8397step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8397step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8397 raw8397Labels = mixedMoment B node3559 node3559Labels := by
  calc
    mixedMoment B raw8397 raw8397Labels = mixedMoment B raw8397step0 raw8397step0Labels := by
      have ha : raw8397step0 = (fun i j => raw8397 (permutation225 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8397step0 raw8397; decide +kernel
      have hl : raw8397step0Labels = raw8397Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8397 raw8397Labels permutation225 permutation7
    mixedMoment B raw8397step0 raw8397step0Labels = mixedMoment B raw8397step1 raw8397step1Labels := by
      have ha : raw8397step1 = -raw8397step0 := by apply Matrix.ext; change ∀ i j, raw8397step1 i j = -(raw8397step0 i j); unfold raw8397step1 raw8397step0; decide +kernel
      have hl : raw8397step1Labels = raw8397step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8397step1 raw8397step1Labels = mixedMoment B raw8397step2 raw8397step2Labels := by
      have ha : raw8397step2 = raw8397step1 := by apply Matrix.ext; unfold raw8397step2 raw8397step1; decide +kernel
      have hl : raw8397step1Labels = labelEmbedding1 ∘ raw8397step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8397step1 raw8397step1Labels raw8397step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3559 node3559Labels := by rfl

def raw8398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8398Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8398step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8398step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8398step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8398step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8398step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8398step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8398 raw8398Labels = mixedMoment B node2841 node2841Labels := by
  calc
    mixedMoment B raw8398 raw8398Labels = mixedMoment B raw8398step0 raw8398step0Labels := by
      have hz : ∀ j, raw8398 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8398step0 = (fun i j => raw8398 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8398step0 raw8398; decide +kernel
      have hl : raw8398step0Labels = raw8398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8398 raw8398Labels permutation265 hz
    mixedMoment B raw8398step0 raw8398step0Labels = mixedMoment B raw8398step1 raw8398step1Labels := by
      have ha : raw8398step1 = (fun i j => raw8398step0 (permutation81 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8398step1 raw8398step0; decide +kernel
      have hl : raw8398step1Labels = raw8398step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8398step0 raw8398step0Labels permutation81 permutation5
    mixedMoment B raw8398step1 raw8398step1Labels = mixedMoment B raw8398step2 raw8398step2Labels := by
      have ha : raw8398step2 = -raw8398step1 := by apply Matrix.ext; change ∀ i j, raw8398step2 i j = -(raw8398step1 i j); unfold raw8398step2 raw8398step1; decide +kernel
      have hl : raw8398step2Labels = raw8398step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8398step2 raw8398step2Labels = mixedMoment B raw8398step3 raw8398step3Labels := by
      have ha : raw8398step3 = raw8398step2 := by apply Matrix.ext; unfold raw8398step3 raw8398step2; decide +kernel
      have hl : raw8398step2Labels = labelEmbedding1 ∘ raw8398step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8398step2 raw8398step2Labels raw8398step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2841 node2841Labels := by rfl

def raw8399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8399Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8399step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8399step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8399step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8399step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8399step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8399 raw8399Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw8399 raw8399Labels = mixedMoment B raw8399step0 raw8399step0Labels := by
      have hz : ∀ j, raw8399 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8399step0 = (fun i j => raw8399 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8399step0 raw8399; decide +kernel
      have hl : raw8399step0Labels = raw8399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8399 raw8399Labels permutation265 hz
    mixedMoment B raw8399step0 raw8399step0Labels = mixedMoment B raw8399step1 raw8399step1Labels := by
      have ha : raw8399step1 = (fun i j => raw8399step0 (permutation45 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8399step1 raw8399step0; decide +kernel
      have hl : raw8399step1Labels = raw8399step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8399step0 raw8399step0Labels permutation45 permutation7
    mixedMoment B raw8399step1 raw8399step1Labels = mixedMoment B raw8399step2 raw8399step2Labels := by
      have ha : raw8399step2 = -raw8399step1 := by apply Matrix.ext; change ∀ i j, raw8399step2 i j = -(raw8399step1 i j); unfold raw8399step2 raw8399step1; decide +kernel
      have hl : raw8399step2Labels = raw8399step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8399step2 raw8399step2Labels = mixedMoment B raw8399step3 raw8399step3Labels := by
      have ha : raw8399step3 = raw8399step2 := by apply Matrix.ext; unfold raw8399step3 raw8399step2; decide +kernel
      have hl : raw8399step2Labels = labelEmbedding1 ∘ raw8399step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8399step2 raw8399step2Labels raw8399step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw8400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8400Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8400step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8400step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8400step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8400step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8400 raw8400Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw8400 raw8400Labels = mixedMoment B raw8400step0 raw8400step0Labels := by
      have hz : ∀ j, raw8400 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8400step0 = (fun i j => raw8400 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8400step0 raw8400; decide +kernel
      have hl : raw8400step0Labels = raw8400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8400 raw8400Labels permutation265 hz
    mixedMoment B raw8400step0 raw8400step0Labels = mixedMoment B raw8400step1 raw8400step1Labels := by
      have ha : raw8400step1 = (fun i j => raw8400step0 (permutation45 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8400step1 raw8400step0; decide +kernel
      have hl : raw8400step1Labels = raw8400step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8400step0 raw8400step0Labels permutation45 permutation7
    mixedMoment B raw8400step1 raw8400step1Labels = mixedMoment B raw8400step2 raw8400step2Labels := by
      have ha : raw8400step2 = -raw8400step1 := by apply Matrix.ext; change ∀ i j, raw8400step2 i j = -(raw8400step1 i j); unfold raw8400step2 raw8400step1; decide +kernel
      have hl : raw8400step2Labels = raw8400step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8400step2 raw8400step2Labels = mixedMoment B raw8400step3 raw8400step3Labels := by
      have ha : raw8400step3 = raw8400step2 := by apply Matrix.ext; unfold raw8400step3 raw8400step2; decide +kernel
      have hl : raw8400step2Labels = labelEmbedding1 ∘ raw8400step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8400step2 raw8400step2Labels raw8400step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw8401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8401Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8401step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8401step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8401step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8401step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8401step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8401step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8401step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8401step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8401 raw8401Labels = mixedMoment B node3306 node3306Labels := by
  calc
    mixedMoment B raw8401 raw8401Labels = mixedMoment B raw8401step0 raw8401step0Labels := by
      have hz : ∀ j, raw8401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8401step0 = (fun i j => raw8401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8401step0 raw8401; decide +kernel
      have hl : raw8401step0Labels = raw8401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8401 raw8401Labels permutation346 hz
    mixedMoment B raw8401step0 raw8401step0Labels = mixedMoment B raw8401step1 raw8401step1Labels := by
      have hz : ∀ j, raw8401step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8401step1 = (fun i j => raw8401step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8401step1 raw8401step0; decide +kernel
      have hl : raw8401step1Labels = raw8401step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8401step0 raw8401step0Labels permutation56 hz
    mixedMoment B raw8401step1 raw8401step1Labels = mixedMoment B raw8401step2 raw8401step2Labels := by
      have ha : raw8401step2 = (fun i j => raw8401step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8401step2 raw8401step1; decide +kernel
      have hl : raw8401step2Labels = raw8401step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8401step1 raw8401step1Labels permutation9 permutation5
    mixedMoment B raw8401step2 raw8401step2Labels = mixedMoment B raw8401step3 raw8401step3Labels := by
      have ha : raw8401step3 = -raw8401step2 := by apply Matrix.ext; change ∀ i j, raw8401step3 i j = -(raw8401step2 i j); unfold raw8401step3 raw8401step2; decide +kernel
      have hl : raw8401step3Labels = raw8401step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8401step3 raw8401step3Labels = mixedMoment B raw8401step4 raw8401step4Labels := by
      have ha : raw8401step4 = raw8401step3 := by apply Matrix.ext; unfold raw8401step4 raw8401step3; decide +kernel
      have hl : raw8401step3Labels = labelEmbedding1 ∘ raw8401step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8401step3 raw8401step3Labels raw8401step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3306 node3306Labels := by rfl

def raw8402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8402step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8402step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8402step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8402step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8402step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8402 raw8402Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw8402 raw8402Labels = mixedMoment B raw8402step0 raw8402step0Labels := by
      have hz : ∀ j, raw8402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8402step0 = (fun i j => raw8402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8402step0 raw8402; decide +kernel
      have hl : raw8402step0Labels = raw8402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8402 raw8402Labels permutation346 hz
    mixedMoment B raw8402step0 raw8402step0Labels = mixedMoment B raw8402step1 raw8402step1Labels := by
      have ha : raw8402step1 = (fun i j => raw8402step0 (permutation45 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8402step1 raw8402step0; decide +kernel
      have hl : raw8402step1Labels = raw8402step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8402step0 raw8402step0Labels permutation45 permutation7
    mixedMoment B raw8402step1 raw8402step1Labels = mixedMoment B raw8402step2 raw8402step2Labels := by
      have ha : raw8402step2 = -raw8402step1 := by apply Matrix.ext; change ∀ i j, raw8402step2 i j = -(raw8402step1 i j); unfold raw8402step2 raw8402step1; decide +kernel
      have hl : raw8402step2Labels = raw8402step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8402step2 raw8402step2Labels = mixedMoment B raw8402step3 raw8402step3Labels := by
      have ha : raw8402step3 = raw8402step2 := by apply Matrix.ext; unfold raw8402step3 raw8402step2; decide +kernel
      have hl : raw8402step2Labels = labelEmbedding1 ∘ raw8402step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8402step2 raw8402step2Labels raw8402step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw8403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8403step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8403step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8403step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8403step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8403step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8403step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8403 raw8403Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw8403 raw8403Labels = mixedMoment B raw8403step0 raw8403step0Labels := by
      have hz : ∀ j, raw8403 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8403step0 = (fun i j => raw8403 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8403step0 raw8403; decide +kernel
      have hl : raw8403step0Labels = raw8403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8403 raw8403Labels permutation265 hz
    mixedMoment B raw8403step0 raw8403step0Labels = mixedMoment B raw8403step1 raw8403step1Labels := by
      have ha : raw8403step1 = (fun i j => raw8403step0 (permutation45 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8403step1 raw8403step0; decide +kernel
      have hl : raw8403step1Labels = raw8403step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8403step0 raw8403step0Labels permutation45 permutation7
    mixedMoment B raw8403step1 raw8403step1Labels = mixedMoment B raw8403step2 raw8403step2Labels := by
      have ha : raw8403step2 = -raw8403step1 := by apply Matrix.ext; change ∀ i j, raw8403step2 i j = -(raw8403step1 i j); unfold raw8403step2 raw8403step1; decide +kernel
      have hl : raw8403step2Labels = raw8403step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8403step2 raw8403step2Labels = mixedMoment B raw8403step3 raw8403step3Labels := by
      have ha : raw8403step3 = raw8403step2 := by apply Matrix.ext; unfold raw8403step3 raw8403step2; decide +kernel
      have hl : raw8403step2Labels = labelEmbedding1 ∘ raw8403step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8403step2 raw8403step2Labels raw8403step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw8404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8404step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8404step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8404step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8404step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8404step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8404 raw8404Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw8404 raw8404Labels = mixedMoment B raw8404step0 raw8404step0Labels := by
      have hz : ∀ j, raw8404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8404step0 = (fun i j => raw8404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8404step0 raw8404; decide +kernel
      have hl : raw8404step0Labels = raw8404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8404 raw8404Labels permutation346 hz
    mixedMoment B raw8404step0 raw8404step0Labels = mixedMoment B raw8404step1 raw8404step1Labels := by
      have hz : ∀ j, raw8404step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8404step1 = (fun i j => raw8404step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8404step1 raw8404step0; decide +kernel
      have hl : raw8404step1Labels = raw8404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8404step0 raw8404step0Labels permutation56 hz
    mixedMoment B raw8404step1 raw8404step1Labels = mixedMoment B raw8404step2 raw8404step2Labels := by
      have ha : raw8404step2 = (fun i j => raw8404step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8404step2 raw8404step1; decide +kernel
      have hl : raw8404step2Labels = raw8404step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8404step1 raw8404step1Labels permutation11 permutation7
    mixedMoment B raw8404step2 raw8404step2Labels = mixedMoment B raw8404step3 raw8404step3Labels := by
      have ha : raw8404step3 = -raw8404step2 := by apply Matrix.ext; change ∀ i j, raw8404step3 i j = -(raw8404step2 i j); unfold raw8404step3 raw8404step2; decide +kernel
      have hl : raw8404step3Labels = raw8404step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8404step3 raw8404step3Labels = mixedMoment B raw8404step4 raw8404step4Labels := by
      have ha : raw8404step4 = raw8404step3 := by apply Matrix.ext; unfold raw8404step4 raw8404step3; decide +kernel
      have hl : raw8404step3Labels = labelEmbedding1 ∘ raw8404step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8404step3 raw8404step3Labels raw8404step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw8405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8405step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8405step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8405step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8405step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8405step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8405step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8405step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8405step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8405step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8405 raw8405Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw8405 raw8405Labels = mixedMoment B raw8405step0 raw8405step0Labels := by
      have hz : ∀ j, raw8405 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8405step0 = (fun i j => raw8405 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8405step0 raw8405; decide +kernel
      have hl : raw8405step0Labels = raw8405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8405 raw8405Labels permutation346 hz
    mixedMoment B raw8405step0 raw8405step0Labels = mixedMoment B raw8405step1 raw8405step1Labels := by
      have hz : ∀ j, raw8405step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8405step1 = (fun i j => raw8405step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8405step1 raw8405step0; decide +kernel
      have hl : raw8405step1Labels = raw8405step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8405step0 raw8405step0Labels permutation56 hz
    mixedMoment B raw8405step1 raw8405step1Labels = mixedMoment B raw8405step2 raw8405step2Labels := by
      have ha : raw8405step2 = (fun i j => raw8405step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8405step2 raw8405step1; decide +kernel
      have hl : raw8405step2Labels = raw8405step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8405step1 raw8405step1Labels permutation11 permutation7
    mixedMoment B raw8405step2 raw8405step2Labels = mixedMoment B raw8405step3 raw8405step3Labels := by
      have ha : raw8405step3 = -raw8405step2 := by apply Matrix.ext; change ∀ i j, raw8405step3 i j = -(raw8405step2 i j); unfold raw8405step3 raw8405step2; decide +kernel
      have hl : raw8405step3Labels = raw8405step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8405step3 raw8405step3Labels = mixedMoment B raw8405step4 raw8405step4Labels := by
      have ha : raw8405step4 = raw8405step3 := by apply Matrix.ext; unfold raw8405step4 raw8405step3; decide +kernel
      have hl : raw8405step3Labels = labelEmbedding1 ∘ raw8405step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8405step3 raw8405step3Labels raw8405step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw8406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8406step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -2, 0], ![2, 2, -4]]
def raw8406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8406step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -2, 0], ![2, 2, -4]]
def raw8406step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8406 raw8406Labels = mixedMoment B node2409 node2409Labels := by
  calc
    mixedMoment B raw8406 raw8406Labels = mixedMoment B raw8406step0 raw8406step0Labels := by
      have hz : ∀ j, raw8406 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8406step0 = (fun i j => raw8406 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8406step0 raw8406; decide +kernel
      have hl : raw8406step0Labels = raw8406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8406 raw8406Labels permutation346 hz
    mixedMoment B raw8406step0 raw8406step0Labels = mixedMoment B raw8406step1 raw8406step1Labels := by
      have hz : ∀ j, raw8406step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8406step1 = (fun i j => raw8406step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8406step1 raw8406step0; decide +kernel
      have hl : raw8406step1Labels = raw8406step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8406step0 raw8406step0Labels permutation56 hz
    mixedMoment B raw8406step1 raw8406step1Labels = mixedMoment B raw8406step2 raw8406step2Labels := by
      have ha : raw8406step2 = (fun i j => raw8406step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8406step2 raw8406step1; decide +kernel
      have hl : raw8406step2Labels = raw8406step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8406step1 raw8406step1Labels permutation25 permutation5
    mixedMoment B raw8406step2 raw8406step2Labels = mixedMoment B raw8406step3 raw8406step3Labels := by
      have ha : raw8406step3 = raw8406step2 := by apply Matrix.ext; unfold raw8406step3 raw8406step2; decide +kernel
      have hl : raw8406step2Labels = labelEmbedding1 ∘ raw8406step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8406step2 raw8406step2Labels raw8406step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2409 node2409Labels := by rfl

def raw8407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8407step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8407step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8407 raw8407Labels = mixedMoment B node2405 node2405Labels := by
  calc
    mixedMoment B raw8407 raw8407Labels = mixedMoment B raw8407step0 raw8407step0Labels := by
      have hz : ∀ j, raw8407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8407step0 = (fun i j => raw8407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8407step0 raw8407; decide +kernel
      have hl : raw8407step0Labels = raw8407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8407 raw8407Labels permutation346 hz
    mixedMoment B raw8407step0 raw8407step0Labels = mixedMoment B raw8407step1 raw8407step1Labels := by
      have ha : raw8407step1 = (fun i j => raw8407step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8407step1 raw8407step0; decide +kernel
      have hl : raw8407step1Labels = raw8407step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8407step0 raw8407step0Labels permutation124 permutation5
    mixedMoment B raw8407step1 raw8407step1Labels = mixedMoment B raw8407step2 raw8407step2Labels := by
      have ha : raw8407step2 = raw8407step1 := by apply Matrix.ext; unfold raw8407step2 raw8407step1; decide +kernel
      have hl : raw8407step1Labels = labelEmbedding1 ∘ raw8407step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8407step1 raw8407step1Labels raw8407step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2405 node2405Labels := by rfl

def raw8408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8408step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8408 raw8408Labels = mixedMoment B node2405 node2405Labels := by
  calc
    mixedMoment B raw8408 raw8408Labels = mixedMoment B raw8408step0 raw8408step0Labels := by
      have hz : ∀ j, raw8408 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8408step0 = (fun i j => raw8408 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8408step0 raw8408; decide +kernel
      have hl : raw8408step0Labels = raw8408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8408 raw8408Labels permutation265 hz
    mixedMoment B raw8408step0 raw8408step0Labels = mixedMoment B raw8408step1 raw8408step1Labels := by
      have ha : raw8408step1 = (fun i j => raw8408step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8408step1 raw8408step0; decide +kernel
      have hl : raw8408step1Labels = raw8408step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8408step0 raw8408step0Labels permutation124 permutation5
    mixedMoment B raw8408step1 raw8408step1Labels = mixedMoment B raw8408step2 raw8408step2Labels := by
      have ha : raw8408step2 = raw8408step1 := by apply Matrix.ext; unfold raw8408step2 raw8408step1; decide +kernel
      have hl : raw8408step1Labels = labelEmbedding1 ∘ raw8408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8408step1 raw8408step1Labels raw8408step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2405 node2405Labels := by rfl

def raw8409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8409step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8409step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8409step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw8409step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8409step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw8409step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8409 raw8409Labels = mixedMoment B node2408 node2408Labels := by
  calc
    mixedMoment B raw8409 raw8409Labels = mixedMoment B raw8409step0 raw8409step0Labels := by
      have hz : ∀ j, raw8409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8409step0 = (fun i j => raw8409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8409step0 raw8409; decide +kernel
      have hl : raw8409step0Labels = raw8409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8409 raw8409Labels permutation346 hz
    mixedMoment B raw8409step0 raw8409step0Labels = mixedMoment B raw8409step1 raw8409step1Labels := by
      have hz : ∀ j, raw8409step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8409step1 = (fun i j => raw8409step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8409step1 raw8409step0; decide +kernel
      have hl : raw8409step1Labels = raw8409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8409step0 raw8409step0Labels permutation56 hz
    mixedMoment B raw8409step1 raw8409step1Labels = mixedMoment B raw8409step2 raw8409step2Labels := by
      have ha : raw8409step2 = (fun i j => raw8409step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8409step2 raw8409step1; decide +kernel
      have hl : raw8409step2Labels = raw8409step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8409step1 raw8409step1Labels permutation24 permutation5
    mixedMoment B raw8409step2 raw8409step2Labels = mixedMoment B raw8409step3 raw8409step3Labels := by
      have ha : raw8409step3 = raw8409step2 := by apply Matrix.ext; unfold raw8409step3 raw8409step2; decide +kernel
      have hl : raw8409step2Labels = labelEmbedding1 ∘ raw8409step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8409step2 raw8409step2Labels raw8409step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2408 node2408Labels := by rfl

def raw8410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8410step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8410step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8410step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8410step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8410step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8410 raw8410Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw8410 raw8410Labels = mixedMoment B raw8410step0 raw8410step0Labels := by
      have hz : ∀ j, raw8410 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8410step0 = (fun i j => raw8410 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8410step0 raw8410; decide +kernel
      have hl : raw8410step0Labels = raw8410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8410 raw8410Labels permutation346 hz
    mixedMoment B raw8410step0 raw8410step0Labels = mixedMoment B raw8410step1 raw8410step1Labels := by
      have hz : ∀ j, raw8410step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8410step1 = (fun i j => raw8410step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8410step1 raw8410step0; decide +kernel
      have hl : raw8410step1Labels = raw8410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8410step0 raw8410step0Labels permutation56 hz
    mixedMoment B raw8410step1 raw8410step1Labels = mixedMoment B raw8410step2 raw8410step2Labels := by
      have ha : raw8410step2 = (fun i j => raw8410step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8410step2 raw8410step1; decide +kernel
      have hl : raw8410step2Labels = raw8410step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8410step1 raw8410step1Labels permutation24 permutation5
    mixedMoment B raw8410step2 raw8410step2Labels = mixedMoment B raw8410step3 raw8410step3Labels := by
      have ha : raw8410step3 = raw8410step2 := by apply Matrix.ext; unfold raw8410step3 raw8410step2; decide +kernel
      have hl : raw8410step2Labels = labelEmbedding1 ∘ raw8410step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8410step2 raw8410step2Labels raw8410step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw8411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8411step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8411step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw8411step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8411step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, -1, -1], ![2, 1, -3]]
def raw8411step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8411step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, -1, -1], ![2, 1, -3]]
def raw8411step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8411 raw8411Labels = mixedMoment B node3247 node3247Labels := by
  calc
    mixedMoment B raw8411 raw8411Labels = mixedMoment B raw8411step0 raw8411step0Labels := by
      have hz : ∀ j, raw8411 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8411step0 = (fun i j => raw8411 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8411step0 raw8411; decide +kernel
      have hl : raw8411step0Labels = raw8411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8411 raw8411Labels permutation346 hz
    mixedMoment B raw8411step0 raw8411step0Labels = mixedMoment B raw8411step1 raw8411step1Labels := by
      have hz : ∀ j, raw8411step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8411step1 = (fun i j => raw8411step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8411step1 raw8411step0; decide +kernel
      have hl : raw8411step1Labels = raw8411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8411step0 raw8411step0Labels permutation56 hz
    mixedMoment B raw8411step1 raw8411step1Labels = mixedMoment B raw8411step2 raw8411step2Labels := by
      have ha : raw8411step2 = (fun i j => raw8411step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8411step2 raw8411step1; decide +kernel
      have hl : raw8411step2Labels = raw8411step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8411step1 raw8411step1Labels permutation8 permutation5
    mixedMoment B raw8411step2 raw8411step2Labels = mixedMoment B raw8411step3 raw8411step3Labels := by
      have ha : raw8411step3 = -raw8411step2 := by apply Matrix.ext; change ∀ i j, raw8411step3 i j = -(raw8411step2 i j); unfold raw8411step3 raw8411step2; decide +kernel
      have hl : raw8411step3Labels = raw8411step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8411step3 raw8411step3Labels = mixedMoment B raw8411step4 raw8411step4Labels := by
      have ha : raw8411step4 = raw8411step3 := by apply Matrix.ext; unfold raw8411step4 raw8411step3; decide +kernel
      have hl : raw8411step3Labels = labelEmbedding1 ∘ raw8411step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8411step3 raw8411step3Labels raw8411step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3247 node3247Labels := by rfl

def raw8412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8412step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8412step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8412 raw8412Labels = mixedMoment B node3358 node3358Labels := by
  calc
    mixedMoment B raw8412 raw8412Labels = mixedMoment B raw8412step0 raw8412step0Labels := by
      have hz : ∀ j, raw8412 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8412step0 = (fun i j => raw8412 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8412step0 raw8412; decide +kernel
      have hl : raw8412step0Labels = raw8412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8412 raw8412Labels permutation346 hz
    mixedMoment B raw8412step0 raw8412step0Labels = mixedMoment B raw8412step1 raw8412step1Labels := by
      have ha : raw8412step1 = (fun i j => raw8412step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8412step1 raw8412step0; decide +kernel
      have hl : raw8412step1Labels = raw8412step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8412step0 raw8412step0Labels permutation148 permutation5
    mixedMoment B raw8412step1 raw8412step1Labels = mixedMoment B raw8412step2 raw8412step2Labels := by
      have ha : raw8412step2 = raw8412step1 := by apply Matrix.ext; unfold raw8412step2 raw8412step1; decide +kernel
      have hl : raw8412step1Labels = labelEmbedding1 ∘ raw8412step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8412step1 raw8412step1Labels raw8412step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3358 node3358Labels := by rfl

def raw8413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8413step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8413step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8413 raw8413Labels = mixedMoment B node3358 node3358Labels := by
  calc
    mixedMoment B raw8413 raw8413Labels = mixedMoment B raw8413step0 raw8413step0Labels := by
      have hz : ∀ j, raw8413 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8413step0 = (fun i j => raw8413 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8413step0 raw8413; decide +kernel
      have hl : raw8413step0Labels = raw8413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8413 raw8413Labels permutation265 hz
    mixedMoment B raw8413step0 raw8413step0Labels = mixedMoment B raw8413step1 raw8413step1Labels := by
      have ha : raw8413step1 = (fun i j => raw8413step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8413step1 raw8413step0; decide +kernel
      have hl : raw8413step1Labels = raw8413step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8413step0 raw8413step0Labels permutation148 permutation5
    mixedMoment B raw8413step1 raw8413step1Labels = mixedMoment B raw8413step2 raw8413step2Labels := by
      have ha : raw8413step2 = raw8413step1 := by apply Matrix.ext; unfold raw8413step2 raw8413step1; decide +kernel
      have hl : raw8413step1Labels = labelEmbedding1 ∘ raw8413step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8413step1 raw8413step1Labels raw8413step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3358 node3358Labels := by rfl

def raw8414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8414step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8414step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8414step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-2, 1, 1], ![-2, -1, 3]]
def raw8414step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8414step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw8414step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8414step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw8414step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8414 raw8414Labels = mixedMoment B node2842 node2842Labels := by
  calc
    mixedMoment B raw8414 raw8414Labels = mixedMoment B raw8414step0 raw8414step0Labels := by
      have hz : ∀ j, raw8414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8414step0 = (fun i j => raw8414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8414step0 raw8414; decide +kernel
      have hl : raw8414step0Labels = raw8414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8414 raw8414Labels permutation346 hz
    mixedMoment B raw8414step0 raw8414step0Labels = mixedMoment B raw8414step1 raw8414step1Labels := by
      have hz : ∀ j, raw8414step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8414step1 = (fun i j => raw8414step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8414step1 raw8414step0; decide +kernel
      have hl : raw8414step1Labels = raw8414step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8414step0 raw8414step0Labels permutation56 hz
    mixedMoment B raw8414step1 raw8414step1Labels = mixedMoment B raw8414step2 raw8414step2Labels := by
      have ha : raw8414step2 = (fun i j => raw8414step1 (permutation14 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8414step2 raw8414step1; decide +kernel
      have hl : raw8414step2Labels = raw8414step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8414step1 raw8414step1Labels permutation14 permutation5
    mixedMoment B raw8414step2 raw8414step2Labels = mixedMoment B raw8414step3 raw8414step3Labels := by
      have ha : raw8414step3 = -raw8414step2 := by apply Matrix.ext; change ∀ i j, raw8414step3 i j = -(raw8414step2 i j); unfold raw8414step3 raw8414step2; decide +kernel
      have hl : raw8414step3Labels = raw8414step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8414step3 raw8414step3Labels = mixedMoment B raw8414step4 raw8414step4Labels := by
      have ha : raw8414step4 = raw8414step3 := by apply Matrix.ext; unfold raw8414step4 raw8414step3; decide +kernel
      have hl : raw8414step3Labels = labelEmbedding1 ∘ raw8414step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8414step3 raw8414step3Labels raw8414step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2842 node2842Labels := by rfl

def raw8415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8415step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8415step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8415step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8415step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8415 raw8415Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw8415 raw8415Labels = mixedMoment B raw8415step0 raw8415step0Labels := by
      have hz : ∀ j, raw8415 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8415step0 = (fun i j => raw8415 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8415step0 raw8415; decide +kernel
      have hl : raw8415step0Labels = raw8415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8415 raw8415Labels permutation346 hz
    mixedMoment B raw8415step0 raw8415step0Labels = mixedMoment B raw8415step1 raw8415step1Labels := by
      have hz : ∀ j, raw8415step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8415step1 = (fun i j => raw8415step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8415step1 raw8415step0; decide +kernel
      have hl : raw8415step1Labels = raw8415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8415step0 raw8415step0Labels permutation56 hz
    mixedMoment B raw8415step1 raw8415step1Labels = mixedMoment B raw8415step2 raw8415step2Labels := by
      have ha : raw8415step2 = (fun i j => raw8415step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8415step2 raw8415step1; decide +kernel
      have hl : raw8415step2Labels = raw8415step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8415step1 raw8415step1Labels permutation30 permutation5
    mixedMoment B raw8415step2 raw8415step2Labels = mixedMoment B raw8415step3 raw8415step3Labels := by
      have ha : raw8415step3 = raw8415step2 := by apply Matrix.ext; unfold raw8415step3 raw8415step2; decide +kernel
      have hl : raw8415step2Labels = labelEmbedding1 ∘ raw8415step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8415step2 raw8415step2Labels raw8415step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3549 node3549Labels := by rfl

def raw8416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8416 raw8416Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw8416 raw8416Labels = mixedMoment B raw8416step0 raw8416step0Labels := by
      have hz : ∀ j, raw8416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8416step0 = (fun i j => raw8416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8416step0 raw8416; decide +kernel
      have hl : raw8416step0Labels = raw8416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8416 raw8416Labels permutation346 hz
    mixedMoment B raw8416step0 raw8416step0Labels = mixedMoment B raw8416step1 raw8416step1Labels := by
      have hz : ∀ j, raw8416step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8416step1 = (fun i j => raw8416step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8416step1 raw8416step0; decide +kernel
      have hl : raw8416step1Labels = raw8416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8416step0 raw8416step0Labels permutation56 hz
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw8417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8417 raw8417Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw8417 raw8417Labels = mixedMoment B raw8417step0 raw8417step0Labels := by
      have hz : ∀ j, raw8417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8417step0 = (fun i j => raw8417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8417step0 raw8417; decide +kernel
      have hl : raw8417step0Labels = raw8417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8417 raw8417Labels permutation346 hz
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw8418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8418 raw8418Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw8418 raw8418Labels = mixedMoment B raw8418step0 raw8418step0Labels := by
      have hz : ∀ j, raw8418 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8418step0 = (fun i j => raw8418 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8418step0 raw8418; decide +kernel
      have hl : raw8418step0Labels = raw8418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8418 raw8418Labels permutation265 hz
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw8419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw8419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8419step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8419step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8419 raw8419Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw8419 raw8419Labels = mixedMoment B raw8419step0 raw8419step0Labels := by
      have hz : ∀ j, raw8419 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8419step0 = (fun i j => raw8419 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8419step0 raw8419; decide +kernel
      have hl : raw8419step0Labels = raw8419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8419 raw8419Labels permutation346 hz
    mixedMoment B raw8419step0 raw8419step0Labels = mixedMoment B raw8419step1 raw8419step1Labels := by
      have hz : ∀ j, raw8419step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8419step1 = (fun i j => raw8419step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8419step1 raw8419step0; decide +kernel
      have hl : raw8419step1Labels = raw8419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8419step0 raw8419step0Labels permutation56 hz
    mixedMoment B raw8419step1 raw8419step1Labels = mixedMoment B raw8419step2 raw8419step2Labels := by
      have ha : raw8419step2 = (fun i j => raw8419step1 (permutation15 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8419step2 raw8419step1; decide +kernel
      have hl : raw8419step2Labels = raw8419step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8419step1 raw8419step1Labels permutation15 permutation4
    mixedMoment B raw8419step2 raw8419step2Labels = mixedMoment B raw8419step3 raw8419step3Labels := by
      have ha : raw8419step3 = -raw8419step2 := by apply Matrix.ext; change ∀ i j, raw8419step3 i j = -(raw8419step2 i j); unfold raw8419step3 raw8419step2; decide +kernel
      have hl : raw8419step3Labels = raw8419step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw8420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8420 raw8420Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw8420 raw8420Labels = mixedMoment B raw8420step0 raw8420step0Labels := by
      have hz : ∀ j, raw8420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8420step0 = (fun i j => raw8420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8420step0 raw8420; decide +kernel
      have hl : raw8420step0Labels = raw8420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8420 raw8420Labels permutation346 hz
    mixedMoment B raw8420step0 raw8420step0Labels = mixedMoment B raw8420step1 raw8420step1Labels := by
      have hz : ∀ j, raw8420step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8420step1 = (fun i j => raw8420step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8420step1 raw8420step0; decide +kernel
      have hl : raw8420step1Labels = raw8420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8420step0 raw8420step0Labels permutation56 hz
    mixedMoment B raw8420step1 raw8420step1Labels = mixedMoment B raw8420step2 raw8420step2Labels := by
      have ha : raw8420step2 = (fun i j => raw8420step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8420step2 raw8420step1; decide +kernel
      have hl : raw8420step2Labels = raw8420step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8420step1 raw8420step1Labels permutation10 permutation2
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw8421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw8421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8421 raw8421Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw8421 raw8421Labels = mixedMoment B raw8421step0 raw8421step0Labels := by
      have hz : ∀ j, raw8421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8421step0 = (fun i j => raw8421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8421step0 raw8421; decide +kernel
      have hl : raw8421step0Labels = raw8421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8421 raw8421Labels permutation346 hz
    mixedMoment B raw8421step0 raw8421step0Labels = mixedMoment B raw8421step1 raw8421step1Labels := by
      have hz : ∀ j, raw8421step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8421step1 = (fun i j => raw8421step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8421step1 raw8421step0; decide +kernel
      have hl : raw8421step1Labels = raw8421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8421step0 raw8421step0Labels permutation56 hz
    mixedMoment B raw8421step1 raw8421step1Labels = mixedMoment B raw8421step2 raw8421step2Labels := by
      have ha : raw8421step2 = (fun i j => raw8421step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8421step2 raw8421step1; decide +kernel
      have hl : raw8421step2Labels = raw8421step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8421step1 raw8421step1Labels permutation18 permutation4
    mixedMoment B raw8421step2 raw8421step2Labels = mixedMoment B raw8421step3 raw8421step3Labels := by
      have ha : raw8421step3 = -raw8421step2 := by apply Matrix.ext; change ∀ i j, raw8421step3 i j = -(raw8421step2 i j); unfold raw8421step3 raw8421step2; decide +kernel
      have hl : raw8421step3Labels = raw8421step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw8422 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![-1, 1], ![1, -1]]
def raw8422Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8422step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![-1, 1], ![1, -1]]
def raw8422step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8422step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]
def raw8422step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8422step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw8422step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical8422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8422 raw8422Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw8422 raw8422Labels = mixedMoment B raw8422step0 raw8422step0Labels := by
      have hz : ∀ j, raw8422 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8422step0 = (fun i j => raw8422 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8422step0 raw8422; decide +kernel
      have hl : raw8422step0Labels = raw8422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8422 raw8422Labels permutation346 hz
    mixedMoment B raw8422step0 raw8422step0Labels = mixedMoment B raw8422step1 raw8422step1Labels := by
      have hz : ∀ j, raw8422step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8422step1 = (fun i j => raw8422step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8422step1 raw8422step0; decide +kernel
      have hl : raw8422step1Labels = raw8422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8422step0 raw8422step0Labels permutation56 hz
    mixedMoment B raw8422step1 raw8422step1Labels = mixedMoment B raw8422step2 raw8422step2Labels := by
      have ha : raw8422step2 = (fun i j => raw8422step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8422step2 raw8422step1; decide +kernel
      have hl : raw8422step2Labels = raw8422step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8422step1 raw8422step1Labels permutation11 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw8423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw8423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8423 raw8423Labels = mixedMoment B node1277 node1277Labels := by
  calc
    mixedMoment B raw8423 raw8423Labels = mixedMoment B raw8423step0 raw8423step0Labels := by
      have hz : ∀ j, raw8423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8423step0 = (fun i j => raw8423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8423step0 raw8423; decide +kernel
      have hl : raw8423step0Labels = raw8423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8423 raw8423Labels permutation346 hz
    mixedMoment B raw8423step0 raw8423step0Labels = mixedMoment B raw8423step1 raw8423step1Labels := by
      have ha : raw8423step1 = (fun i j => raw8423step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8423step1 raw8423step0; decide +kernel
      have hl : raw8423step1Labels = raw8423step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8423step0 raw8423step0Labels permutation40 permutation2
    _ = mixedMoment B node1277 node1277Labels := by rfl

def raw8424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw8424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8424 raw8424Labels = mixedMoment B node1277 node1277Labels := by
  calc
    mixedMoment B raw8424 raw8424Labels = mixedMoment B raw8424step0 raw8424step0Labels := by
      have hz : ∀ j, raw8424 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8424step0 = (fun i j => raw8424 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8424step0 raw8424; decide +kernel
      have hl : raw8424step0Labels = raw8424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8424 raw8424Labels permutation265 hz
    mixedMoment B raw8424step0 raw8424step0Labels = mixedMoment B raw8424step1 raw8424step1Labels := by
      have ha : raw8424step1 = (fun i j => raw8424step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8424step1 raw8424step0; decide +kernel
      have hl : raw8424step1Labels = raw8424step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8424step0 raw8424step0Labels permutation40 permutation2
    _ = mixedMoment B node1277 node1277Labels := by rfl

def raw8425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8425 raw8425Labels = mixedMoment B node1295 node1295Labels := by
  calc
    mixedMoment B raw8425 raw8425Labels = mixedMoment B raw8425step0 raw8425step0Labels := by
      have hz : ∀ j, raw8425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8425step0 = (fun i j => raw8425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8425step0 raw8425; decide +kernel
      have hl : raw8425step0Labels = raw8425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8425 raw8425Labels permutation346 hz
    mixedMoment B raw8425step0 raw8425step0Labels = mixedMoment B raw8425step1 raw8425step1Labels := by
      have hz : ∀ j, raw8425step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8425step1 = (fun i j => raw8425step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8425step1 raw8425step0; decide +kernel
      have hl : raw8425step1Labels = raw8425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8425step0 raw8425step0Labels permutation56 hz
    mixedMoment B raw8425step1 raw8425step1Labels = mixedMoment B raw8425step2 raw8425step2Labels := by
      have ha : raw8425step2 = (fun i j => raw8425step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8425step2 raw8425step1; decide +kernel
      have hl : raw8425step2Labels = raw8425step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8425step1 raw8425step1Labels permutation10 permutation2
    _ = mixedMoment B node1295 node1295Labels := by rfl

def raw8426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8426 raw8426Labels = mixedMoment B node1283 node1283Labels := by
  calc
    mixedMoment B raw8426 raw8426Labels = mixedMoment B raw8426step0 raw8426step0Labels := by
      have hz : ∀ j, raw8426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8426step0 = (fun i j => raw8426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8426step0 raw8426; decide +kernel
      have hl : raw8426step0Labels = raw8426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8426 raw8426Labels permutation346 hz
    mixedMoment B raw8426step0 raw8426step0Labels = mixedMoment B raw8426step1 raw8426step1Labels := by
      have hz : ∀ j, raw8426step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8426step1 = (fun i j => raw8426step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8426step1 raw8426step0; decide +kernel
      have hl : raw8426step1Labels = raw8426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8426step0 raw8426step0Labels permutation56 hz
    _ = mixedMoment B node1283 node1283Labels := by rfl

def raw8427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8427step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8427 raw8427Labels = mixedMoment B node1279 node1279Labels := by
  calc
    mixedMoment B raw8427 raw8427Labels = mixedMoment B raw8427step0 raw8427step0Labels := by
      have hz : ∀ j, raw8427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8427step0 = (fun i j => raw8427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8427step0 raw8427; decide +kernel
      have hl : raw8427step0Labels = raw8427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8427 raw8427Labels permutation346 hz
    mixedMoment B raw8427step0 raw8427step0Labels = mixedMoment B raw8427step1 raw8427step1Labels := by
      have hz : ∀ j, raw8427step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8427step1 = (fun i j => raw8427step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8427step1 raw8427step0; decide +kernel
      have hl : raw8427step1Labels = raw8427step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8427step0 raw8427step0Labels permutation56 hz
    _ = mixedMoment B node1279 node1279Labels := by rfl

def raw8428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw8428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8428 raw8428Labels = mixedMoment B node2577 node2577Labels := by
  calc
    mixedMoment B raw8428 raw8428Labels = mixedMoment B raw8428step0 raw8428step0Labels := by
      have ha : raw8428step0 = (fun i j => raw8428 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8428step0 raw8428; decide +kernel
      have hl : raw8428step0Labels = raw8428Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8428 raw8428Labels permutation160 permutation2
    _ = mixedMoment B node2577 node2577Labels := by rfl

def raw8429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8429 raw8429Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw8429 raw8429Labels = mixedMoment B raw8429step0 raw8429step0Labels := by
      have hz : ∀ j, raw8429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8429step0 = (fun i j => raw8429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8429step0 raw8429; decide +kernel
      have hl : raw8429step0Labels = raw8429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8429 raw8429Labels permutation346 hz
    mixedMoment B raw8429step0 raw8429step0Labels = mixedMoment B raw8429step1 raw8429step1Labels := by
      have ha : raw8429step1 = (fun i j => raw8429step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8429step1 raw8429step0; decide +kernel
      have hl : raw8429step1Labels = raw8429step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8429step0 raw8429step0Labels permutation34 permutation2
    _ = mixedMoment B node2591 node2591Labels := by rfl

def raw8430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8430 raw8430Labels = mixedMoment B node2582 node2582Labels := by
  calc
    mixedMoment B raw8430 raw8430Labels = mixedMoment B raw8430step0 raw8430step0Labels := by
      have hz : ∀ j, raw8430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8430step0 = (fun i j => raw8430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8430step0 raw8430; decide +kernel
      have hl : raw8430step0Labels = raw8430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8430 raw8430Labels permutation346 hz
    _ = mixedMoment B node2582 node2582Labels := by rfl

def raw8431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8431 raw8431Labels = mixedMoment B node2579 node2579Labels := by
  calc
    mixedMoment B raw8431 raw8431Labels = mixedMoment B raw8431step0 raw8431step0Labels := by
      have hz : ∀ j, raw8431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8431step0 = (fun i j => raw8431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8431step0 raw8431; decide +kernel
      have hl : raw8431step0Labels = raw8431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8431 raw8431Labels permutation346 hz
    _ = mixedMoment B node2579 node2579Labels := by rfl

def raw8432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8432 raw8432Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw8432 raw8432Labels = mixedMoment B raw8432step0 raw8432step0Labels := by
      have hz : ∀ j, raw8432 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8432step0 = (fun i j => raw8432 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8432step0 raw8432; decide +kernel
      have hl : raw8432step0Labels = raw8432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8432 raw8432Labels permutation265 hz
    mixedMoment B raw8432step0 raw8432step0Labels = mixedMoment B raw8432step1 raw8432step1Labels := by
      have ha : raw8432step1 = (fun i j => raw8432step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8432step1 raw8432step0; decide +kernel
      have hl : raw8432step1Labels = raw8432step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8432step0 raw8432step0Labels permutation34 permutation2
    _ = mixedMoment B node2591 node2591Labels := by rfl

def raw8433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8433step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8433step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8433 raw8433Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw8433 raw8433Labels = mixedMoment B raw8433step0 raw8433step0Labels := by
      have hz : ∀ j, raw8433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8433step0 = (fun i j => raw8433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8433step0 raw8433; decide +kernel
      have hl : raw8433step0Labels = raw8433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8433 raw8433Labels permutation346 hz
    mixedMoment B raw8433step0 raw8433step0Labels = mixedMoment B raw8433step1 raw8433step1Labels := by
      have hz : ∀ j, raw8433step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8433step1 = (fun i j => raw8433step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8433step1 raw8433step0; decide +kernel
      have hl : raw8433step1Labels = raw8433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8433step0 raw8433step0Labels permutation56 hz
    mixedMoment B raw8433step1 raw8433step1Labels = mixedMoment B raw8433step2 raw8433step2Labels := by
      have ha : raw8433step2 = (fun i j => raw8433step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8433step2 raw8433step1; decide +kernel
      have hl : raw8433step2Labels = raw8433step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8433step1 raw8433step1Labels permutation10 permutation2
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw8434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8434step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8434 raw8434Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw8434 raw8434Labels = mixedMoment B raw8434step0 raw8434step0Labels := by
      have hz : ∀ j, raw8434 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8434step0 = (fun i j => raw8434 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8434step0 raw8434; decide +kernel
      have hl : raw8434step0Labels = raw8434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8434 raw8434Labels permutation346 hz
    mixedMoment B raw8434step0 raw8434step0Labels = mixedMoment B raw8434step1 raw8434step1Labels := by
      have hz : ∀ j, raw8434step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8434step1 = (fun i j => raw8434step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8434step1 raw8434step0; decide +kernel
      have hl : raw8434step1Labels = raw8434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8434step0 raw8434step0Labels permutation56 hz
    mixedMoment B raw8434step1 raw8434step1Labels = mixedMoment B raw8434step2 raw8434step2Labels := by
      have ha : raw8434step2 = (fun i j => raw8434step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8434step2 raw8434step1; decide +kernel
      have hl : raw8434step2Labels = raw8434step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8434step1 raw8434step1Labels permutation11 permutation2
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw8435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw8435step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8435step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8435step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8435step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8435 raw8435Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw8435 raw8435Labels = mixedMoment B raw8435step0 raw8435step0Labels := by
      have hz : ∀ j, raw8435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8435step0 = (fun i j => raw8435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8435step0 raw8435; decide +kernel
      have hl : raw8435step0Labels = raw8435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8435 raw8435Labels permutation346 hz
    mixedMoment B raw8435step0 raw8435step0Labels = mixedMoment B raw8435step1 raw8435step1Labels := by
      have ha : raw8435step1 = (fun i j => raw8435step0 (permutation81 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8435step1 raw8435step0; decide +kernel
      have hl : raw8435step1Labels = raw8435step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8435step0 raw8435step0Labels permutation81 permutation6
    mixedMoment B raw8435step1 raw8435step1Labels = mixedMoment B raw8435step2 raw8435step2Labels := by
      have ha : raw8435step2 = -raw8435step1 := by apply Matrix.ext; change ∀ i j, raw8435step2 i j = -(raw8435step1 i j); unfold raw8435step2 raw8435step1; decide +kernel
      have hl : raw8435step2Labels = raw8435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8435step2 raw8435step2Labels = mixedMoment B raw8435step3 raw8435step3Labels := by
      have ha : raw8435step3 = raw8435step2 := by apply Matrix.ext; unfold raw8435step3 raw8435step2; decide +kernel
      have hl : raw8435step2Labels = labelEmbedding9 ∘ raw8435step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8435step2 raw8435step2Labels raw8435step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw8436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw8436step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8436step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8436step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8436step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8436 raw8436Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw8436 raw8436Labels = mixedMoment B raw8436step0 raw8436step0Labels := by
      have hz : ∀ j, raw8436 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8436step0 = (fun i j => raw8436 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8436step0 raw8436; decide +kernel
      have hl : raw8436step0Labels = raw8436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8436 raw8436Labels permutation265 hz
    mixedMoment B raw8436step0 raw8436step0Labels = mixedMoment B raw8436step1 raw8436step1Labels := by
      have ha : raw8436step1 = (fun i j => raw8436step0 (permutation81 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8436step1 raw8436step0; decide +kernel
      have hl : raw8436step1Labels = raw8436step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8436step0 raw8436step0Labels permutation81 permutation6
    mixedMoment B raw8436step1 raw8436step1Labels = mixedMoment B raw8436step2 raw8436step2Labels := by
      have ha : raw8436step2 = -raw8436step1 := by apply Matrix.ext; change ∀ i j, raw8436step2 i j = -(raw8436step1 i j); unfold raw8436step2 raw8436step1; decide +kernel
      have hl : raw8436step2Labels = raw8436step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8436step2 raw8436step2Labels = mixedMoment B raw8436step3 raw8436step3Labels := by
      have ha : raw8436step3 = raw8436step2 := by apply Matrix.ext; unfold raw8436step3 raw8436step2; decide +kernel
      have hl : raw8436step2Labels = labelEmbedding9 ∘ raw8436step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8436step2 raw8436step2Labels raw8436step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw8437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8437step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8437 raw8437Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw8437 raw8437Labels = mixedMoment B raw8437step0 raw8437step0Labels := by
      have hz : ∀ j, raw8437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8437step0 = (fun i j => raw8437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8437step0 raw8437; decide +kernel
      have hl : raw8437step0Labels = raw8437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8437 raw8437Labels permutation346 hz
    mixedMoment B raw8437step0 raw8437step0Labels = mixedMoment B raw8437step1 raw8437step1Labels := by
      have hz : ∀ j, raw8437step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8437step1 = (fun i j => raw8437step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8437step1 raw8437step0; decide +kernel
      have hl : raw8437step1Labels = raw8437step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8437step0 raw8437step0Labels permutation56 hz
    _ = mixedMoment B node5475 node5475Labels := by rfl

def raw8438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8438step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8438step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8438step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8438step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8438step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8438 raw8438Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw8438 raw8438Labels = mixedMoment B raw8438step0 raw8438step0Labels := by
      have hz : ∀ j, raw8438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8438step0 = (fun i j => raw8438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8438step0 raw8438; decide +kernel
      have hl : raw8438step0Labels = raw8438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8438 raw8438Labels permutation346 hz
    mixedMoment B raw8438step0 raw8438step0Labels = mixedMoment B raw8438step1 raw8438step1Labels := by
      have hz : ∀ j, raw8438step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8438step1 = (fun i j => raw8438step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8438step1 raw8438step0; decide +kernel
      have hl : raw8438step1Labels = raw8438step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8438step0 raw8438step0Labels permutation56 hz
    mixedMoment B raw8438step1 raw8438step1Labels = mixedMoment B raw8438step2 raw8438step2Labels := by
      have ha : raw8438step2 = (fun i j => raw8438step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8438step2 raw8438step1; decide +kernel
      have hl : raw8438step2Labels = raw8438step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8438step1 raw8438step1Labels permutation18 permutation4
    mixedMoment B raw8438step2 raw8438step2Labels = mixedMoment B raw8438step3 raw8438step3Labels := by
      have ha : raw8438step3 = raw8438step2 := by apply Matrix.ext; unfold raw8438step3 raw8438step2; decide +kernel
      have hl : raw8438step2Labels = labelEmbedding7 ∘ raw8438step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8438step2 raw8438step2Labels raw8438step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5449 node5449Labels := by rfl

def raw8439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8439step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8439step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8439step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8439step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8439step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8439step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8439 raw8439Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw8439 raw8439Labels = mixedMoment B raw8439step0 raw8439step0Labels := by
      have hz : ∀ j, raw8439 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8439step0 = (fun i j => raw8439 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8439step0 raw8439; decide +kernel
      have hl : raw8439step0Labels = raw8439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8439 raw8439Labels permutation346 hz
    mixedMoment B raw8439step0 raw8439step0Labels = mixedMoment B raw8439step1 raw8439step1Labels := by
      have hz : ∀ j, raw8439step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8439step1 = (fun i j => raw8439step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8439step1 raw8439step0; decide +kernel
      have hl : raw8439step1Labels = raw8439step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8439step0 raw8439step0Labels permutation56 hz
    mixedMoment B raw8439step1 raw8439step1Labels = mixedMoment B raw8439step2 raw8439step2Labels := by
      have ha : raw8439step2 = (fun i j => raw8439step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8439step2 raw8439step1; decide +kernel
      have hl : raw8439step2Labels = raw8439step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8439step1 raw8439step1Labels permutation15 permutation6
    mixedMoment B raw8439step2 raw8439step2Labels = mixedMoment B raw8439step3 raw8439step3Labels := by
      have ha : raw8439step3 = -raw8439step2 := by apply Matrix.ext; change ∀ i j, raw8439step3 i j = -(raw8439step2 i j); unfold raw8439step3 raw8439step2; decide +kernel
      have hl : raw8439step3Labels = raw8439step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8439step3 raw8439step3Labels = mixedMoment B raw8439step4 raw8439step4Labels := by
      have ha : raw8439step4 = raw8439step3 := by apply Matrix.ext; unfold raw8439step4 raw8439step3; decide +kernel
      have hl : raw8439step3Labels = labelEmbedding9 ∘ raw8439step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8439step3 raw8439step3Labels raw8439step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw8440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8440step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8440step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8440 raw8440Labels = mixedMoment B node4471 node4471Labels := by
  calc
    mixedMoment B raw8440 raw8440Labels = mixedMoment B raw8440step0 raw8440step0Labels := by
      have hz : ∀ j, raw8440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8440step0 = (fun i j => raw8440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8440step0 raw8440; decide +kernel
      have hl : raw8440step0Labels = raw8440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8440 raw8440Labels permutation346 hz
    mixedMoment B raw8440step0 raw8440step0Labels = mixedMoment B raw8440step1 raw8440step1Labels := by
      have ha : raw8440step1 = (fun i j => raw8440step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8440step1 raw8440step0; decide +kernel
      have hl : raw8440step1Labels = raw8440step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8440step0 raw8440step0Labels permutation40 permutation3
    mixedMoment B raw8440step1 raw8440step1Labels = mixedMoment B raw8440step2 raw8440step2Labels := by
      have ha : raw8440step2 = raw8440step1 := by apply Matrix.ext; unfold raw8440step2 raw8440step1; decide +kernel
      have hl : raw8440step1Labels = labelEmbedding6 ∘ raw8440step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8440step1 raw8440step1Labels raw8440step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4471 node4471Labels := by rfl

def raw8441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8441step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8441 raw8441Labels = mixedMoment B node5083 node5083Labels := by
  calc
    mixedMoment B raw8441 raw8441Labels = mixedMoment B raw8441step0 raw8441step0Labels := by
      have ha : raw8441step0 = (fun i j => raw8441 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8441step0 raw8441; decide +kernel
      have hl : raw8441step0Labels = raw8441Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8441 raw8441Labels permutation184 permutation3
    mixedMoment B raw8441step0 raw8441step0Labels = mixedMoment B raw8441step1 raw8441step1Labels := by
      have ha : raw8441step1 = raw8441step0 := by apply Matrix.ext; unfold raw8441step1 raw8441step0; decide +kernel
      have hl : raw8441step0Labels = labelEmbedding6 ∘ raw8441step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8441step0 raw8441step0Labels raw8441step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5083 node5083Labels := by rfl

def raw8442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8442step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8442step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8442 raw8442Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw8442 raw8442Labels = mixedMoment B raw8442step0 raw8442step0Labels := by
      have hz : ∀ j, raw8442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8442step0 = (fun i j => raw8442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8442step0 raw8442; decide +kernel
      have hl : raw8442step0Labels = raw8442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8442 raw8442Labels permutation346 hz
    mixedMoment B raw8442step0 raw8442step0Labels = mixedMoment B raw8442step1 raw8442step1Labels := by
      have ha : raw8442step1 = (fun i j => raw8442step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8442step1 raw8442step0; decide +kernel
      have hl : raw8442step1Labels = raw8442step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8442step0 raw8442step0Labels permutation40 permutation3
    mixedMoment B raw8442step1 raw8442step1Labels = mixedMoment B raw8442step2 raw8442step2Labels := by
      have ha : raw8442step2 = raw8442step1 := by apply Matrix.ext; unfold raw8442step2 raw8442step1; decide +kernel
      have hl : raw8442step1Labels = labelEmbedding6 ∘ raw8442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8442step1 raw8442step1Labels raw8442step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw8443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8443step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw8443step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw8443step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8443 raw8443Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw8443 raw8443Labels = mixedMoment B raw8443step0 raw8443step0Labels := by
      have hz : ∀ j, raw8443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8443step0 = (fun i j => raw8443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8443step0 raw8443; decide +kernel
      have hl : raw8443step0Labels = raw8443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8443 raw8443Labels permutation346 hz
    mixedMoment B raw8443step0 raw8443step0Labels = mixedMoment B raw8443step1 raw8443step1Labels := by
      have ha : raw8443step1 = (fun i j => raw8443step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8443step1 raw8443step0; decide +kernel
      have hl : raw8443step1Labels = raw8443step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8443step0 raw8443step0Labels permutation46 permutation3
    mixedMoment B raw8443step1 raw8443step1Labels = mixedMoment B raw8443step2 raw8443step2Labels := by
      have ha : raw8443step2 = raw8443step1 := by apply Matrix.ext; unfold raw8443step2 raw8443step1; decide +kernel
      have hl : raw8443step1Labels = labelEmbedding6 ∘ raw8443step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8443step1 raw8443step1Labels raw8443step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw8444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8444step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8444step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8444step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8444 raw8444Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw8444 raw8444Labels = mixedMoment B raw8444step0 raw8444step0Labels := by
      have hz : ∀ j, raw8444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8444step0 = (fun i j => raw8444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8444step0 raw8444; decide +kernel
      have hl : raw8444step0Labels = raw8444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8444 raw8444Labels permutation346 hz
    mixedMoment B raw8444step0 raw8444step0Labels = mixedMoment B raw8444step1 raw8444step1Labels := by
      have ha : raw8444step1 = (fun i j => raw8444step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8444step1 raw8444step0; decide +kernel
      have hl : raw8444step1Labels = raw8444step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8444step0 raw8444step0Labels permutation41 permutation3
    mixedMoment B raw8444step1 raw8444step1Labels = mixedMoment B raw8444step2 raw8444step2Labels := by
      have ha : raw8444step2 = raw8444step1 := by apply Matrix.ext; unfold raw8444step2 raw8444step1; decide +kernel
      have hl : raw8444step1Labels = labelEmbedding6 ∘ raw8444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8444step1 raw8444step1Labels raw8444step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw8445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8445step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8445step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8445 raw8445Labels = mixedMoment B node4471 node4471Labels := by
  calc
    mixedMoment B raw8445 raw8445Labels = mixedMoment B raw8445step0 raw8445step0Labels := by
      have hz : ∀ j, raw8445 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8445step0 = (fun i j => raw8445 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8445step0 raw8445; decide +kernel
      have hl : raw8445step0Labels = raw8445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8445 raw8445Labels permutation265 hz
    mixedMoment B raw8445step0 raw8445step0Labels = mixedMoment B raw8445step1 raw8445step1Labels := by
      have ha : raw8445step1 = (fun i j => raw8445step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8445step1 raw8445step0; decide +kernel
      have hl : raw8445step1Labels = raw8445step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8445step0 raw8445step0Labels permutation40 permutation3
    mixedMoment B raw8445step1 raw8445step1Labels = mixedMoment B raw8445step2 raw8445step2Labels := by
      have ha : raw8445step2 = raw8445step1 := by apply Matrix.ext; unfold raw8445step2 raw8445step1; decide +kernel
      have hl : raw8445step1Labels = labelEmbedding6 ∘ raw8445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8445step1 raw8445step1Labels raw8445step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4471 node4471Labels := by rfl

def raw8446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8446step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8446step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8446 raw8446Labels = mixedMoment B node5083 node5083Labels := by
  calc
    mixedMoment B raw8446 raw8446Labels = mixedMoment B raw8446step0 raw8446step0Labels := by
      have ha : raw8446step0 = (fun i j => raw8446 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8446step0 raw8446; decide +kernel
      have hl : raw8446step0Labels = raw8446Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8446 raw8446Labels permutation160 permutation3
    mixedMoment B raw8446step0 raw8446step0Labels = mixedMoment B raw8446step1 raw8446step1Labels := by
      have ha : raw8446step1 = raw8446step0 := by apply Matrix.ext; unfold raw8446step1 raw8446step0; decide +kernel
      have hl : raw8446step0Labels = labelEmbedding6 ∘ raw8446step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8446step0 raw8446step0Labels raw8446step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5083 node5083Labels := by rfl

def raw8447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8447step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8447step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8447step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8447 raw8447Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw8447 raw8447Labels = mixedMoment B raw8447step0 raw8447step0Labels := by
      have hz : ∀ j, raw8447 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8447step0 = (fun i j => raw8447 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8447step0 raw8447; decide +kernel
      have hl : raw8447step0Labels = raw8447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8447 raw8447Labels permutation265 hz
    mixedMoment B raw8447step0 raw8447step0Labels = mixedMoment B raw8447step1 raw8447step1Labels := by
      have ha : raw8447step1 = (fun i j => raw8447step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8447step1 raw8447step0; decide +kernel
      have hl : raw8447step1Labels = raw8447step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8447step0 raw8447step0Labels permutation40 permutation3
    mixedMoment B raw8447step1 raw8447step1Labels = mixedMoment B raw8447step2 raw8447step2Labels := by
      have ha : raw8447step2 = raw8447step1 := by apply Matrix.ext; unfold raw8447step2 raw8447step1; decide +kernel
      have hl : raw8447step1Labels = labelEmbedding6 ∘ raw8447step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8447step1 raw8447step1Labels raw8447step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
