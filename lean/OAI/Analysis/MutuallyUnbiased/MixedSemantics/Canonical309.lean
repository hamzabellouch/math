import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.ExtraNodes

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39552Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39552step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw39552step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39552step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39552 raw39552Labels = mixedMoment B node168 node168Labels := by
  calc
    mixedMoment B raw39552 raw39552Labels = mixedMoment B raw39552step0 raw39552step0Labels := by
      have hz : ∀ j, raw39552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39552step0 = (fun i j => raw39552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39552step0 raw39552; decide +kernel
      have hl : raw39552step0Labels = raw39552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39552 raw39552Labels permutation346 hz
    mixedMoment B raw39552step0 raw39552step0Labels = mixedMoment B raw39552step1 raw39552step1Labels := by
      have ha : raw39552step1 = (fun i j => raw39552step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39552step1 raw39552step0; decide +kernel
      have hl : raw39552step1Labels = raw39552step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39552step0 raw39552step0Labels permutation40 permutation7
    mixedMoment B raw39552step1 raw39552step1Labels = mixedMoment B raw39552step2 raw39552step2Labels := by
      have ha : raw39552step2 = -raw39552step1 := by apply Matrix.ext; change ∀ i j, raw39552step2 i j = -(raw39552step1 i j); unfold raw39552step2 raw39552step1; decide +kernel
      have hl : raw39552step2Labels = raw39552step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node168 node168Labels := by rfl

def raw39553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39553Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39553step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39553step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39553step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39553 raw39553Labels = mixedMoment B node195 node195Labels := by
  calc
    mixedMoment B raw39553 raw39553Labels = mixedMoment B raw39553step0 raw39553step0Labels := by
      have hz : ∀ j, raw39553 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39553step0 = (fun i j => raw39553 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39553step0 raw39553; decide +kernel
      have hl : raw39553step0Labels = raw39553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39553 raw39553Labels permutation346 hz
    mixedMoment B raw39553step0 raw39553step0Labels = mixedMoment B raw39553step1 raw39553step1Labels := by
      have ha : raw39553step1 = (fun i j => raw39553step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39553step1 raw39553step0; decide +kernel
      have hl : raw39553step1Labels = raw39553step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39553step0 raw39553step0Labels permutation54 permutation7
    mixedMoment B raw39553step1 raw39553step1Labels = mixedMoment B raw39553step2 raw39553step2Labels := by
      have ha : raw39553step2 = -raw39553step1 := by apply Matrix.ext; change ∀ i j, raw39553step2 i j = -(raw39553step1 i j); unfold raw39553step2 raw39553step1; decide +kernel
      have hl : raw39553step2Labels = raw39553step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node195 node195Labels := by rfl

def raw39554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39554Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39554step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39554step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39554step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39554 raw39554Labels = mixedMoment B node240 node240Labels := by
  calc
    mixedMoment B raw39554 raw39554Labels = mixedMoment B raw39554step0 raw39554step0Labels := by
      have hz : ∀ j, raw39554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39554step0 = (fun i j => raw39554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39554step0 raw39554; decide +kernel
      have hl : raw39554step0Labels = raw39554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39554 raw39554Labels permutation346 hz
    mixedMoment B raw39554step0 raw39554step0Labels = mixedMoment B raw39554step1 raw39554step1Labels := by
      have ha : raw39554step1 = (fun i j => raw39554step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39554step1 raw39554step0; decide +kernel
      have hl : raw39554step1Labels = raw39554step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39554step0 raw39554step0Labels permutation54 permutation7
    mixedMoment B raw39554step1 raw39554step1Labels = mixedMoment B raw39554step2 raw39554step2Labels := by
      have ha : raw39554step2 = -raw39554step1 := by apply Matrix.ext; change ∀ i j, raw39554step2 i j = -(raw39554step1 i j); unfold raw39554step2 raw39554step1; decide +kernel
      have hl : raw39554step2Labels = raw39554step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node240 node240Labels := by rfl

def raw39555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39555Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39555step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39555step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39555step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39555 raw39555Labels = mixedMoment B node248 node248Labels := by
  calc
    mixedMoment B raw39555 raw39555Labels = mixedMoment B raw39555step0 raw39555step0Labels := by
      have hz : ∀ j, raw39555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39555step0 = (fun i j => raw39555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39555step0 raw39555; decide +kernel
      have hl : raw39555step0Labels = raw39555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39555 raw39555Labels permutation346 hz
    mixedMoment B raw39555step0 raw39555step0Labels = mixedMoment B raw39555step1 raw39555step1Labels := by
      have ha : raw39555step1 = (fun i j => raw39555step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39555step1 raw39555step0; decide +kernel
      have hl : raw39555step1Labels = raw39555step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39555step0 raw39555step0Labels permutation53 permutation7
    mixedMoment B raw39555step1 raw39555step1Labels = mixedMoment B raw39555step2 raw39555step2Labels := by
      have ha : raw39555step2 = -raw39555step1 := by apply Matrix.ext; change ∀ i j, raw39555step2 i j = -(raw39555step1 i j); unfold raw39555step2 raw39555step1; decide +kernel
      have hl : raw39555step2Labels = raw39555step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node248 node248Labels := by rfl

def raw39556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39556Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39556step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39556step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39556 raw39556Labels = mixedMoment B node213 node213Labels := by
  calc
    mixedMoment B raw39556 raw39556Labels = mixedMoment B raw39556step0 raw39556step0Labels := by
      have ha : raw39556step0 = (fun i j => raw39556 (permutation198 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39556step0 raw39556; decide +kernel
      have hl : raw39556step0Labels = raw39556Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39556 raw39556Labels permutation198 permutation7
    mixedMoment B raw39556step0 raw39556step0Labels = mixedMoment B raw39556step1 raw39556step1Labels := by
      have ha : raw39556step1 = -raw39556step0 := by apply Matrix.ext; change ∀ i j, raw39556step1 i j = -(raw39556step0 i j); unfold raw39556step1 raw39556step0; decide +kernel
      have hl : raw39556step1Labels = raw39556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node213 node213Labels := by rfl

def raw39557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39557Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39557step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39557step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39557 raw39557Labels = mixedMoment B node167 node167Labels := by
  calc
    mixedMoment B raw39557 raw39557Labels = mixedMoment B raw39557step0 raw39557step0Labels := by
      have ha : raw39557step0 = (fun i j => raw39557 (permutation198 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39557step0 raw39557; decide +kernel
      have hl : raw39557step0Labels = raw39557Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39557 raw39557Labels permutation198 permutation7
    mixedMoment B raw39557step0 raw39557step0Labels = mixedMoment B raw39557step1 raw39557step1Labels := by
      have ha : raw39557step1 = -raw39557step0 := by apply Matrix.ext; change ∀ i j, raw39557step1 i j = -(raw39557step0 i j); unfold raw39557step1 raw39557step0; decide +kernel
      have hl : raw39557step1Labels = raw39557step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node167 node167Labels := by rfl

def raw39558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw39558Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw39558step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39558step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39558 raw39558Labels = mixedMoment B node253 node253Labels := by
  calc
    mixedMoment B raw39558 raw39558Labels = mixedMoment B raw39558step0 raw39558step0Labels := by
      have ha : raw39558step0 = (fun i j => raw39558 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39558step0 raw39558; decide +kernel
      have hl : raw39558step0Labels = raw39558Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39558 raw39558Labels permutation246 permutation7
    mixedMoment B raw39558step0 raw39558step0Labels = mixedMoment B raw39558step1 raw39558step1Labels := by
      have ha : raw39558step1 = -raw39558step0 := by apply Matrix.ext; change ∀ i j, raw39558step1 i j = -(raw39558step0 i j); unfold raw39558step1 raw39558step0; decide +kernel
      have hl : raw39558step1Labels = raw39558step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node253 node253Labels := by rfl

def raw39559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39559Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39559 raw39559Labels = mixedMoment B node257 node257Labels := by
  calc
    _ = mixedMoment B node257 node257Labels := by rfl

def raw39560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39560Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39560step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39560step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39560 raw39560Labels = mixedMoment B node189 node189Labels := by
  calc
    mixedMoment B raw39560 raw39560Labels = mixedMoment B raw39560step0 raw39560step0Labels := by
      have ha : raw39560step0 = (fun i j => raw39560 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39560step0 raw39560; decide +kernel
      have hl : raw39560step0Labels = raw39560Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39560 raw39560Labels permutation224 permutation7
    mixedMoment B raw39560step0 raw39560step0Labels = mixedMoment B raw39560step1 raw39560step1Labels := by
      have ha : raw39560step1 = -raw39560step0 := by apply Matrix.ext; change ∀ i j, raw39560step1 i j = -(raw39560step0 i j); unfold raw39560step1 raw39560step0; decide +kernel
      have hl : raw39560step1Labels = raw39560step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node189 node189Labels := by rfl

def raw39561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39561Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39561step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw39561step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39561step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39561 raw39561Labels = mixedMoment B node254 node254Labels := by
  calc
    mixedMoment B raw39561 raw39561Labels = mixedMoment B raw39561step0 raw39561step0Labels := by
      have hz : ∀ j, raw39561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39561step0 = (fun i j => raw39561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39561step0 raw39561; decide +kernel
      have hl : raw39561step0Labels = raw39561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39561 raw39561Labels permutation434 hz
    mixedMoment B raw39561step0 raw39561step0Labels = mixedMoment B raw39561step1 raw39561step1Labels := by
      have ha : raw39561step1 = (fun i j => raw39561step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39561step1 raw39561step0; decide +kernel
      have hl : raw39561step1Labels = raw39561step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39561step0 raw39561step0Labels permutation50 permutation7
    mixedMoment B raw39561step1 raw39561step1Labels = mixedMoment B raw39561step2 raw39561step2Labels := by
      have ha : raw39561step2 = -raw39561step1 := by apply Matrix.ext; change ∀ i j, raw39561step2 i j = -(raw39561step1 i j); unfold raw39561step2 raw39561step1; decide +kernel
      have hl : raw39561step2Labels = raw39561step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node254 node254Labels := by rfl

def raw39562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39562Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39562step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39562 raw39562Labels = mixedMoment B node260 node260Labels := by
  calc
    mixedMoment B raw39562 raw39562Labels = mixedMoment B raw39562step0 raw39562step0Labels := by
      have hz : ∀ j, raw39562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39562step0 = (fun i j => raw39562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39562step0 raw39562; decide +kernel
      have hl : raw39562step0Labels = raw39562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39562 raw39562Labels permutation434 hz
    _ = mixedMoment B node260 node260Labels := by rfl

def raw39563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39563Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw39563step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw39563step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw39563step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39563 raw39563Labels = mixedMoment B node190 node190Labels := by
  calc
    mixedMoment B raw39563 raw39563Labels = mixedMoment B raw39563step0 raw39563step0Labels := by
      have hz : ∀ j, raw39563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39563step0 = (fun i j => raw39563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39563step0 raw39563; decide +kernel
      have hl : raw39563step0Labels = raw39563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39563 raw39563Labels permutation434 hz
    mixedMoment B raw39563step0 raw39563step0Labels = mixedMoment B raw39563step1 raw39563step1Labels := by
      have ha : raw39563step1 = (fun i j => raw39563step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39563step1 raw39563step0; decide +kernel
      have hl : raw39563step1Labels = raw39563step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39563step0 raw39563step0Labels permutation44 permutation7
    mixedMoment B raw39563step1 raw39563step1Labels = mixedMoment B raw39563step2 raw39563step2Labels := by
      have ha : raw39563step2 = -raw39563step1 := by apply Matrix.ext; change ∀ i j, raw39563step2 i j = -(raw39563step1 i j); unfold raw39563step2 raw39563step1; decide +kernel
      have hl : raw39563step2Labels = raw39563step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node190 node190Labels := by rfl

def raw39564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39564Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39564step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39564step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39564 raw39564Labels = mixedMoment B node220 node220Labels := by
  calc
    mixedMoment B raw39564 raw39564Labels = mixedMoment B raw39564step0 raw39564step0Labels := by
      have ha : raw39564step0 = (fun i j => raw39564 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39564step0 raw39564; decide +kernel
      have hl : raw39564step0Labels = raw39564Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39564 raw39564Labels permutation212 permutation7
    mixedMoment B raw39564step0 raw39564step0Labels = mixedMoment B raw39564step1 raw39564step1Labels := by
      have ha : raw39564step1 = -raw39564step0 := by apply Matrix.ext; change ∀ i j, raw39564step1 i j = -(raw39564step0 i j); unfold raw39564step1 raw39564step0; decide +kernel
      have hl : raw39564step1Labels = raw39564step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node220 node220Labels := by rfl

def raw39565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39565Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw39565step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw39565step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39565 raw39565Labels = mixedMoment B node163 node163Labels := by
  calc
    mixedMoment B raw39565 raw39565Labels = mixedMoment B raw39565step0 raw39565step0Labels := by
      have ha : raw39565step0 = (fun i j => raw39565 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39565step0 raw39565; decide +kernel
      have hl : raw39565step0Labels = raw39565Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39565 raw39565Labels permutation212 permutation7
    mixedMoment B raw39565step0 raw39565step0Labels = mixedMoment B raw39565step1 raw39565step1Labels := by
      have ha : raw39565step1 = -raw39565step0 := by apply Matrix.ext; change ∀ i j, raw39565step1 i j = -(raw39565step0 i j); unfold raw39565step1 raw39565step0; decide +kernel
      have hl : raw39565step1Labels = raw39565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node163 node163Labels := by rfl

def raw39566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39566Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39566step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39566 raw39566Labels = mixedMoment B node259 node259Labels := by
  calc
    mixedMoment B raw39566 raw39566Labels = mixedMoment B raw39566step0 raw39566step0Labels := by
      have ha : raw39566step0 = (fun i j => raw39566 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39566step0 raw39566; decide +kernel
      have hl : raw39566step0Labels = raw39566Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39566 raw39566Labels permutation155 permutation2
    _ = mixedMoment B node259 node259Labels := by rfl

def raw39567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39567Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39567step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw39567step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw39567step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39567step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39567 raw39567Labels = mixedMoment B node255 node255Labels := by
  calc
    mixedMoment B raw39567 raw39567Labels = mixedMoment B raw39567step0 raw39567step0Labels := by
      have hz : ∀ j, raw39567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39567step0 = (fun i j => raw39567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39567step0 raw39567; decide +kernel
      have hl : raw39567step0Labels = raw39567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39567 raw39567Labels permutation434 hz
    mixedMoment B raw39567step0 raw39567step0Labels = mixedMoment B raw39567step1 raw39567step1Labels := by
      have hz : ∀ j, raw39567step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39567step1 = (fun i j => raw39567step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39567step1 raw39567step0; decide +kernel
      have hl : raw39567step1Labels = raw39567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39567step0 raw39567step0Labels permutation80 hz
    mixedMoment B raw39567step1 raw39567step1Labels = mixedMoment B raw39567step2 raw39567step2Labels := by
      have ha : raw39567step2 = (fun i j => raw39567step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39567step2 raw39567step1; decide +kernel
      have hl : raw39567step2Labels = raw39567step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39567step1 raw39567step1Labels permutation12 permutation7
    mixedMoment B raw39567step2 raw39567step2Labels = mixedMoment B raw39567step3 raw39567step3Labels := by
      have ha : raw39567step3 = -raw39567step2 := by apply Matrix.ext; change ∀ i j, raw39567step3 i j = -(raw39567step2 i j); unfold raw39567step3 raw39567step2; decide +kernel
      have hl : raw39567step3Labels = raw39567step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node255 node255Labels := by rfl

def raw39568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39568Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39568step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw39568step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw39568step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39568 raw39568Labels = mixedMoment B node134 node134Labels := by
  calc
    mixedMoment B raw39568 raw39568Labels = mixedMoment B raw39568step0 raw39568step0Labels := by
      have hz : ∀ j, raw39568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39568step0 = (fun i j => raw39568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39568step0 raw39568; decide +kernel
      have hl : raw39568step0Labels = raw39568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39568 raw39568Labels permutation434 hz
    mixedMoment B raw39568step0 raw39568step0Labels = mixedMoment B raw39568step1 raw39568step1Labels := by
      have hz : ∀ j, raw39568step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39568step1 = (fun i j => raw39568step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39568step1 raw39568step0; decide +kernel
      have hl : raw39568step1Labels = raw39568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39568step0 raw39568step0Labels permutation80 hz
    mixedMoment B raw39568step1 raw39568step1Labels = mixedMoment B raw39568step2 raw39568step2Labels := by
      have ha : raw39568step2 = (fun i j => raw39568step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39568step2 raw39568step1; decide +kernel
      have hl : raw39568step2Labels = raw39568step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39568step1 raw39568step1Labels permutation29 permutation6
    _ = mixedMoment B node134 node134Labels := by rfl

def raw39569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39569Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39569step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw39569step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39569step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39569 raw39569Labels = mixedMoment B node5503 node5503Labels := by
  calc
    mixedMoment B raw39569 raw39569Labels = mixedMoment B raw39569step0 raw39569step0Labels := by
      have hz : ∀ j, raw39569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39569step0 = (fun i j => raw39569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39569step0 raw39569; decide +kernel
      have hl : raw39569step0Labels = raw39569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39569 raw39569Labels permutation346 hz
    mixedMoment B raw39569step0 raw39569step0Labels = mixedMoment B raw39569step1 raw39569step1Labels := by
      have ha : raw39569step1 = (fun i j => raw39569step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39569step1 raw39569step0; decide +kernel
      have hl : raw39569step1Labels = raw39569step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39569step0 raw39569step0Labels permutation42 permutation7
    mixedMoment B raw39569step1 raw39569step1Labels = mixedMoment B raw39569step2 raw39569step2Labels := by
      have ha : raw39569step2 = -raw39569step1 := by apply Matrix.ext; change ∀ i j, raw39569step2 i j = -(raw39569step1 i j); unfold raw39569step2 raw39569step1; decide +kernel
      have hl : raw39569step2Labels = raw39569step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5503 node5503Labels := by rfl

def raw39570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39570Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39570step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw39570step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw39570step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39570 raw39570Labels = mixedMoment B node222 node222Labels := by
  calc
    mixedMoment B raw39570 raw39570Labels = mixedMoment B raw39570step0 raw39570step0Labels := by
      have hz : ∀ j, raw39570 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39570step0 = (fun i j => raw39570 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39570step0 raw39570; decide +kernel
      have hl : raw39570step0Labels = raw39570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39570 raw39570Labels permutation346 hz
    mixedMoment B raw39570step0 raw39570step0Labels = mixedMoment B raw39570step1 raw39570step1Labels := by
      have ha : raw39570step1 = (fun i j => raw39570step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39570step1 raw39570step0; decide +kernel
      have hl : raw39570step1Labels = raw39570step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39570step0 raw39570step0Labels permutation40 permutation7
    mixedMoment B raw39570step1 raw39570step1Labels = mixedMoment B raw39570step2 raw39570step2Labels := by
      have ha : raw39570step2 = -raw39570step1 := by apply Matrix.ext; change ∀ i j, raw39570step2 i j = -(raw39570step1 i j); unfold raw39570step2 raw39570step1; decide +kernel
      have hl : raw39570step2Labels = raw39570step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node222 node222Labels := by rfl

def raw39571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39571Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39571step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39571step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39571 raw39571Labels = mixedMoment B node117 node117Labels := by
  calc
    mixedMoment B raw39571 raw39571Labels = mixedMoment B raw39571step0 raw39571step0Labels := by
      have hz : ∀ j, raw39571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39571step0 = (fun i j => raw39571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39571step0 raw39571; decide +kernel
      have hl : raw39571step0Labels = raw39571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39571 raw39571Labels permutation346 hz
    mixedMoment B raw39571step0 raw39571step0Labels = mixedMoment B raw39571step1 raw39571step1Labels := by
      have ha : raw39571step1 = (fun i j => raw39571step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39571step1 raw39571step0; decide +kernel
      have hl : raw39571step1Labels = raw39571step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39571step0 raw39571step0Labels permutation139 permutation6
    _ = mixedMoment B node117 node117Labels := by rfl

def raw39572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw39572Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw39572step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw39572step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39572step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39572 raw39572Labels = mixedMoment B node192 node192Labels := by
  calc
    mixedMoment B raw39572 raw39572Labels = mixedMoment B raw39572step0 raw39572step0Labels := by
      have hz : ∀ j, raw39572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39572step0 = (fun i j => raw39572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39572step0 raw39572; decide +kernel
      have hl : raw39572step0Labels = raw39572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39572 raw39572Labels permutation346 hz
    mixedMoment B raw39572step0 raw39572step0Labels = mixedMoment B raw39572step1 raw39572step1Labels := by
      have ha : raw39572step1 = (fun i j => raw39572step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39572step1 raw39572step0; decide +kernel
      have hl : raw39572step1Labels = raw39572step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39572step0 raw39572step0Labels permutation51 permutation7
    mixedMoment B raw39572step1 raw39572step1Labels = mixedMoment B raw39572step2 raw39572step2Labels := by
      have ha : raw39572step2 = -raw39572step1 := by apply Matrix.ext; change ∀ i j, raw39572step2 i j = -(raw39572step1 i j); unfold raw39572step2 raw39572step1; decide +kernel
      have hl : raw39572step2Labels = raw39572step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node192 node192Labels := by rfl

def raw39573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw39573Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw39573step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw39573step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw39573step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39573 raw39573Labels = mixedMoment B node239 node239Labels := by
  calc
    mixedMoment B raw39573 raw39573Labels = mixedMoment B raw39573step0 raw39573step0Labels := by
      have hz : ∀ j, raw39573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39573step0 = (fun i j => raw39573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39573step0 raw39573; decide +kernel
      have hl : raw39573step0Labels = raw39573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39573 raw39573Labels permutation346 hz
    mixedMoment B raw39573step0 raw39573step0Labels = mixedMoment B raw39573step1 raw39573step1Labels := by
      have ha : raw39573step1 = (fun i j => raw39573step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39573step1 raw39573step0; decide +kernel
      have hl : raw39573step1Labels = raw39573step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39573step0 raw39573step0Labels permutation54 permutation7
    mixedMoment B raw39573step1 raw39573step1Labels = mixedMoment B raw39573step2 raw39573step2Labels := by
      have ha : raw39573step2 = -raw39573step1 := by apply Matrix.ext; change ∀ i j, raw39573step2 i j = -(raw39573step1 i j); unfold raw39573step2 raw39573step1; decide +kernel
      have hl : raw39573step2Labels = raw39573step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node239 node239Labels := by rfl

def raw39574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39574Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39574step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39574step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39574step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39574 raw39574Labels = mixedMoment B node260 node260Labels := by
  calc
    mixedMoment B raw39574 raw39574Labels = mixedMoment B raw39574step0 raw39574step0Labels := by
      have hz : ∀ j, raw39574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39574step0 = (fun i j => raw39574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39574step0 raw39574; decide +kernel
      have hl : raw39574step0Labels = raw39574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39574 raw39574Labels permutation346 hz
    mixedMoment B raw39574step0 raw39574step0Labels = mixedMoment B raw39574step1 raw39574step1Labels := by
      have ha : raw39574step1 = (fun i j => raw39574step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39574step1 raw39574step0; decide +kernel
      have hl : raw39574step1Labels = raw39574step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39574step0 raw39574step0Labels permutation48 permutation7
    mixedMoment B raw39574step1 raw39574step1Labels = mixedMoment B raw39574step2 raw39574step2Labels := by
      have ha : raw39574step2 = -raw39574step1 := by apply Matrix.ext; change ∀ i j, raw39574step2 i j = -(raw39574step1 i j); unfold raw39574step2 raw39574step1; decide +kernel
      have hl : raw39574step2Labels = raw39574step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node260 node260Labels := by rfl

def raw39575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39575Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw39575step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39575step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39575 raw39575Labels = mixedMoment B node212 node212Labels := by
  calc
    mixedMoment B raw39575 raw39575Labels = mixedMoment B raw39575step0 raw39575step0Labels := by
      have ha : raw39575step0 = (fun i j => raw39575 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39575step0 raw39575; decide +kernel
      have hl : raw39575step0Labels = raw39575Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39575 raw39575Labels permutation195 permutation7
    mixedMoment B raw39575step0 raw39575step0Labels = mixedMoment B raw39575step1 raw39575step1Labels := by
      have ha : raw39575step1 = -raw39575step0 := by apply Matrix.ext; change ∀ i j, raw39575step1 i j = -(raw39575step0 i j); unfold raw39575step1 raw39575step0; decide +kernel
      have hl : raw39575step1Labels = raw39575step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node212 node212Labels := by rfl

def raw39576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39576Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw39576step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39576step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39576 raw39576Labels = mixedMoment B node221 node221Labels := by
  calc
    mixedMoment B raw39576 raw39576Labels = mixedMoment B raw39576step0 raw39576step0Labels := by
      have ha : raw39576step0 = (fun i j => raw39576 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39576step0 raw39576; decide +kernel
      have hl : raw39576step0Labels = raw39576Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39576 raw39576Labels permutation195 permutation7
    mixedMoment B raw39576step0 raw39576step0Labels = mixedMoment B raw39576step1 raw39576step1Labels := by
      have ha : raw39576step1 = -raw39576step0 := by apply Matrix.ext; change ∀ i j, raw39576step1 i j = -(raw39576step0 i j); unfold raw39576step1 raw39576step0; decide +kernel
      have hl : raw39576step1Labels = raw39576step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node221 node221Labels := by rfl

def raw39577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw39577Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw39577step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39577step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39577 raw39577Labels = mixedMoment B node164 node164Labels := by
  calc
    mixedMoment B raw39577 raw39577Labels = mixedMoment B raw39577step0 raw39577step0Labels := by
      have ha : raw39577step0 = (fun i j => raw39577 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39577step0 raw39577; decide +kernel
      have hl : raw39577step0Labels = raw39577Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39577 raw39577Labels permutation195 permutation7
    mixedMoment B raw39577step0 raw39577step0Labels = mixedMoment B raw39577step1 raw39577step1Labels := by
      have ha : raw39577step1 = -raw39577step0 := by apply Matrix.ext; change ∀ i j, raw39577step1 i j = -(raw39577step0 i j); unfold raw39577step1 raw39577step0; decide +kernel
      have hl : raw39577step1Labels = raw39577step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node164 node164Labels := by rfl

def raw39578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39578Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39578step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39578step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39578step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw39578step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39578step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw39578step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39578 raw39578Labels = mixedMoment B node154 node154Labels := by
  calc
    mixedMoment B raw39578 raw39578Labels = mixedMoment B raw39578step0 raw39578step0Labels := by
      have hz : ∀ j, raw39578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39578step0 = (fun i j => raw39578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39578step0 raw39578; decide +kernel
      have hl : raw39578step0Labels = raw39578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39578 raw39578Labels permutation434 hz
    mixedMoment B raw39578step0 raw39578step0Labels = mixedMoment B raw39578step1 raw39578step1Labels := by
      have hz : ∀ j, raw39578step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39578step1 = (fun i j => raw39578step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39578step1 raw39578step0; decide +kernel
      have hl : raw39578step1Labels = raw39578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39578step0 raw39578step0Labels permutation80 hz
    mixedMoment B raw39578step1 raw39578step1Labels = mixedMoment B raw39578step2 raw39578step2Labels := by
      have hz : ∀ j, raw39578step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39578step2 = (fun i j => raw39578step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39578step2 raw39578step1; decide +kernel
      have hl : raw39578step2Labels = raw39578step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39578step1 raw39578step1Labels permutation14 hz
    mixedMoment B raw39578step2 raw39578step2Labels = mixedMoment B raw39578step3 raw39578step3Labels := by
      have ha : raw39578step3 = (fun i j => raw39578step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39578step3 raw39578step2; decide +kernel
      have hl : raw39578step3Labels = raw39578step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39578step2 raw39578step2Labels permutation7 permutation7
    _ = mixedMoment B node154 node154Labels := by rfl

def raw39579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw39579Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw39579step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw39579step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39579step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![2, 3, -5]]
def raw39579step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39579step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw39579step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39579 raw39579Labels = mixedMoment B node41 node41Labels := by
  calc
    mixedMoment B raw39579 raw39579Labels = mixedMoment B raw39579step0 raw39579step0Labels := by
      have hz : ∀ j, raw39579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39579step0 = (fun i j => raw39579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39579step0 raw39579; decide +kernel
      have hl : raw39579step0Labels = raw39579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39579 raw39579Labels permutation434 hz
    mixedMoment B raw39579step0 raw39579step0Labels = mixedMoment B raw39579step1 raw39579step1Labels := by
      have hz : ∀ j, raw39579step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39579step1 = (fun i j => raw39579step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39579step1 raw39579step0; decide +kernel
      have hl : raw39579step1Labels = raw39579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39579step0 raw39579step0Labels permutation80 hz
    mixedMoment B raw39579step1 raw39579step1Labels = mixedMoment B raw39579step2 raw39579step2Labels := by
      have hz : ∀ j, raw39579step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39579step2 = (fun i j => raw39579step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39579step2 raw39579step1; decide +kernel
      have hl : raw39579step2Labels = raw39579step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39579step1 raw39579step1Labels permutation14 hz
    mixedMoment B raw39579step2 raw39579step2Labels = mixedMoment B raw39579step3 raw39579step3Labels := by
      have ha : raw39579step3 = (fun i j => raw39579step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39579step3 raw39579step2; decide +kernel
      have hl : raw39579step3Labels = raw39579step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39579step2 raw39579step2Labels permutation7 permutation6
    _ = mixedMoment B node41 node41Labels := by rfl

def raw39580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39580Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39580step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39580step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw39580step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39580 raw39580Labels = mixedMoment B node102 node102Labels := by
  calc
    mixedMoment B raw39580 raw39580Labels = mixedMoment B raw39580step0 raw39580step0Labels := by
      have hz : ∀ j, raw39580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39580step0 = (fun i j => raw39580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39580step0 raw39580; decide +kernel
      have hl : raw39580step0Labels = raw39580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39580 raw39580Labels permutation346 hz
    mixedMoment B raw39580step0 raw39580step0Labels = mixedMoment B raw39580step1 raw39580step1Labels := by
      have hz : ∀ j, raw39580step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39580step1 = (fun i j => raw39580step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39580step1 raw39580step0; decide +kernel
      have hl : raw39580step1Labels = raw39580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39580step0 raw39580step0Labels permutation56 hz
    mixedMoment B raw39580step1 raw39580step1Labels = mixedMoment B raw39580step2 raw39580step2Labels := by
      have ha : raw39580step2 = (fun i j => raw39580step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39580step2 raw39580step1; decide +kernel
      have hl : raw39580step2Labels = raw39580step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39580step1 raw39580step1Labels permutation25 permutation6
    _ = mixedMoment B node102 node102Labels := by rfl

def raw39581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39581Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39581step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39581step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw39581step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39581 raw39581Labels = mixedMoment B node143 node143Labels := by
  calc
    mixedMoment B raw39581 raw39581Labels = mixedMoment B raw39581step0 raw39581step0Labels := by
      have hz : ∀ j, raw39581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39581step0 = (fun i j => raw39581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39581step0 raw39581; decide +kernel
      have hl : raw39581step0Labels = raw39581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39581 raw39581Labels permutation346 hz
    mixedMoment B raw39581step0 raw39581step0Labels = mixedMoment B raw39581step1 raw39581step1Labels := by
      have hz : ∀ j, raw39581step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39581step1 = (fun i j => raw39581step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39581step1 raw39581step0; decide +kernel
      have hl : raw39581step1Labels = raw39581step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39581step0 raw39581step0Labels permutation56 hz
    mixedMoment B raw39581step1 raw39581step1Labels = mixedMoment B raw39581step2 raw39581step2Labels := by
      have ha : raw39581step2 = (fun i j => raw39581step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39581step2 raw39581step1; decide +kernel
      have hl : raw39581step2Labels = raw39581step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39581step1 raw39581step1Labels permutation31 permutation7
    _ = mixedMoment B node143 node143Labels := by rfl

def raw39582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw39582Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw39582step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw39582step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39582step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39582 raw39582Labels = mixedMoment B node32 node32Labels := by
  calc
    mixedMoment B raw39582 raw39582Labels = mixedMoment B raw39582step0 raw39582step0Labels := by
      have hz : ∀ j, raw39582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39582step0 = (fun i j => raw39582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39582step0 raw39582; decide +kernel
      have hl : raw39582step0Labels = raw39582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39582 raw39582Labels permutation346 hz
    mixedMoment B raw39582step0 raw39582step0Labels = mixedMoment B raw39582step1 raw39582step1Labels := by
      have hz : ∀ j, raw39582step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39582step1 = (fun i j => raw39582step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39582step1 raw39582step0; decide +kernel
      have hl : raw39582step1Labels = raw39582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39582step0 raw39582step0Labels permutation56 hz
    mixedMoment B raw39582step1 raw39582step1Labels = mixedMoment B raw39582step2 raw39582step2Labels := by
      have ha : raw39582step2 = (fun i j => raw39582step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39582step2 raw39582step1; decide +kernel
      have hl : raw39582step2Labels = raw39582step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39582step1 raw39582step1Labels permutation29 permutation6
    _ = mixedMoment B node32 node32Labels := by rfl

def raw39583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39583Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39583step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39583step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39583step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39583 raw39583Labels = mixedMoment B node19 node19Labels := by
  calc
    mixedMoment B raw39583 raw39583Labels = mixedMoment B raw39583step0 raw39583step0Labels := by
      have hz : ∀ j, raw39583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39583step0 = (fun i j => raw39583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39583step0 raw39583; decide +kernel
      have hl : raw39583step0Labels = raw39583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39583 raw39583Labels permutation346 hz
    mixedMoment B raw39583step0 raw39583step0Labels = mixedMoment B raw39583step1 raw39583step1Labels := by
      have hz : ∀ j, raw39583step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39583step1 = (fun i j => raw39583step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39583step1 raw39583step0; decide +kernel
      have hl : raw39583step1Labels = raw39583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39583step0 raw39583step0Labels permutation56 hz
    mixedMoment B raw39583step1 raw39583step1Labels = mixedMoment B raw39583step2 raw39583step2Labels := by
      have ha : raw39583step2 = (fun i j => raw39583step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39583step2 raw39583step1; decide +kernel
      have hl : raw39583step2Labels = raw39583step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39583step1 raw39583step1Labels permutation31 permutation6
    _ = mixedMoment B node19 node19Labels := by rfl

def raw39584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw39584Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw39584step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw39584step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw39584step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39584 raw39584Labels = mixedMoment B node73 node73Labels := by
  calc
    mixedMoment B raw39584 raw39584Labels = mixedMoment B raw39584step0 raw39584step0Labels := by
      have hz : ∀ j, raw39584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39584step0 = (fun i j => raw39584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39584step0 raw39584; decide +kernel
      have hl : raw39584step0Labels = raw39584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39584 raw39584Labels permutation346 hz
    mixedMoment B raw39584step0 raw39584step0Labels = mixedMoment B raw39584step1 raw39584step1Labels := by
      have hz : ∀ j, raw39584step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39584step1 = (fun i j => raw39584step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39584step1 raw39584step0; decide +kernel
      have hl : raw39584step1Labels = raw39584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39584step0 raw39584step0Labels permutation56 hz
    mixedMoment B raw39584step1 raw39584step1Labels = mixedMoment B raw39584step2 raw39584step2Labels := by
      have ha : raw39584step2 = (fun i j => raw39584step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39584step2 raw39584step1; decide +kernel
      have hl : raw39584step2Labels = raw39584step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39584step1 raw39584step1Labels permutation17 permutation6
    _ = mixedMoment B node73 node73Labels := by rfl

def raw39585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw39585Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw39585step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw39585step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39585step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39585 raw39585Labels = mixedMoment B node97 node97Labels := by
  calc
    mixedMoment B raw39585 raw39585Labels = mixedMoment B raw39585step0 raw39585step0Labels := by
      have hz : ∀ j, raw39585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39585step0 = (fun i j => raw39585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39585step0 raw39585; decide +kernel
      have hl : raw39585step0Labels = raw39585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39585 raw39585Labels permutation346 hz
    mixedMoment B raw39585step0 raw39585step0Labels = mixedMoment B raw39585step1 raw39585step1Labels := by
      have hz : ∀ j, raw39585step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39585step1 = (fun i j => raw39585step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39585step1 raw39585step0; decide +kernel
      have hl : raw39585step1Labels = raw39585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39585step0 raw39585step0Labels permutation56 hz
    mixedMoment B raw39585step1 raw39585step1Labels = mixedMoment B raw39585step2 raw39585step2Labels := by
      have ha : raw39585step2 = (fun i j => raw39585step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39585step2 raw39585step1; decide +kernel
      have hl : raw39585step2Labels = raw39585step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39585step1 raw39585step1Labels permutation17 permutation6
    _ = mixedMoment B node97 node97Labels := by rfl

def raw39586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw39586Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw39586step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw39586step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw39586step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw39586step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39586 raw39586Labels = mixedMoment B node197 node197Labels := by
  calc
    mixedMoment B raw39586 raw39586Labels = mixedMoment B raw39586step0 raw39586step0Labels := by
      have hz : ∀ j, raw39586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39586step0 = (fun i j => raw39586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39586step0 raw39586; decide +kernel
      have hl : raw39586step0Labels = raw39586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39586 raw39586Labels permutation346 hz
    mixedMoment B raw39586step0 raw39586step0Labels = mixedMoment B raw39586step1 raw39586step1Labels := by
      have hz : ∀ j, raw39586step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39586step1 = (fun i j => raw39586step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39586step1 raw39586step0; decide +kernel
      have hl : raw39586step1Labels = raw39586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39586step0 raw39586step0Labels permutation56 hz
    mixedMoment B raw39586step1 raw39586step1Labels = mixedMoment B raw39586step2 raw39586step2Labels := by
      have ha : raw39586step2 = (fun i j => raw39586step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39586step2 raw39586step1; decide +kernel
      have hl : raw39586step2Labels = raw39586step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39586step1 raw39586step1Labels permutation13 permutation7
    mixedMoment B raw39586step2 raw39586step2Labels = mixedMoment B raw39586step3 raw39586step3Labels := by
      have ha : raw39586step3 = -raw39586step2 := by apply Matrix.ext; change ∀ i j, raw39586step3 i j = -(raw39586step2 i j); unfold raw39586step3 raw39586step2; decide +kernel
      have hl : raw39586step3Labels = raw39586step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node197 node197Labels := by rfl

def raw39587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39587Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39587step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39587step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw39587step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39587step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39587step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39587 raw39587Labels = mixedMoment B node249 node249Labels := by
  calc
    mixedMoment B raw39587 raw39587Labels = mixedMoment B raw39587step0 raw39587step0Labels := by
      have hz : ∀ j, raw39587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39587step0 = (fun i j => raw39587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39587step0 raw39587; decide +kernel
      have hl : raw39587step0Labels = raw39587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39587 raw39587Labels permutation346 hz
    mixedMoment B raw39587step0 raw39587step0Labels = mixedMoment B raw39587step1 raw39587step1Labels := by
      have hz : ∀ j, raw39587step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39587step1 = (fun i j => raw39587step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39587step1 raw39587step0; decide +kernel
      have hl : raw39587step1Labels = raw39587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39587step0 raw39587step0Labels permutation56 hz
    mixedMoment B raw39587step1 raw39587step1Labels = mixedMoment B raw39587step2 raw39587step2Labels := by
      have ha : raw39587step2 = (fun i j => raw39587step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39587step2 raw39587step1; decide +kernel
      have hl : raw39587step2Labels = raw39587step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39587step1 raw39587step1Labels permutation13 permutation7
    mixedMoment B raw39587step2 raw39587step2Labels = mixedMoment B raw39587step3 raw39587step3Labels := by
      have ha : raw39587step3 = -raw39587step2 := by apply Matrix.ext; change ∀ i j, raw39587step3 i j = -(raw39587step2 i j); unfold raw39587step3 raw39587step2; decide +kernel
      have hl : raw39587step3Labels = raw39587step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node249 node249Labels := by rfl

def raw39588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39588Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39588step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39588step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39588 raw39588Labels = mixedMoment B node14 node14Labels := by
  calc
    mixedMoment B raw39588 raw39588Labels = mixedMoment B raw39588step0 raw39588step0Labels := by
      have hz : ∀ j, raw39588 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39588step0 = (fun i j => raw39588 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39588step0 raw39588; decide +kernel
      have hl : raw39588step0Labels = raw39588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39588 raw39588Labels permutation265 hz
    mixedMoment B raw39588step0 raw39588step0Labels = mixedMoment B raw39588step1 raw39588step1Labels := by
      have ha : raw39588step1 = (fun i j => raw39588step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39588step1 raw39588step0; decide +kernel
      have hl : raw39588step1Labels = raw39588step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39588step0 raw39588step0Labels permutation149 permutation6
    _ = mixedMoment B node14 node14Labels := by rfl

def raw39589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw39589Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw39589step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39589step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39589 raw39589Labels = mixedMoment B node67 node67Labels := by
  calc
    mixedMoment B raw39589 raw39589Labels = mixedMoment B raw39589step0 raw39589step0Labels := by
      have hz : ∀ j, raw39589 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39589step0 = (fun i j => raw39589 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39589step0 raw39589; decide +kernel
      have hl : raw39589step0Labels = raw39589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39589 raw39589Labels permutation265 hz
    mixedMoment B raw39589step0 raw39589step0Labels = mixedMoment B raw39589step1 raw39589step1Labels := by
      have ha : raw39589step1 = (fun i j => raw39589step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39589step1 raw39589step0; decide +kernel
      have hl : raw39589step1Labels = raw39589step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39589step0 raw39589step0Labels permutation95 permutation6
    _ = mixedMoment B node67 node67Labels := by rfl

def raw39590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw39590Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw39590step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39590step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39590 raw39590Labels = mixedMoment B node87 node87Labels := by
  calc
    mixedMoment B raw39590 raw39590Labels = mixedMoment B raw39590step0 raw39590step0Labels := by
      have hz : ∀ j, raw39590 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39590step0 = (fun i j => raw39590 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39590step0 raw39590; decide +kernel
      have hl : raw39590step0Labels = raw39590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39590 raw39590Labels permutation265 hz
    mixedMoment B raw39590step0 raw39590step0Labels = mixedMoment B raw39590step1 raw39590step1Labels := by
      have ha : raw39590step1 = (fun i j => raw39590step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39590step1 raw39590step0; decide +kernel
      have hl : raw39590step1Labels = raw39590step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39590step0 raw39590step0Labels permutation97 permutation6
    _ = mixedMoment B node87 node87Labels := by rfl

def raw39591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39591Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39591step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw39591step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39591step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39591 raw39591Labels = mixedMoment B node227 node227Labels := by
  calc
    mixedMoment B raw39591 raw39591Labels = mixedMoment B raw39591step0 raw39591step0Labels := by
      have hz : ∀ j, raw39591 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39591step0 = (fun i j => raw39591 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39591step0 raw39591; decide +kernel
      have hl : raw39591step0Labels = raw39591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39591 raw39591Labels permutation265 hz
    mixedMoment B raw39591step0 raw39591step0Labels = mixedMoment B raw39591step1 raw39591step1Labels := by
      have ha : raw39591step1 = (fun i j => raw39591step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39591step1 raw39591step0; decide +kernel
      have hl : raw39591step1Labels = raw39591step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39591step0 raw39591step0Labels permutation36 permutation7
    mixedMoment B raw39591step1 raw39591step1Labels = mixedMoment B raw39591step2 raw39591step2Labels := by
      have ha : raw39591step2 = -raw39591step1 := by apply Matrix.ext; change ∀ i j, raw39591step2 i j = -(raw39591step1 i j); unfold raw39591step2 raw39591step1; decide +kernel
      have hl : raw39591step2Labels = raw39591step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node227 node227Labels := by rfl

def raw39592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39592Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39592step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39592step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39592 raw39592Labels = mixedMoment B node60 node60Labels := by
  calc
    mixedMoment B raw39592 raw39592Labels = mixedMoment B raw39592step0 raw39592step0Labels := by
      have hz : ∀ j, raw39592 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39592step0 = (fun i j => raw39592 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39592step0 raw39592; decide +kernel
      have hl : raw39592step0Labels = raw39592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39592 raw39592Labels permutation265 hz
    mixedMoment B raw39592step0 raw39592step0Labels = mixedMoment B raw39592step1 raw39592step1Labels := by
      have ha : raw39592step1 = (fun i j => raw39592step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39592step1 raw39592step0; decide +kernel
      have hl : raw39592step1Labels = raw39592step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39592step0 raw39592step0Labels permutation97 permutation6
    _ = mixedMoment B node60 node60Labels := by rfl

def raw39593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw39593Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw39593step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw39593step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw39593step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39593 raw39593Labels = mixedMoment B node169 node169Labels := by
  calc
    mixedMoment B raw39593 raw39593Labels = mixedMoment B raw39593step0 raw39593step0Labels := by
      have hz : ∀ j, raw39593 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39593step0 = (fun i j => raw39593 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39593step0 raw39593; decide +kernel
      have hl : raw39593step0Labels = raw39593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39593 raw39593Labels permutation265 hz
    mixedMoment B raw39593step0 raw39593step0Labels = mixedMoment B raw39593step1 raw39593step1Labels := by
      have ha : raw39593step1 = (fun i j => raw39593step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39593step1 raw39593step0; decide +kernel
      have hl : raw39593step1Labels = raw39593step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39593step0 raw39593step0Labels permutation37 permutation7
    mixedMoment B raw39593step1 raw39593step1Labels = mixedMoment B raw39593step2 raw39593step2Labels := by
      have ha : raw39593step2 = -raw39593step1 := by apply Matrix.ext; change ∀ i j, raw39593step2 i j = -(raw39593step1 i j); unfold raw39593step2 raw39593step1; decide +kernel
      have hl : raw39593step2Labels = raw39593step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node169 node169Labels := by rfl

def raw39594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39594Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39594step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39594 raw39594Labels = mixedMoment B node58 node58Labels := by
  calc
    mixedMoment B raw39594 raw39594Labels = mixedMoment B raw39594step0 raw39594step0Labels := by
      have ha : raw39594step0 = (fun i j => raw39594 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39594step0 raw39594; decide +kernel
      have hl : raw39594step0Labels = raw39594Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39594 raw39594Labels permutation502 permutation6
    _ = mixedMoment B node58 node58Labels := by rfl

def raw39595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39595Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39595step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw39595step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw39595step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39595step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw39595step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39595 raw39595Labels = mixedMoment B node102 node102Labels := by
  calc
    mixedMoment B raw39595 raw39595Labels = mixedMoment B raw39595step0 raw39595step0Labels := by
      have hz : ∀ j, raw39595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39595step0 = (fun i j => raw39595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39595step0 raw39595; decide +kernel
      have hl : raw39595step0Labels = raw39595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39595 raw39595Labels permutation434 hz
    mixedMoment B raw39595step0 raw39595step0Labels = mixedMoment B raw39595step1 raw39595step1Labels := by
      have hz : ∀ j, raw39595step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39595step1 = (fun i j => raw39595step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39595step1 raw39595step0; decide +kernel
      have hl : raw39595step1Labels = raw39595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39595step0 raw39595step0Labels permutation80 hz
    mixedMoment B raw39595step1 raw39595step1Labels = mixedMoment B raw39595step2 raw39595step2Labels := by
      have ha : raw39595step2 = (fun i j => raw39595step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39595step2 raw39595step1; decide +kernel
      have hl : raw39595step2Labels = raw39595step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39595step1 raw39595step1Labels permutation13 permutation7
    mixedMoment B raw39595step2 raw39595step2Labels = mixedMoment B raw39595step3 raw39595step3Labels := by
      have ha : raw39595step3 = -raw39595step2 := by apply Matrix.ext; change ∀ i j, raw39595step3 i j = -(raw39595step2 i j); unfold raw39595step3 raw39595step2; decide +kernel
      have hl : raw39595step3Labels = raw39595step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node102 node102Labels := by rfl

def raw39596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39596Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39596step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw39596step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw39596step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39596step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39596step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39596 raw39596Labels = mixedMoment B node97 node97Labels := by
  calc
    mixedMoment B raw39596 raw39596Labels = mixedMoment B raw39596step0 raw39596step0Labels := by
      have hz : ∀ j, raw39596 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39596step0 = (fun i j => raw39596 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39596step0 raw39596; decide +kernel
      have hl : raw39596step0Labels = raw39596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39596 raw39596Labels permutation434 hz
    mixedMoment B raw39596step0 raw39596step0Labels = mixedMoment B raw39596step1 raw39596step1Labels := by
      have hz : ∀ j, raw39596step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39596step1 = (fun i j => raw39596step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39596step1 raw39596step0; decide +kernel
      have hl : raw39596step1Labels = raw39596step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39596step0 raw39596step0Labels permutation80 hz
    mixedMoment B raw39596step1 raw39596step1Labels = mixedMoment B raw39596step2 raw39596step2Labels := by
      have ha : raw39596step2 = (fun i j => raw39596step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39596step2 raw39596step1; decide +kernel
      have hl : raw39596step2Labels = raw39596step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39596step1 raw39596step1Labels permutation11 permutation7
    mixedMoment B raw39596step2 raw39596step2Labels = mixedMoment B raw39596step3 raw39596step3Labels := by
      have ha : raw39596step3 = -raw39596step2 := by apply Matrix.ext; change ∀ i j, raw39596step3 i j = -(raw39596step2 i j); unfold raw39596step3 raw39596step2; decide +kernel
      have hl : raw39596step3Labels = raw39596step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node97 node97Labels := by rfl

def raw39597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39597Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39597step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw39597step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw39597step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39597step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39597step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39597 raw39597Labels = mixedMoment B node76 node76Labels := by
  calc
    mixedMoment B raw39597 raw39597Labels = mixedMoment B raw39597step0 raw39597step0Labels := by
      have hz : ∀ j, raw39597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39597step0 = (fun i j => raw39597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39597step0 raw39597; decide +kernel
      have hl : raw39597step0Labels = raw39597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39597 raw39597Labels permutation434 hz
    mixedMoment B raw39597step0 raw39597step0Labels = mixedMoment B raw39597step1 raw39597step1Labels := by
      have hz : ∀ j, raw39597step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39597step1 = (fun i j => raw39597step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39597step1 raw39597step0; decide +kernel
      have hl : raw39597step1Labels = raw39597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39597step0 raw39597step0Labels permutation80 hz
    mixedMoment B raw39597step1 raw39597step1Labels = mixedMoment B raw39597step2 raw39597step2Labels := by
      have ha : raw39597step2 = (fun i j => raw39597step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39597step2 raw39597step1; decide +kernel
      have hl : raw39597step2Labels = raw39597step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39597step1 raw39597step1Labels permutation11 permutation7
    mixedMoment B raw39597step2 raw39597step2Labels = mixedMoment B raw39597step3 raw39597step3Labels := by
      have ha : raw39597step3 = -raw39597step2 := by apply Matrix.ext; change ∀ i j, raw39597step3 i j = -(raw39597step2 i j); unfold raw39597step3 raw39597step2; decide +kernel
      have hl : raw39597step3Labels = raw39597step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node76 node76Labels := by rfl

def raw39598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39598Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39598step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw39598step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39598step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39598 raw39598Labels = mixedMoment B node60 node60Labels := by
  calc
    mixedMoment B raw39598 raw39598Labels = mixedMoment B raw39598step0 raw39598step0Labels := by
      have hz : ∀ j, raw39598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39598step0 = (fun i j => raw39598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39598step0 raw39598; decide +kernel
      have hl : raw39598step0Labels = raw39598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39598 raw39598Labels permutation346 hz
    mixedMoment B raw39598step0 raw39598step0Labels = mixedMoment B raw39598step1 raw39598step1Labels := by
      have ha : raw39598step1 = (fun i j => raw39598step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39598step1 raw39598step0; decide +kernel
      have hl : raw39598step1Labels = raw39598step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39598step0 raw39598step0Labels permutation41 permutation7
    mixedMoment B raw39598step1 raw39598step1Labels = mixedMoment B raw39598step2 raw39598step2Labels := by
      have ha : raw39598step2 = -raw39598step1 := by apply Matrix.ext; change ∀ i j, raw39598step2 i j = -(raw39598step1 i j); unfold raw39598step2 raw39598step1; decide +kernel
      have hl : raw39598step2Labels = raw39598step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node60 node60Labels := by rfl

def raw39599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39599Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39599step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw39599step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39599step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39599 raw39599Labels = mixedMoment B node87 node87Labels := by
  calc
    mixedMoment B raw39599 raw39599Labels = mixedMoment B raw39599step0 raw39599step0Labels := by
      have hz : ∀ j, raw39599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39599step0 = (fun i j => raw39599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39599step0 raw39599; decide +kernel
      have hl : raw39599step0Labels = raw39599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39599 raw39599Labels permutation346 hz
    mixedMoment B raw39599step0 raw39599step0Labels = mixedMoment B raw39599step1 raw39599step1Labels := by
      have ha : raw39599step1 = (fun i j => raw39599step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39599step1 raw39599step0; decide +kernel
      have hl : raw39599step1Labels = raw39599step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39599step0 raw39599step0Labels permutation49 permutation7
    mixedMoment B raw39599step1 raw39599step1Labels = mixedMoment B raw39599step2 raw39599step2Labels := by
      have ha : raw39599step2 = -raw39599step1 := by apply Matrix.ext; change ∀ i j, raw39599step2 i j = -(raw39599step1 i j); unfold raw39599step2 raw39599step1; decide +kernel
      have hl : raw39599step2Labels = raw39599step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node87 node87Labels := by rfl

def raw39600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39600Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw39600step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39600step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39600 raw39600Labels = mixedMoment B node58 node58Labels := by
  calc
    mixedMoment B raw39600 raw39600Labels = mixedMoment B raw39600step0 raw39600step0Labels := by
      have ha : raw39600step0 = (fun i j => raw39600 (permutation197 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39600step0 raw39600; decide +kernel
      have hl : raw39600step0Labels = raw39600Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39600 raw39600Labels permutation197 permutation7
    mixedMoment B raw39600step0 raw39600step0Labels = mixedMoment B raw39600step1 raw39600step1Labels := by
      have ha : raw39600step1 = -raw39600step0 := by apply Matrix.ext; change ∀ i j, raw39600step1 i j = -(raw39600step0 i j); unfold raw39600step1 raw39600step0; decide +kernel
      have hl : raw39600step1Labels = raw39600step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node58 node58Labels := by rfl

def raw39601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39601Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39601step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw39601step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39601step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39601 raw39601Labels = mixedMoment B node101 node101Labels := by
  calc
    mixedMoment B raw39601 raw39601Labels = mixedMoment B raw39601step0 raw39601step0Labels := by
      have hz : ∀ j, raw39601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39601step0 = (fun i j => raw39601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39601step0 raw39601; decide +kernel
      have hl : raw39601step0Labels = raw39601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39601 raw39601Labels permutation434 hz
    mixedMoment B raw39601step0 raw39601step0Labels = mixedMoment B raw39601step1 raw39601step1Labels := by
      have ha : raw39601step1 = (fun i j => raw39601step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39601step1 raw39601step0; decide +kernel
      have hl : raw39601step1Labels = raw39601step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39601step0 raw39601step0Labels permutation53 permutation7
    mixedMoment B raw39601step1 raw39601step1Labels = mixedMoment B raw39601step2 raw39601step2Labels := by
      have ha : raw39601step2 = -raw39601step1 := by apply Matrix.ext; change ∀ i j, raw39601step2 i j = -(raw39601step1 i j); unfold raw39601step2 raw39601step1; decide +kernel
      have hl : raw39601step2Labels = raw39601step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node101 node101Labels := by rfl

def raw39602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39602Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39602step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39602step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39602step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39602 raw39602Labels = mixedMoment B node74 node74Labels := by
  calc
    mixedMoment B raw39602 raw39602Labels = mixedMoment B raw39602step0 raw39602step0Labels := by
      have hz : ∀ j, raw39602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39602step0 = (fun i j => raw39602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39602step0 raw39602; decide +kernel
      have hl : raw39602step0Labels = raw39602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39602 raw39602Labels permutation434 hz
    mixedMoment B raw39602step0 raw39602step0Labels = mixedMoment B raw39602step1 raw39602step1Labels := by
      have ha : raw39602step1 = (fun i j => raw39602step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39602step1 raw39602step0; decide +kernel
      have hl : raw39602step1Labels = raw39602step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39602step0 raw39602step0Labels permutation46 permutation7
    mixedMoment B raw39602step1 raw39602step1Labels = mixedMoment B raw39602step2 raw39602step2Labels := by
      have ha : raw39602step2 = -raw39602step1 := by apply Matrix.ext; change ∀ i j, raw39602step2 i j = -(raw39602step1 i j); unfold raw39602step2 raw39602step1; decide +kernel
      have hl : raw39602step2Labels = raw39602step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node74 node74Labels := by rfl

def raw39603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39603Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39603step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw39603step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw39603step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39603step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39603step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39603 raw39603Labels = mixedMoment B node103 node103Labels := by
  calc
    mixedMoment B raw39603 raw39603Labels = mixedMoment B raw39603step0 raw39603step0Labels := by
      have hz : ∀ j, raw39603 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39603step0 = (fun i j => raw39603 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39603step0 raw39603; decide +kernel
      have hl : raw39603step0Labels = raw39603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39603 raw39603Labels permutation434 hz
    mixedMoment B raw39603step0 raw39603step0Labels = mixedMoment B raw39603step1 raw39603step1Labels := by
      have hz : ∀ j, raw39603step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39603step1 = (fun i j => raw39603step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39603step1 raw39603step0; decide +kernel
      have hl : raw39603step1Labels = raw39603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39603step0 raw39603step0Labels permutation80 hz
    mixedMoment B raw39603step1 raw39603step1Labels = mixedMoment B raw39603step2 raw39603step2Labels := by
      have ha : raw39603step2 = (fun i j => raw39603step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39603step2 raw39603step1; decide +kernel
      have hl : raw39603step2Labels = raw39603step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39603step1 raw39603step1Labels permutation12 permutation7
    mixedMoment B raw39603step2 raw39603step2Labels = mixedMoment B raw39603step3 raw39603step3Labels := by
      have ha : raw39603step3 = -raw39603step2 := by apply Matrix.ext; change ∀ i j, raw39603step3 i j = -(raw39603step2 i j); unfold raw39603step3 raw39603step2; decide +kernel
      have hl : raw39603step3Labels = raw39603step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node103 node103Labels := by rfl

def raw39604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39604Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39604step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39604step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39604step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39604step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39604step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39604 raw39604Labels = mixedMoment B node98 node98Labels := by
  calc
    mixedMoment B raw39604 raw39604Labels = mixedMoment B raw39604step0 raw39604step0Labels := by
      have hz : ∀ j, raw39604 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39604step0 = (fun i j => raw39604 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39604step0 raw39604; decide +kernel
      have hl : raw39604step0Labels = raw39604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39604 raw39604Labels permutation434 hz
    mixedMoment B raw39604step0 raw39604step0Labels = mixedMoment B raw39604step1 raw39604step1Labels := by
      have hz : ∀ j, raw39604step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39604step1 = (fun i j => raw39604step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39604step1 raw39604step0; decide +kernel
      have hl : raw39604step1Labels = raw39604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39604step0 raw39604step0Labels permutation80 hz
    mixedMoment B raw39604step1 raw39604step1Labels = mixedMoment B raw39604step2 raw39604step2Labels := by
      have ha : raw39604step2 = (fun i j => raw39604step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39604step2 raw39604step1; decide +kernel
      have hl : raw39604step2Labels = raw39604step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39604step1 raw39604step1Labels permutation10 permutation7
    mixedMoment B raw39604step2 raw39604step2Labels = mixedMoment B raw39604step3 raw39604step3Labels := by
      have ha : raw39604step3 = -raw39604step2 := by apply Matrix.ext; change ∀ i j, raw39604step3 i j = -(raw39604step2 i j); unfold raw39604step3 raw39604step2; decide +kernel
      have hl : raw39604step3Labels = raw39604step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node98 node98Labels := by rfl

def raw39605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39605Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39605step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw39605step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39605step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw39605step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39605step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39605step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39605 raw39605Labels = mixedMoment B node75 node75Labels := by
  calc
    mixedMoment B raw39605 raw39605Labels = mixedMoment B raw39605step0 raw39605step0Labels := by
      have hz : ∀ j, raw39605 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39605step0 = (fun i j => raw39605 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39605step0 raw39605; decide +kernel
      have hl : raw39605step0Labels = raw39605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39605 raw39605Labels permutation434 hz
    mixedMoment B raw39605step0 raw39605step0Labels = mixedMoment B raw39605step1 raw39605step1Labels := by
      have hz : ∀ j, raw39605step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39605step1 = (fun i j => raw39605step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39605step1 raw39605step0; decide +kernel
      have hl : raw39605step1Labels = raw39605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39605step0 raw39605step0Labels permutation80 hz
    mixedMoment B raw39605step1 raw39605step1Labels = mixedMoment B raw39605step2 raw39605step2Labels := by
      have ha : raw39605step2 = (fun i j => raw39605step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39605step2 raw39605step1; decide +kernel
      have hl : raw39605step2Labels = raw39605step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39605step1 raw39605step1Labels permutation10 permutation7
    mixedMoment B raw39605step2 raw39605step2Labels = mixedMoment B raw39605step3 raw39605step3Labels := by
      have ha : raw39605step3 = -raw39605step2 := by apply Matrix.ext; change ∀ i j, raw39605step3 i j = -(raw39605step2 i j); unfold raw39605step3 raw39605step2; decide +kernel
      have hl : raw39605step3Labels = raw39605step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node75 node75Labels := by rfl

def raw39606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39606Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39606step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39606step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39606 raw39606Labels = mixedMoment B node91 node91Labels := by
  calc
    mixedMoment B raw39606 raw39606Labels = mixedMoment B raw39606step0 raw39606step0Labels := by
      have ha : raw39606step0 = (fun i j => raw39606 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39606step0 raw39606; decide +kernel
      have hl : raw39606step0Labels = raw39606Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39606 raw39606Labels permutation246 permutation7
    mixedMoment B raw39606step0 raw39606step0Labels = mixedMoment B raw39606step1 raw39606step1Labels := by
      have ha : raw39606step1 = -raw39606step0 := by apply Matrix.ext; change ∀ i j, raw39606step1 i j = -(raw39606step0 i j); unfold raw39606step1 raw39606step0; decide +kernel
      have hl : raw39606step1Labels = raw39606step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node91 node91Labels := by rfl

def raw39607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39607Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39607step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw39607step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw39607step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39607step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39607 raw39607Labels = mixedMoment B node5504 node5504Labels := by
  calc
    mixedMoment B raw39607 raw39607Labels = mixedMoment B raw39607step0 raw39607step0Labels := by
      have hz : ∀ j, raw39607 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39607step0 = (fun i j => raw39607 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39607step0 raw39607; decide +kernel
      have hl : raw39607step0Labels = raw39607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39607 raw39607Labels permutation434 hz
    mixedMoment B raw39607step0 raw39607step0Labels = mixedMoment B raw39607step1 raw39607step1Labels := by
      have hz : ∀ j, raw39607step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39607step1 = (fun i j => raw39607step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39607step1 raw39607step0; decide +kernel
      have hl : raw39607step1Labels = raw39607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39607step0 raw39607step0Labels permutation80 hz
    mixedMoment B raw39607step1 raw39607step1Labels = mixedMoment B raw39607step2 raw39607step2Labels := by
      have ha : raw39607step2 = (fun i j => raw39607step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39607step2 raw39607step1; decide +kernel
      have hl : raw39607step2Labels = raw39607step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39607step1 raw39607step1Labels permutation12 permutation7
    mixedMoment B raw39607step2 raw39607step2Labels = mixedMoment B raw39607step3 raw39607step3Labels := by
      have ha : raw39607step3 = -raw39607step2 := by apply Matrix.ext; change ∀ i j, raw39607step3 i j = -(raw39607step2 i j); unfold raw39607step3 raw39607step2; decide +kernel
      have hl : raw39607step3Labels = raw39607step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5504 node5504Labels := by rfl

def raw39608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39608Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39608step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw39608step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw39608step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39608step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw39608step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39608 raw39608Labels = mixedMoment B node94 node94Labels := by
  calc
    mixedMoment B raw39608 raw39608Labels = mixedMoment B raw39608step0 raw39608step0Labels := by
      have hz : ∀ j, raw39608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39608step0 = (fun i j => raw39608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39608step0 raw39608; decide +kernel
      have hl : raw39608step0Labels = raw39608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39608 raw39608Labels permutation434 hz
    mixedMoment B raw39608step0 raw39608step0Labels = mixedMoment B raw39608step1 raw39608step1Labels := by
      have hz : ∀ j, raw39608step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39608step1 = (fun i j => raw39608step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39608step1 raw39608step0; decide +kernel
      have hl : raw39608step1Labels = raw39608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39608step0 raw39608step0Labels permutation80 hz
    mixedMoment B raw39608step1 raw39608step1Labels = mixedMoment B raw39608step2 raw39608step2Labels := by
      have ha : raw39608step2 = (fun i j => raw39608step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39608step2 raw39608step1; decide +kernel
      have hl : raw39608step2Labels = raw39608step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39608step1 raw39608step1Labels permutation10 permutation7
    mixedMoment B raw39608step2 raw39608step2Labels = mixedMoment B raw39608step3 raw39608step3Labels := by
      have ha : raw39608step3 = -raw39608step2 := by apply Matrix.ext; change ∀ i j, raw39608step3 i j = -(raw39608step2 i j); unfold raw39608step3 raw39608step2; decide +kernel
      have hl : raw39608step3Labels = raw39608step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node94 node94Labels := by rfl

def raw39609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39609Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39609step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw39609step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39609step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39609 raw39609Labels = mixedMoment B node93 node93Labels := by
  calc
    mixedMoment B raw39609 raw39609Labels = mixedMoment B raw39609step0 raw39609step0Labels := by
      have hz : ∀ j, raw39609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39609step0 = (fun i j => raw39609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39609step0 raw39609; decide +kernel
      have hl : raw39609step0Labels = raw39609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39609 raw39609Labels permutation346 hz
    mixedMoment B raw39609step0 raw39609step0Labels = mixedMoment B raw39609step1 raw39609step1Labels := by
      have ha : raw39609step1 = (fun i j => raw39609step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39609step1 raw39609step0; decide +kernel
      have hl : raw39609step1Labels = raw39609step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39609step0 raw39609step0Labels permutation51 permutation7
    mixedMoment B raw39609step1 raw39609step1Labels = mixedMoment B raw39609step2 raw39609step2Labels := by
      have ha : raw39609step2 = -raw39609step1 := by apply Matrix.ext; change ∀ i j, raw39609step2 i j = -(raw39609step1 i j); unfold raw39609step2 raw39609step1; decide +kernel
      have hl : raw39609step2Labels = raw39609step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node93 node93Labels := by rfl

def raw39610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39610Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39610step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39610step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39610step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw39610step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39610step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw39610step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39610 raw39610Labels = mixedMoment B node104 node104Labels := by
  calc
    mixedMoment B raw39610 raw39610Labels = mixedMoment B raw39610step0 raw39610step0Labels := by
      have hz : ∀ j, raw39610 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39610step0 = (fun i j => raw39610 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39610step0 raw39610; decide +kernel
      have hl : raw39610step0Labels = raw39610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39610 raw39610Labels permutation434 hz
    mixedMoment B raw39610step0 raw39610step0Labels = mixedMoment B raw39610step1 raw39610step1Labels := by
      have hz : ∀ j, raw39610step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39610step1 = (fun i j => raw39610step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39610step1 raw39610step0; decide +kernel
      have hl : raw39610step1Labels = raw39610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39610step0 raw39610step0Labels permutation80 hz
    mixedMoment B raw39610step1 raw39610step1Labels = mixedMoment B raw39610step2 raw39610step2Labels := by
      have hz : ∀ j, raw39610step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39610step2 = (fun i j => raw39610step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39610step2 raw39610step1; decide +kernel
      have hl : raw39610step2Labels = raw39610step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39610step1 raw39610step1Labels permutation14 hz
    mixedMoment B raw39610step2 raw39610step2Labels = mixedMoment B raw39610step3 raw39610step3Labels := by
      have ha : raw39610step3 = (fun i j => raw39610step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39610step3 raw39610step2; decide +kernel
      have hl : raw39610step3Labels = raw39610step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39610step2 raw39610step2Labels permutation5 permutation6
    _ = mixedMoment B node104 node104Labels := by rfl

def raw39611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39611Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39611step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39611step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39611step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw39611step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39611step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw39611step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39611step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw39611step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39611 raw39611Labels = mixedMoment B node100 node100Labels := by
  calc
    mixedMoment B raw39611 raw39611Labels = mixedMoment B raw39611step0 raw39611step0Labels := by
      have hz : ∀ j, raw39611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39611step0 = (fun i j => raw39611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39611step0 raw39611; decide +kernel
      have hl : raw39611step0Labels = raw39611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39611 raw39611Labels permutation434 hz
    mixedMoment B raw39611step0 raw39611step0Labels = mixedMoment B raw39611step1 raw39611step1Labels := by
      have hz : ∀ j, raw39611step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39611step1 = (fun i j => raw39611step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39611step1 raw39611step0; decide +kernel
      have hl : raw39611step1Labels = raw39611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39611step0 raw39611step0Labels permutation80 hz
    mixedMoment B raw39611step1 raw39611step1Labels = mixedMoment B raw39611step2 raw39611step2Labels := by
      have hz : ∀ j, raw39611step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39611step2 = (fun i j => raw39611step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39611step2 raw39611step1; decide +kernel
      have hl : raw39611step2Labels = raw39611step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39611step1 raw39611step1Labels permutation14 hz
    mixedMoment B raw39611step2 raw39611step2Labels = mixedMoment B raw39611step3 raw39611step3Labels := by
      have ha : raw39611step3 = (fun i j => raw39611step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39611step3 raw39611step2; decide +kernel
      have hl : raw39611step3Labels = raw39611step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39611step2 raw39611step2Labels permutation2 permutation7
    mixedMoment B raw39611step3 raw39611step3Labels = mixedMoment B raw39611step4 raw39611step4Labels := by
      have ha : raw39611step4 = -raw39611step3 := by apply Matrix.ext; change ∀ i j, raw39611step4 i j = -(raw39611step3 i j); unfold raw39611step4 raw39611step3; decide +kernel
      have hl : raw39611step4Labels = raw39611step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node100 node100Labels := by rfl

def raw39612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw39612Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw39612step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw39612step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39612step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![2, 3, -5]]
def raw39612step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39612step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw39612step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39612 raw39612Labels = mixedMoment B node37 node37Labels := by
  calc
    mixedMoment B raw39612 raw39612Labels = mixedMoment B raw39612step0 raw39612step0Labels := by
      have hz : ∀ j, raw39612 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39612step0 = (fun i j => raw39612 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39612step0 raw39612; decide +kernel
      have hl : raw39612step0Labels = raw39612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39612 raw39612Labels permutation434 hz
    mixedMoment B raw39612step0 raw39612step0Labels = mixedMoment B raw39612step1 raw39612step1Labels := by
      have hz : ∀ j, raw39612step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39612step1 = (fun i j => raw39612step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39612step1 raw39612step0; decide +kernel
      have hl : raw39612step1Labels = raw39612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39612step0 raw39612step0Labels permutation80 hz
    mixedMoment B raw39612step1 raw39612step1Labels = mixedMoment B raw39612step2 raw39612step2Labels := by
      have hz : ∀ j, raw39612step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39612step2 = (fun i j => raw39612step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39612step2 raw39612step1; decide +kernel
      have hl : raw39612step2Labels = raw39612step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39612step1 raw39612step1Labels permutation14 hz
    mixedMoment B raw39612step2 raw39612step2Labels = mixedMoment B raw39612step3 raw39612step3Labels := by
      have ha : raw39612step3 = (fun i j => raw39612step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39612step3 raw39612step2; decide +kernel
      have hl : raw39612step3Labels = raw39612step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39612step2 raw39612step2Labels permutation7 permutation6
    _ = mixedMoment B node37 node37Labels := by rfl

def raw39613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39613Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39613step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39613step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw39613step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39613 raw39613Labels = mixedMoment B node16 node16Labels := by
  calc
    mixedMoment B raw39613 raw39613Labels = mixedMoment B raw39613step0 raw39613step0Labels := by
      have hz : ∀ j, raw39613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39613step0 = (fun i j => raw39613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39613step0 raw39613; decide +kernel
      have hl : raw39613step0Labels = raw39613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39613 raw39613Labels permutation346 hz
    mixedMoment B raw39613step0 raw39613step0Labels = mixedMoment B raw39613step1 raw39613step1Labels := by
      have hz : ∀ j, raw39613step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39613step1 = (fun i j => raw39613step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39613step1 raw39613step0; decide +kernel
      have hl : raw39613step1Labels = raw39613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39613step0 raw39613step0Labels permutation56 hz
    mixedMoment B raw39613step1 raw39613step1Labels = mixedMoment B raw39613step2 raw39613step2Labels := by
      have ha : raw39613step2 = (fun i j => raw39613step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39613step2 raw39613step1; decide +kernel
      have hl : raw39613step2Labels = raw39613step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39613step1 raw39613step1Labels permutation31 permutation6
    _ = mixedMoment B node16 node16Labels := by rfl

def raw39614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw39614Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw39614step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw39614step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw39614step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39614 raw39614Labels = mixedMoment B node88 node88Labels := by
  calc
    mixedMoment B raw39614 raw39614Labels = mixedMoment B raw39614step0 raw39614step0Labels := by
      have hz : ∀ j, raw39614 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39614step0 = (fun i j => raw39614 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39614step0 raw39614; decide +kernel
      have hl : raw39614step0Labels = raw39614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39614 raw39614Labels permutation346 hz
    mixedMoment B raw39614step0 raw39614step0Labels = mixedMoment B raw39614step1 raw39614step1Labels := by
      have hz : ∀ j, raw39614step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39614step1 = (fun i j => raw39614step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39614step1 raw39614step0; decide +kernel
      have hl : raw39614step1Labels = raw39614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39614step0 raw39614step0Labels permutation56 hz
    mixedMoment B raw39614step1 raw39614step1Labels = mixedMoment B raw39614step2 raw39614step2Labels := by
      have ha : raw39614step2 = (fun i j => raw39614step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39614step2 raw39614step1; decide +kernel
      have hl : raw39614step2Labels = raw39614step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39614step1 raw39614step1Labels permutation17 permutation6
    _ = mixedMoment B node88 node88Labels := by rfl

def raw39615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39615Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39615step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39615step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw39615step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39615step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39615step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39615 raw39615Labels = mixedMoment B node99 node99Labels := by
  calc
    mixedMoment B raw39615 raw39615Labels = mixedMoment B raw39615step0 raw39615step0Labels := by
      have hz : ∀ j, raw39615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39615step0 = (fun i j => raw39615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39615step0 raw39615; decide +kernel
      have hl : raw39615step0Labels = raw39615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39615 raw39615Labels permutation346 hz
    mixedMoment B raw39615step0 raw39615step0Labels = mixedMoment B raw39615step1 raw39615step1Labels := by
      have hz : ∀ j, raw39615step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39615step1 = (fun i j => raw39615step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39615step1 raw39615step0; decide +kernel
      have hl : raw39615step1Labels = raw39615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39615step0 raw39615step0Labels permutation56 hz
    mixedMoment B raw39615step1 raw39615step1Labels = mixedMoment B raw39615step2 raw39615step2Labels := by
      have ha : raw39615step2 = (fun i j => raw39615step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39615step2 raw39615step1; decide +kernel
      have hl : raw39615step2Labels = raw39615step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39615step1 raw39615step1Labels permutation12 permutation7
    mixedMoment B raw39615step2 raw39615step2Labels = mixedMoment B raw39615step3 raw39615step3Labels := by
      have ha : raw39615step3 = -raw39615step2 := by apply Matrix.ext; change ∀ i j, raw39615step3 i j = -(raw39615step2 i j); unfold raw39615step3 raw39615step2; decide +kernel
      have hl : raw39615step3Labels = raw39615step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node99 node99Labels := by rfl

def raw39616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39616Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39616step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw39616step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39616 raw39616Labels = mixedMoment B node59 node59Labels := by
  calc
    mixedMoment B raw39616 raw39616Labels = mixedMoment B raw39616step0 raw39616step0Labels := by
      have hz : ∀ j, raw39616 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39616step0 = (fun i j => raw39616 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39616step0 raw39616; decide +kernel
      have hl : raw39616step0Labels = raw39616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39616 raw39616Labels permutation265 hz
    mixedMoment B raw39616step0 raw39616step0Labels = mixedMoment B raw39616step1 raw39616step1Labels := by
      have ha : raw39616step1 = (fun i j => raw39616step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39616step1 raw39616step0; decide +kernel
      have hl : raw39616step1Labels = raw39616step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39616step0 raw39616step0Labels permutation97 permutation6
    _ = mixedMoment B node59 node59Labels := by rfl

def raw39617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39617Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39617step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw39617step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw39617step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39617step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39617 raw39617Labels = mixedMoment B node19 node19Labels := by
  calc
    mixedMoment B raw39617 raw39617Labels = mixedMoment B raw39617step0 raw39617step0Labels := by
      have hz : ∀ j, raw39617 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39617step0 = (fun i j => raw39617 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39617step0 raw39617; decide +kernel
      have hl : raw39617step0Labels = raw39617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39617 raw39617Labels permutation434 hz
    mixedMoment B raw39617step0 raw39617step0Labels = mixedMoment B raw39617step1 raw39617step1Labels := by
      have hz : ∀ j, raw39617step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39617step1 = (fun i j => raw39617step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39617step1 raw39617step0; decide +kernel
      have hl : raw39617step1Labels = raw39617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39617step0 raw39617step0Labels permutation80 hz
    mixedMoment B raw39617step1 raw39617step1Labels = mixedMoment B raw39617step2 raw39617step2Labels := by
      have ha : raw39617step2 = (fun i j => raw39617step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39617step2 raw39617step1; decide +kernel
      have hl : raw39617step2Labels = raw39617step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39617step1 raw39617step1Labels permutation11 permutation7
    mixedMoment B raw39617step2 raw39617step2Labels = mixedMoment B raw39617step3 raw39617step3Labels := by
      have ha : raw39617step3 = -raw39617step2 := by apply Matrix.ext; change ∀ i j, raw39617step3 i j = -(raw39617step2 i j); unfold raw39617step3 raw39617step2; decide +kernel
      have hl : raw39617step3Labels = raw39617step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node19 node19Labels := by rfl

def raw39618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39618Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39618step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw39618step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39618step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39618 raw39618Labels = mixedMoment B node14 node14Labels := by
  calc
    mixedMoment B raw39618 raw39618Labels = mixedMoment B raw39618step0 raw39618step0Labels := by
      have hz : ∀ j, raw39618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39618step0 = (fun i j => raw39618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39618step0 raw39618; decide +kernel
      have hl : raw39618step0Labels = raw39618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39618 raw39618Labels permutation346 hz
    mixedMoment B raw39618step0 raw39618step0Labels = mixedMoment B raw39618step1 raw39618step1Labels := by
      have ha : raw39618step1 = (fun i j => raw39618step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39618step1 raw39618step0; decide +kernel
      have hl : raw39618step1Labels = raw39618step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39618step0 raw39618step0Labels permutation53 permutation7
    mixedMoment B raw39618step1 raw39618step1Labels = mixedMoment B raw39618step2 raw39618step2Labels := by
      have ha : raw39618step2 = -raw39618step1 := by apply Matrix.ext; change ∀ i j, raw39618step2 i j = -(raw39618step1 i j); unfold raw39618step2 raw39618step1; decide +kernel
      have hl : raw39618step2Labels = raw39618step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node14 node14Labels := by rfl

def raw39619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39619Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39619step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39619step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39619step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39619 raw39619Labels = mixedMoment B node12 node12Labels := by
  calc
    mixedMoment B raw39619 raw39619Labels = mixedMoment B raw39619step0 raw39619step0Labels := by
      have hz : ∀ j, raw39619 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39619step0 = (fun i j => raw39619 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39619step0 raw39619; decide +kernel
      have hl : raw39619step0Labels = raw39619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39619 raw39619Labels permutation434 hz
    mixedMoment B raw39619step0 raw39619step0Labels = mixedMoment B raw39619step1 raw39619step1Labels := by
      have ha : raw39619step1 = (fun i j => raw39619step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39619step1 raw39619step0; decide +kernel
      have hl : raw39619step1Labels = raw39619step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39619step0 raw39619step0Labels permutation46 permutation7
    mixedMoment B raw39619step1 raw39619step1Labels = mixedMoment B raw39619step2 raw39619step2Labels := by
      have ha : raw39619step2 = -raw39619step1 := by apply Matrix.ext; change ∀ i j, raw39619step2 i j = -(raw39619step1 i j); unfold raw39619step2 raw39619step1; decide +kernel
      have hl : raw39619step2Labels = raw39619step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node12 node12Labels := by rfl

def raw39620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39620Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39620step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw39620step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw39620step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39620step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39620 raw39620Labels = mixedMoment B node17 node17Labels := by
  calc
    mixedMoment B raw39620 raw39620Labels = mixedMoment B raw39620step0 raw39620step0Labels := by
      have hz : ∀ j, raw39620 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39620step0 = (fun i j => raw39620 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39620step0 raw39620; decide +kernel
      have hl : raw39620step0Labels = raw39620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39620 raw39620Labels permutation434 hz
    mixedMoment B raw39620step0 raw39620step0Labels = mixedMoment B raw39620step1 raw39620step1Labels := by
      have hz : ∀ j, raw39620step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39620step1 = (fun i j => raw39620step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39620step1 raw39620step0; decide +kernel
      have hl : raw39620step1Labels = raw39620step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39620step0 raw39620step0Labels permutation80 hz
    mixedMoment B raw39620step1 raw39620step1Labels = mixedMoment B raw39620step2 raw39620step2Labels := by
      have ha : raw39620step2 = (fun i j => raw39620step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39620step2 raw39620step1; decide +kernel
      have hl : raw39620step2Labels = raw39620step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39620step1 raw39620step1Labels permutation10 permutation7
    mixedMoment B raw39620step2 raw39620step2Labels = mixedMoment B raw39620step3 raw39620step3Labels := by
      have ha : raw39620step3 = -raw39620step2 := by apply Matrix.ext; change ∀ i j, raw39620step3 i j = -(raw39620step2 i j); unfold raw39620step3 raw39620step2; decide +kernel
      have hl : raw39620step3Labels = raw39620step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node17 node17Labels := by rfl

def raw39621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39621Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39621step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39621step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39621step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39621 raw39621Labels = mixedMoment B node15 node15Labels := by
  calc
    mixedMoment B raw39621 raw39621Labels = mixedMoment B raw39621step0 raw39621step0Labels := by
      have hz : ∀ j, raw39621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39621step0 = (fun i j => raw39621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39621step0 raw39621; decide +kernel
      have hl : raw39621step0Labels = raw39621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39621 raw39621Labels permutation346 hz
    mixedMoment B raw39621step0 raw39621step0Labels = mixedMoment B raw39621step1 raw39621step1Labels := by
      have ha : raw39621step1 = (fun i j => raw39621step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39621step1 raw39621step0; decide +kernel
      have hl : raw39621step1Labels = raw39621step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39621step0 raw39621step0Labels permutation54 permutation7
    mixedMoment B raw39621step1 raw39621step1Labels = mixedMoment B raw39621step2 raw39621step2Labels := by
      have ha : raw39621step2 = -raw39621step1 := by apply Matrix.ext; change ∀ i j, raw39621step2 i j = -(raw39621step1 i j); unfold raw39621step2 raw39621step1; decide +kernel
      have hl : raw39621step2Labels = raw39621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node15 node15Labels := by rfl

def raw39622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39622Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39622step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39622step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39622 raw39622Labels = mixedMoment B node8 node8Labels := by
  calc
    mixedMoment B raw39622 raw39622Labels = mixedMoment B raw39622step0 raw39622step0Labels := by
      have ha : raw39622step0 = (fun i j => raw39622 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39622step0 raw39622; decide +kernel
      have hl : raw39622step0Labels = raw39622Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39622 raw39622Labels permutation224 permutation7
    mixedMoment B raw39622step0 raw39622step0Labels = mixedMoment B raw39622step1 raw39622step1Labels := by
      have ha : raw39622step1 = -raw39622step0 := by apply Matrix.ext; change ∀ i j, raw39622step1 i j = -(raw39622step0 i j); unfold raw39622step1 raw39622step0; decide +kernel
      have hl : raw39622step1Labels = raw39622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node8 node8Labels := by rfl

def raw39623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39623Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw39623step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw39623step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw39623step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39623 raw39623Labels = mixedMoment B node9 node9Labels := by
  calc
    mixedMoment B raw39623 raw39623Labels = mixedMoment B raw39623step0 raw39623step0Labels := by
      have hz : ∀ j, raw39623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39623step0 = (fun i j => raw39623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39623step0 raw39623; decide +kernel
      have hl : raw39623step0Labels = raw39623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39623 raw39623Labels permutation434 hz
    mixedMoment B raw39623step0 raw39623step0Labels = mixedMoment B raw39623step1 raw39623step1Labels := by
      have ha : raw39623step1 = (fun i j => raw39623step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39623step1 raw39623step0; decide +kernel
      have hl : raw39623step1Labels = raw39623step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39623step0 raw39623step0Labels permutation44 permutation7
    mixedMoment B raw39623step1 raw39623step1Labels = mixedMoment B raw39623step2 raw39623step2Labels := by
      have ha : raw39623step2 = -raw39623step1 := by apply Matrix.ext; change ∀ i j, raw39623step2 i j = -(raw39623step1 i j); unfold raw39623step2 raw39623step1; decide +kernel
      have hl : raw39623step2Labels = raw39623step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node9 node9Labels := by rfl

def raw39624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39624Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39624step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw39624step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw39624step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw39624step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39624 raw39624Labels = mixedMoment B node13 node13Labels := by
  calc
    mixedMoment B raw39624 raw39624Labels = mixedMoment B raw39624step0 raw39624step0Labels := by
      have hz : ∀ j, raw39624 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39624step0 = (fun i j => raw39624 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39624step0 raw39624; decide +kernel
      have hl : raw39624step0Labels = raw39624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39624 raw39624Labels permutation434 hz
    mixedMoment B raw39624step0 raw39624step0Labels = mixedMoment B raw39624step1 raw39624step1Labels := by
      have hz : ∀ j, raw39624step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39624step1 = (fun i j => raw39624step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39624step1 raw39624step0; decide +kernel
      have hl : raw39624step1Labels = raw39624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39624step0 raw39624step0Labels permutation80 hz
    mixedMoment B raw39624step1 raw39624step1Labels = mixedMoment B raw39624step2 raw39624step2Labels := by
      have ha : raw39624step2 = (fun i j => raw39624step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39624step2 raw39624step1; decide +kernel
      have hl : raw39624step2Labels = raw39624step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39624step1 raw39624step1Labels permutation10 permutation7
    mixedMoment B raw39624step2 raw39624step2Labels = mixedMoment B raw39624step3 raw39624step3Labels := by
      have ha : raw39624step3 = -raw39624step2 := by apply Matrix.ext; change ∀ i j, raw39624step3 i j = -(raw39624step2 i j); unfold raw39624step3 raw39624step2; decide +kernel
      have hl : raw39624step3Labels = raw39624step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node13 node13Labels := by rfl

def raw39625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw39625Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw39625step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw39625step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39625step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39625 raw39625Labels = mixedMoment B node11 node11Labels := by
  calc
    mixedMoment B raw39625 raw39625Labels = mixedMoment B raw39625step0 raw39625step0Labels := by
      have hz : ∀ j, raw39625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39625step0 = (fun i j => raw39625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39625step0 raw39625; decide +kernel
      have hl : raw39625step0Labels = raw39625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39625 raw39625Labels permutation346 hz
    mixedMoment B raw39625step0 raw39625step0Labels = mixedMoment B raw39625step1 raw39625step1Labels := by
      have ha : raw39625step1 = (fun i j => raw39625step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39625step1 raw39625step0; decide +kernel
      have hl : raw39625step1Labels = raw39625step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39625step0 raw39625step0Labels permutation51 permutation7
    mixedMoment B raw39625step1 raw39625step1Labels = mixedMoment B raw39625step2 raw39625step2Labels := by
      have ha : raw39625step2 = -raw39625step1 := by apply Matrix.ext; change ∀ i j, raw39625step2 i j = -(raw39625step1 i j); unfold raw39625step2 raw39625step1; decide +kernel
      have hl : raw39625step2Labels = raw39625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node11 node11Labels := by rfl

def raw39626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39626Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39626step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39626step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39626step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw39626step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39626step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def raw39626step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39626 raw39626Labels = mixedMoment B node20 node20Labels := by
  calc
    mixedMoment B raw39626 raw39626Labels = mixedMoment B raw39626step0 raw39626step0Labels := by
      have hz : ∀ j, raw39626 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39626step0 = (fun i j => raw39626 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39626step0 raw39626; decide +kernel
      have hl : raw39626step0Labels = raw39626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39626 raw39626Labels permutation434 hz
    mixedMoment B raw39626step0 raw39626step0Labels = mixedMoment B raw39626step1 raw39626step1Labels := by
      have hz : ∀ j, raw39626step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39626step1 = (fun i j => raw39626step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39626step1 raw39626step0; decide +kernel
      have hl : raw39626step1Labels = raw39626step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39626step0 raw39626step0Labels permutation80 hz
    mixedMoment B raw39626step1 raw39626step1Labels = mixedMoment B raw39626step2 raw39626step2Labels := by
      have hz : ∀ j, raw39626step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39626step2 = (fun i j => raw39626step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39626step2 raw39626step1; decide +kernel
      have hl : raw39626step2Labels = raw39626step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39626step1 raw39626step1Labels permutation14 hz
    mixedMoment B raw39626step2 raw39626step2Labels = mixedMoment B raw39626step3 raw39626step3Labels := by
      have ha : raw39626step3 = (fun i j => raw39626step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39626step3 raw39626step2; decide +kernel
      have hl : raw39626step3Labels = raw39626step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39626step2 raw39626step2Labels permutation7 permutation6
    _ = mixedMoment B node20 node20Labels := by rfl

def raw39627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39627Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39627step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39627step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw39627step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39627step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw39627step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39627 raw39627Labels = mixedMoment B node16 node16Labels := by
  calc
    mixedMoment B raw39627 raw39627Labels = mixedMoment B raw39627step0 raw39627step0Labels := by
      have hz : ∀ j, raw39627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39627step0 = (fun i j => raw39627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39627step0 raw39627; decide +kernel
      have hl : raw39627step0Labels = raw39627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39627 raw39627Labels permutation346 hz
    mixedMoment B raw39627step0 raw39627step0Labels = mixedMoment B raw39627step1 raw39627step1Labels := by
      have hz : ∀ j, raw39627step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39627step1 = (fun i j => raw39627step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39627step1 raw39627step0; decide +kernel
      have hl : raw39627step1Labels = raw39627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39627step0 raw39627step0Labels permutation56 hz
    mixedMoment B raw39627step1 raw39627step1Labels = mixedMoment B raw39627step2 raw39627step2Labels := by
      have ha : raw39627step2 = (fun i j => raw39627step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39627step2 raw39627step1; decide +kernel
      have hl : raw39627step2Labels = raw39627step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39627step1 raw39627step1Labels permutation13 permutation7
    mixedMoment B raw39627step2 raw39627step2Labels = mixedMoment B raw39627step3 raw39627step3Labels := by
      have ha : raw39627step3 = -raw39627step2 := by apply Matrix.ext; change ∀ i j, raw39627step3 i j = -(raw39627step2 i j); unfold raw39627step3 raw39627step2; decide +kernel
      have hl : raw39627step3Labels = raw39627step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node16 node16Labels := by rfl

def raw39628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw39628Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw39628step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw39628step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw39628step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39628step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw39628step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39628 raw39628Labels = mixedMoment B node18 node18Labels := by
  calc
    mixedMoment B raw39628 raw39628Labels = mixedMoment B raw39628step0 raw39628step0Labels := by
      have hz : ∀ j, raw39628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39628step0 = (fun i j => raw39628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39628step0 raw39628; decide +kernel
      have hl : raw39628step0Labels = raw39628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39628 raw39628Labels permutation346 hz
    mixedMoment B raw39628step0 raw39628step0Labels = mixedMoment B raw39628step1 raw39628step1Labels := by
      have hz : ∀ j, raw39628step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39628step1 = (fun i j => raw39628step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39628step1 raw39628step0; decide +kernel
      have hl : raw39628step1Labels = raw39628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39628step0 raw39628step0Labels permutation56 hz
    mixedMoment B raw39628step1 raw39628step1Labels = mixedMoment B raw39628step2 raw39628step2Labels := by
      have ha : raw39628step2 = (fun i j => raw39628step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39628step2 raw39628step1; decide +kernel
      have hl : raw39628step2Labels = raw39628step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39628step1 raw39628step1Labels permutation13 permutation7
    mixedMoment B raw39628step2 raw39628step2Labels = mixedMoment B raw39628step3 raw39628step3Labels := by
      have ha : raw39628step3 = -raw39628step2 := by apply Matrix.ext; change ∀ i j, raw39628step3 i j = -(raw39628step2 i j); unfold raw39628step3 raw39628step2; decide +kernel
      have hl : raw39628step3Labels = raw39628step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node18 node18Labels := by rfl

def raw39629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39629Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39629step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw39629step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39629step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![3, -3, 0]]
def raw39629step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39629step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw39629step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39629 raw39629Labels = mixedMoment B node5502 node5502Labels := by
  calc
    mixedMoment B raw39629 raw39629Labels = mixedMoment B raw39629step0 raw39629step0Labels := by
      have hz : ∀ j, raw39629 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39629step0 = (fun i j => raw39629 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39629step0 raw39629; decide +kernel
      have hl : raw39629step0Labels = raw39629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39629 raw39629Labels permutation520 hz
    mixedMoment B raw39629step0 raw39629step0Labels = mixedMoment B raw39629step1 raw39629step1Labels := by
      have hz : ∀ j, raw39629step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39629step1 = (fun i j => raw39629step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39629step1 raw39629step0; decide +kernel
      have hl : raw39629step1Labels = raw39629step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39629step0 raw39629step0Labels permutation104 hz
    mixedMoment B raw39629step1 raw39629step1Labels = mixedMoment B raw39629step2 raw39629step2Labels := by
      have hz : ∀ j, raw39629step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39629step2 = (fun i j => raw39629step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39629step2 raw39629step1; decide +kernel
      have hl : raw39629step2Labels = raw39629step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39629step1 raw39629step1Labels permutation20 hz
    mixedMoment B raw39629step2 raw39629step2Labels = mixedMoment B raw39629step3 raw39629step3Labels := by
      have ha : raw39629step3 = (fun i j => raw39629step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39629step3 raw39629step2; decide +kernel
      have hl : raw39629step3Labels = raw39629step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39629step2 raw39629step2Labels permutation7 permutation5
    _ = mixedMoment B node5502 node5502Labels := by rfl

def raw39630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39630Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39630step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw39630step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39630step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw39630step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39630step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39630step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39630 raw39630Labels = mixedMoment B node389 node389Labels := by
  calc
    mixedMoment B raw39630 raw39630Labels = mixedMoment B raw39630step0 raw39630step0Labels := by
      have hz : ∀ j, raw39630 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39630step0 = (fun i j => raw39630 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39630step0 raw39630; decide +kernel
      have hl : raw39630step0Labels = raw39630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39630 raw39630Labels permutation434 hz
    mixedMoment B raw39630step0 raw39630step0Labels = mixedMoment B raw39630step1 raw39630step1Labels := by
      have hz : ∀ j, raw39630step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39630step1 = (fun i j => raw39630step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39630step1 raw39630step0; decide +kernel
      have hl : raw39630step1Labels = raw39630step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39630step0 raw39630step0Labels permutation80 hz
    mixedMoment B raw39630step1 raw39630step1Labels = mixedMoment B raw39630step2 raw39630step2Labels := by
      have ha : raw39630step2 = (fun i j => raw39630step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39630step2 raw39630step1; decide +kernel
      have hl : raw39630step2Labels = raw39630step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39630step1 raw39630step1Labels permutation8 permutation5
    mixedMoment B raw39630step2 raw39630step2Labels = mixedMoment B raw39630step3 raw39630step3Labels := by
      have ha : raw39630step3 = -raw39630step2 := by apply Matrix.ext; change ∀ i j, raw39630step3 i j = -(raw39630step2 i j); unfold raw39630step3 raw39630step2; decide +kernel
      have hl : raw39630step3Labels = raw39630step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node389 node389Labels := by rfl

def raw39631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39631Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39631step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -3, 2], ![2, 0, -2]]
def raw39631step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw39631step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39631 raw39631Labels = mixedMoment B node385 node385Labels := by
  calc
    mixedMoment B raw39631 raw39631Labels = mixedMoment B raw39631step0 raw39631step0Labels := by
      have hz : ∀ j, raw39631 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39631step0 = (fun i j => raw39631 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39631step0 raw39631; decide +kernel
      have hl : raw39631step0Labels = raw39631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39631 raw39631Labels permutation434 hz
    mixedMoment B raw39631step0 raw39631step0Labels = mixedMoment B raw39631step1 raw39631step1Labels := by
      have hz : ∀ j, raw39631step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39631step1 = (fun i j => raw39631step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39631step1 raw39631step0; decide +kernel
      have hl : raw39631step1Labels = raw39631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39631step0 raw39631step0Labels permutation80 hz
    mixedMoment B raw39631step1 raw39631step1Labels = mixedMoment B raw39631step2 raw39631step2Labels := by
      have ha : raw39631step2 = (fun i j => raw39631step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39631step2 raw39631step1; decide +kernel
      have hl : raw39631step2Labels = raw39631step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39631step1 raw39631step1Labels permutation23 permutation4
    _ = mixedMoment B node385 node385Labels := by rfl

def raw39632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39632Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39632step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39632step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39632step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39632step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39632 raw39632Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw39632 raw39632Labels = mixedMoment B raw39632step0 raw39632step0Labels := by
      have hz : ∀ j, raw39632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39632step0 = (fun i j => raw39632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39632step0 raw39632; decide +kernel
      have hl : raw39632step0Labels = raw39632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39632 raw39632Labels permutation346 hz
    mixedMoment B raw39632step0 raw39632step0Labels = mixedMoment B raw39632step1 raw39632step1Labels := by
      have ha : raw39632step1 = (fun i j => raw39632step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39632step1 raw39632step0; decide +kernel
      have hl : raw39632step1Labels = raw39632step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39632step0 raw39632step0Labels permutation34 permutation5
    mixedMoment B raw39632step1 raw39632step1Labels = mixedMoment B raw39632step2 raw39632step2Labels := by
      have ha : raw39632step2 = -raw39632step1 := by apply Matrix.ext; change ∀ i j, raw39632step2 i j = -(raw39632step1 i j); unfold raw39632step2 raw39632step1; decide +kernel
      have hl : raw39632step2Labels = raw39632step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node377 node377Labels := by rfl

def raw39633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39633Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39633step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw39633step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39633step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39633 raw39633Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw39633 raw39633Labels = mixedMoment B raw39633step0 raw39633step0Labels := by
      have hz : ∀ j, raw39633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39633step0 = (fun i j => raw39633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39633step0 raw39633; decide +kernel
      have hl : raw39633step0Labels = raw39633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39633 raw39633Labels permutation346 hz
    mixedMoment B raw39633step0 raw39633step0Labels = mixedMoment B raw39633step1 raw39633step1Labels := by
      have ha : raw39633step1 = (fun i j => raw39633step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39633step1 raw39633step0; decide +kernel
      have hl : raw39633step1Labels = raw39633step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39633step0 raw39633step0Labels permutation32 permutation5
    mixedMoment B raw39633step1 raw39633step1Labels = mixedMoment B raw39633step2 raw39633step2Labels := by
      have ha : raw39633step2 = -raw39633step1 := by apply Matrix.ext; change ∀ i j, raw39633step2 i j = -(raw39633step1 i j); unfold raw39633step2 raw39633step1; decide +kernel
      have hl : raw39633step2Labels = raw39633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node387 node387Labels := by rfl

def raw39634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39634Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39634step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw39634step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39634step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39634 raw39634Labels = mixedMoment B node383 node383Labels := by
  calc
    mixedMoment B raw39634 raw39634Labels = mixedMoment B raw39634step0 raw39634step0Labels := by
      have hz : ∀ j, raw39634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39634step0 = (fun i j => raw39634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39634step0 raw39634; decide +kernel
      have hl : raw39634step0Labels = raw39634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39634 raw39634Labels permutation346 hz
    mixedMoment B raw39634step0 raw39634step0Labels = mixedMoment B raw39634step1 raw39634step1Labels := by
      have ha : raw39634step1 = (fun i j => raw39634step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39634step1 raw39634step0; decide +kernel
      have hl : raw39634step1Labels = raw39634step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39634step0 raw39634step0Labels permutation36 permutation5
    mixedMoment B raw39634step1 raw39634step1Labels = mixedMoment B raw39634step2 raw39634step2Labels := by
      have ha : raw39634step2 = -raw39634step1 := by apply Matrix.ext; change ∀ i j, raw39634step2 i j = -(raw39634step1 i j); unfold raw39634step2 raw39634step1; decide +kernel
      have hl : raw39634step2Labels = raw39634step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node383 node383Labels := by rfl

def raw39635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39635Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39635step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39635step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39635step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39635 raw39635Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39635 raw39635Labels = mixedMoment B raw39635step0 raw39635step0Labels := by
      have hz : ∀ j, raw39635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39635step0 = (fun i j => raw39635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39635step0 raw39635; decide +kernel
      have hl : raw39635step0Labels = raw39635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39635 raw39635Labels permutation346 hz
    mixedMoment B raw39635step0 raw39635step0Labels = mixedMoment B raw39635step1 raw39635step1Labels := by
      have ha : raw39635step1 = (fun i j => raw39635step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39635step1 raw39635step0; decide +kernel
      have hl : raw39635step1Labels = raw39635step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39635step0 raw39635step0Labels permutation37 permutation5
    mixedMoment B raw39635step1 raw39635step1Labels = mixedMoment B raw39635step2 raw39635step2Labels := by
      have ha : raw39635step2 = -raw39635step1 := by apply Matrix.ext; change ∀ i j, raw39635step2 i j = -(raw39635step1 i j); unfold raw39635step2 raw39635step1; decide +kernel
      have hl : raw39635step2Labels = raw39635step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node384 node384Labels := by rfl

def raw39636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39636Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw39636step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39636step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39636 raw39636Labels = mixedMoment B node382 node382Labels := by
  calc
    mixedMoment B raw39636 raw39636Labels = mixedMoment B raw39636step0 raw39636step0Labels := by
      have ha : raw39636step0 = (fun i j => raw39636 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39636step0 raw39636; decide +kernel
      have hl : raw39636step0Labels = raw39636Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39636 raw39636Labels permutation170 permutation5
    mixedMoment B raw39636step0 raw39636step0Labels = mixedMoment B raw39636step1 raw39636step1Labels := by
      have ha : raw39636step1 = -raw39636step0 := by apply Matrix.ext; change ∀ i j, raw39636step1 i j = -(raw39636step0 i j); unfold raw39636step1 raw39636step0; decide +kernel
      have hl : raw39636step1Labels = raw39636step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node382 node382Labels := by rfl

def raw39637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39637Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39637step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw39637step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw39637step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39637step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39637 raw39637Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw39637 raw39637Labels = mixedMoment B raw39637step0 raw39637step0Labels := by
      have hz : ∀ j, raw39637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39637step0 = (fun i j => raw39637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39637step0 raw39637; decide +kernel
      have hl : raw39637step0Labels = raw39637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39637 raw39637Labels permutation434 hz
    mixedMoment B raw39637step0 raw39637step0Labels = mixedMoment B raw39637step1 raw39637step1Labels := by
      have hz : ∀ j, raw39637step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39637step1 = (fun i j => raw39637step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39637step1 raw39637step0; decide +kernel
      have hl : raw39637step1Labels = raw39637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39637step0 raw39637step0Labels permutation80 hz
    mixedMoment B raw39637step1 raw39637step1Labels = mixedMoment B raw39637step2 raw39637step2Labels := by
      have ha : raw39637step2 = (fun i j => raw39637step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39637step2 raw39637step1; decide +kernel
      have hl : raw39637step2Labels = raw39637step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39637step1 raw39637step1Labels permutation10 permutation5
    mixedMoment B raw39637step2 raw39637step2Labels = mixedMoment B raw39637step3 raw39637step3Labels := by
      have ha : raw39637step3 = -raw39637step2 := by apply Matrix.ext; change ∀ i j, raw39637step3 i j = -(raw39637step2 i j); unfold raw39637step3 raw39637step2; decide +kernel
      have hl : raw39637step3Labels = raw39637step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node402 node402Labels := by rfl

def raw39638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39638Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39638step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw39638step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw39638step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39638step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39638step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39638 raw39638Labels = mixedMoment B node414 node414Labels := by
  calc
    mixedMoment B raw39638 raw39638Labels = mixedMoment B raw39638step0 raw39638step0Labels := by
      have hz : ∀ j, raw39638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39638step0 = (fun i j => raw39638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39638step0 raw39638; decide +kernel
      have hl : raw39638step0Labels = raw39638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39638 raw39638Labels permutation434 hz
    mixedMoment B raw39638step0 raw39638step0Labels = mixedMoment B raw39638step1 raw39638step1Labels := by
      have hz : ∀ j, raw39638step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39638step1 = (fun i j => raw39638step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39638step1 raw39638step0; decide +kernel
      have hl : raw39638step1Labels = raw39638step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39638step0 raw39638step0Labels permutation80 hz
    mixedMoment B raw39638step1 raw39638step1Labels = mixedMoment B raw39638step2 raw39638step2Labels := by
      have ha : raw39638step2 = (fun i j => raw39638step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39638step2 raw39638step1; decide +kernel
      have hl : raw39638step2Labels = raw39638step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39638step1 raw39638step1Labels permutation8 permutation5
    mixedMoment B raw39638step2 raw39638step2Labels = mixedMoment B raw39638step3 raw39638step3Labels := by
      have ha : raw39638step3 = -raw39638step2 := by apply Matrix.ext; change ∀ i j, raw39638step3 i j = -(raw39638step2 i j); unfold raw39638step3 raw39638step2; decide +kernel
      have hl : raw39638step3Labels = raw39638step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node414 node414Labels := by rfl

def raw39639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39639Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39639step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw39639step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw39639step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39639step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39639step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39639 raw39639Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39639 raw39639Labels = mixedMoment B raw39639step0 raw39639step0Labels := by
      have hz : ∀ j, raw39639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39639step0 = (fun i j => raw39639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39639step0 raw39639; decide +kernel
      have hl : raw39639step0Labels = raw39639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39639 raw39639Labels permutation434 hz
    mixedMoment B raw39639step0 raw39639step0Labels = mixedMoment B raw39639step1 raw39639step1Labels := by
      have hz : ∀ j, raw39639step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39639step1 = (fun i j => raw39639step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39639step1 raw39639step0; decide +kernel
      have hl : raw39639step1Labels = raw39639step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39639step0 raw39639step0Labels permutation80 hz
    mixedMoment B raw39639step1 raw39639step1Labels = mixedMoment B raw39639step2 raw39639step2Labels := by
      have ha : raw39639step2 = (fun i j => raw39639step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39639step2 raw39639step1; decide +kernel
      have hl : raw39639step2Labels = raw39639step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39639step1 raw39639step1Labels permutation12 permutation5
    mixedMoment B raw39639step2 raw39639step2Labels = mixedMoment B raw39639step3 raw39639step3Labels := by
      have ha : raw39639step3 = -raw39639step2 := by apply Matrix.ext; change ∀ i j, raw39639step3 i j = -(raw39639step2 i j); unfold raw39639step3 raw39639step2; decide +kernel
      have hl : raw39639step3Labels = raw39639step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node410 node410Labels := by rfl

def raw39640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39640Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39640step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw39640step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39640step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39640 raw39640Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39640 raw39640Labels = mixedMoment B raw39640step0 raw39640step0Labels := by
      have hz : ∀ j, raw39640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39640step0 = (fun i j => raw39640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39640step0 raw39640; decide +kernel
      have hl : raw39640step0Labels = raw39640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39640 raw39640Labels permutation346 hz
    mixedMoment B raw39640step0 raw39640step0Labels = mixedMoment B raw39640step1 raw39640step1Labels := by
      have ha : raw39640step1 = (fun i j => raw39640step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39640step1 raw39640step0; decide +kernel
      have hl : raw39640step1Labels = raw39640step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39640step0 raw39640step0Labels permutation50 permutation5
    mixedMoment B raw39640step1 raw39640step1Labels = mixedMoment B raw39640step2 raw39640step2Labels := by
      have ha : raw39640step2 = -raw39640step1 := by apply Matrix.ext; change ∀ i j, raw39640step2 i j = -(raw39640step1 i j); unfold raw39640step2 raw39640step1; decide +kernel
      have hl : raw39640step2Labels = raw39640step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node409 node409Labels := by rfl

def raw39641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39641Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39641step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw39641step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw39641step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39641step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39641step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39641 raw39641Labels = mixedMoment B node391 node391Labels := by
  calc
    mixedMoment B raw39641 raw39641Labels = mixedMoment B raw39641step0 raw39641step0Labels := by
      have hz : ∀ j, raw39641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39641step0 = (fun i j => raw39641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39641step0 raw39641; decide +kernel
      have hl : raw39641step0Labels = raw39641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39641 raw39641Labels permutation434 hz
    mixedMoment B raw39641step0 raw39641step0Labels = mixedMoment B raw39641step1 raw39641step1Labels := by
      have hz : ∀ j, raw39641step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39641step1 = (fun i j => raw39641step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39641step1 raw39641step0; decide +kernel
      have hl : raw39641step1Labels = raw39641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39641step0 raw39641step0Labels permutation80 hz
    mixedMoment B raw39641step1 raw39641step1Labels = mixedMoment B raw39641step2 raw39641step2Labels := by
      have ha : raw39641step2 = (fun i j => raw39641step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39641step2 raw39641step1; decide +kernel
      have hl : raw39641step2Labels = raw39641step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39641step1 raw39641step1Labels permutation16 permutation6
    mixedMoment B raw39641step2 raw39641step2Labels = mixedMoment B raw39641step3 raw39641step3Labels := by
      have ha : raw39641step3 = -raw39641step2 := by apply Matrix.ext; change ∀ i j, raw39641step3 i j = -(raw39641step2 i j); unfold raw39641step3 raw39641step2; decide +kernel
      have hl : raw39641step3Labels = raw39641step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node391 node391Labels := by rfl

def raw39642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39642Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39642step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39642step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39642step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![2, -3, 1]]
def raw39642step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39642step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 3, -1], ![2, -3, 1]]
def raw39642step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39642step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw39642step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39642 raw39642Labels = mixedMoment B node422 node422Labels := by
  calc
    mixedMoment B raw39642 raw39642Labels = mixedMoment B raw39642step0 raw39642step0Labels := by
      have hz : ∀ j, raw39642 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39642step0 = (fun i j => raw39642 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39642step0 raw39642; decide +kernel
      have hl : raw39642step0Labels = raw39642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39642 raw39642Labels permutation520 hz
    mixedMoment B raw39642step0 raw39642step0Labels = mixedMoment B raw39642step1 raw39642step1Labels := by
      have hz : ∀ j, raw39642step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39642step1 = (fun i j => raw39642step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39642step1 raw39642step0; decide +kernel
      have hl : raw39642step1Labels = raw39642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39642step0 raw39642step0Labels permutation104 hz
    mixedMoment B raw39642step1 raw39642step1Labels = mixedMoment B raw39642step2 raw39642step2Labels := by
      have hz : ∀ j, raw39642step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39642step2 = (fun i j => raw39642step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39642step2 raw39642step1; decide +kernel
      have hl : raw39642step2Labels = raw39642step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39642step1 raw39642step1Labels permutation20 hz
    mixedMoment B raw39642step2 raw39642step2Labels = mixedMoment B raw39642step3 raw39642step3Labels := by
      have hz : ∀ j, raw39642step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw39642step3 = (fun i j => raw39642step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw39642step3 raw39642step2; decide +kernel
      have hl : raw39642step3Labels = raw39642step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39642step2 raw39642step2Labels permutation4 hz
    mixedMoment B raw39642step3 raw39642step3Labels = mixedMoment B raw39642step4 raw39642step4Labels := by
      have ha : raw39642step4 = (fun i j => raw39642step3 (permutation1 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39642step4 raw39642step3; decide +kernel
      have hl : raw39642step4Labels = raw39642step3Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39642step3 raw39642step3Labels permutation1 permutation5
    _ = mixedMoment B node422 node422Labels := by rfl

def raw39643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39643Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39643step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39643step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39643step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![2, -2, 0]]
def raw39643step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39643step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw39643step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39643step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39643step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39643 raw39643Labels = mixedMoment B node418 node418Labels := by
  calc
    mixedMoment B raw39643 raw39643Labels = mixedMoment B raw39643step0 raw39643step0Labels := by
      have hz : ∀ j, raw39643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39643step0 = (fun i j => raw39643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39643step0 raw39643; decide +kernel
      have hl : raw39643step0Labels = raw39643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39643 raw39643Labels permutation434 hz
    mixedMoment B raw39643step0 raw39643step0Labels = mixedMoment B raw39643step1 raw39643step1Labels := by
      have hz : ∀ j, raw39643step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39643step1 = (fun i j => raw39643step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39643step1 raw39643step0; decide +kernel
      have hl : raw39643step1Labels = raw39643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39643step0 raw39643step0Labels permutation80 hz
    mixedMoment B raw39643step1 raw39643step1Labels = mixedMoment B raw39643step2 raw39643step2Labels := by
      have hz : ∀ j, raw39643step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39643step2 = (fun i j => raw39643step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39643step2 raw39643step1; decide +kernel
      have hl : raw39643step2Labels = raw39643step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39643step1 raw39643step1Labels permutation14 hz
    mixedMoment B raw39643step2 raw39643step2Labels = mixedMoment B raw39643step3 raw39643step3Labels := by
      have ha : raw39643step3 = (fun i j => raw39643step2 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39643step3 raw39643step2; decide +kernel
      have hl : raw39643step3Labels = raw39643step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39643step2 raw39643step2Labels permutation2 permutation5
    mixedMoment B raw39643step3 raw39643step3Labels = mixedMoment B raw39643step4 raw39643step4Labels := by
      have ha : raw39643step4 = -raw39643step3 := by apply Matrix.ext; change ∀ i j, raw39643step4 i j = -(raw39643step3 i j); unfold raw39643step4 raw39643step3; decide +kernel
      have hl : raw39643step4Labels = raw39643step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node418 node418Labels := by rfl

def raw39644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw39644Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw39644step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw39644step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39644step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -2, 2], ![2, -1, -1]]
def raw39644step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39644step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw39644step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39644step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39644step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39644 raw39644Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw39644 raw39644Labels = mixedMoment B raw39644step0 raw39644step0Labels := by
      have hz : ∀ j, raw39644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39644step0 = (fun i j => raw39644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39644step0 raw39644; decide +kernel
      have hl : raw39644step0Labels = raw39644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39644 raw39644Labels permutation434 hz
    mixedMoment B raw39644step0 raw39644step0Labels = mixedMoment B raw39644step1 raw39644step1Labels := by
      have hz : ∀ j, raw39644step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39644step1 = (fun i j => raw39644step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39644step1 raw39644step0; decide +kernel
      have hl : raw39644step1Labels = raw39644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39644step0 raw39644step0Labels permutation80 hz
    mixedMoment B raw39644step1 raw39644step1Labels = mixedMoment B raw39644step2 raw39644step2Labels := by
      have hz : ∀ j, raw39644step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39644step2 = (fun i j => raw39644step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39644step2 raw39644step1; decide +kernel
      have hl : raw39644step2Labels = raw39644step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39644step1 raw39644step1Labels permutation14 hz
    mixedMoment B raw39644step2 raw39644step2Labels = mixedMoment B raw39644step3 raw39644step3Labels := by
      have ha : raw39644step3 = (fun i j => raw39644step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39644step3 raw39644step2; decide +kernel
      have hl : raw39644step3Labels = raw39644step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39644step2 raw39644step2Labels permutation3 permutation5
    mixedMoment B raw39644step3 raw39644step3Labels = mixedMoment B raw39644step4 raw39644step4Labels := by
      have ha : raw39644step4 = -raw39644step3 := by apply Matrix.ext; change ∀ i j, raw39644step4 i j = -(raw39644step3 i j); unfold raw39644step4 raw39644step3; decide +kernel
      have hl : raw39644step4Labels = raw39644step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node420 node420Labels := by rfl

def raw39645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39645Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39645step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39645step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39645step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -3, 3], ![2, 0, -2]]
def raw39645step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39645step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39645step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39645 raw39645Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw39645 raw39645Labels = mixedMoment B raw39645step0 raw39645step0Labels := by
      have hz : ∀ j, raw39645 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39645step0 = (fun i j => raw39645 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39645step0 raw39645; decide +kernel
      have hl : raw39645step0Labels = raw39645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39645 raw39645Labels permutation434 hz
    mixedMoment B raw39645step0 raw39645step0Labels = mixedMoment B raw39645step1 raw39645step1Labels := by
      have hz : ∀ j, raw39645step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39645step1 = (fun i j => raw39645step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39645step1 raw39645step0; decide +kernel
      have hl : raw39645step1Labels = raw39645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39645step0 raw39645step0Labels permutation80 hz
    mixedMoment B raw39645step1 raw39645step1Labels = mixedMoment B raw39645step2 raw39645step2Labels := by
      have hz : ∀ j, raw39645step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39645step2 = (fun i j => raw39645step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39645step2 raw39645step1; decide +kernel
      have hl : raw39645step2Labels = raw39645step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39645step1 raw39645step1Labels permutation14 hz
    mixedMoment B raw39645step2 raw39645step2Labels = mixedMoment B raw39645step3 raw39645step3Labels := by
      have ha : raw39645step3 = (fun i j => raw39645step2 (permutation5 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39645step3 raw39645step2; decide +kernel
      have hl : raw39645step3Labels = raw39645step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39645step2 raw39645step2Labels permutation5 permutation4
    _ = mixedMoment B node270 node270Labels := by rfl

def raw39646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39646Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39646step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39646step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39646step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39646step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39646step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw39646step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39646step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw39646step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39646 raw39646Labels = mixedMoment B node419 node419Labels := by
  calc
    mixedMoment B raw39646 raw39646Labels = mixedMoment B raw39646step0 raw39646step0Labels := by
      have hz : ∀ j, raw39646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39646step0 = (fun i j => raw39646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39646step0 raw39646; decide +kernel
      have hl : raw39646step0Labels = raw39646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39646 raw39646Labels permutation434 hz
    mixedMoment B raw39646step0 raw39646step0Labels = mixedMoment B raw39646step1 raw39646step1Labels := by
      have hz : ∀ j, raw39646step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39646step1 = (fun i j => raw39646step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39646step1 raw39646step0; decide +kernel
      have hl : raw39646step1Labels = raw39646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39646step0 raw39646step0Labels permutation80 hz
    mixedMoment B raw39646step1 raw39646step1Labels = mixedMoment B raw39646step2 raw39646step2Labels := by
      have hz : ∀ j, raw39646step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39646step2 = (fun i j => raw39646step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39646step2 raw39646step1; decide +kernel
      have hl : raw39646step2Labels = raw39646step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39646step1 raw39646step1Labels permutation14 hz
    mixedMoment B raw39646step2 raw39646step2Labels = mixedMoment B raw39646step3 raw39646step3Labels := by
      have ha : raw39646step3 = (fun i j => raw39646step2 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39646step3 raw39646step2; decide +kernel
      have hl : raw39646step3Labels = raw39646step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39646step2 raw39646step2Labels permutation2 permutation5
    mixedMoment B raw39646step3 raw39646step3Labels = mixedMoment B raw39646step4 raw39646step4Labels := by
      have ha : raw39646step4 = -raw39646step3 := by apply Matrix.ext; change ∀ i j, raw39646step4 i j = -(raw39646step3 i j); unfold raw39646step4 raw39646step3; decide +kernel
      have hl : raw39646step4Labels = raw39646step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node419 node419Labels := by rfl

def raw39647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39647Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39647step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39647step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw39647step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39647step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39647step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39647 raw39647Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39647 raw39647Labels = mixedMoment B raw39647step0 raw39647step0Labels := by
      have hz : ∀ j, raw39647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39647step0 = (fun i j => raw39647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39647step0 raw39647; decide +kernel
      have hl : raw39647step0Labels = raw39647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39647 raw39647Labels permutation346 hz
    mixedMoment B raw39647step0 raw39647step0Labels = mixedMoment B raw39647step1 raw39647step1Labels := by
      have hz : ∀ j, raw39647step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39647step1 = (fun i j => raw39647step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39647step1 raw39647step0; decide +kernel
      have hl : raw39647step1Labels = raw39647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39647step0 raw39647step0Labels permutation56 hz
    mixedMoment B raw39647step1 raw39647step1Labels = mixedMoment B raw39647step2 raw39647step2Labels := by
      have ha : raw39647step2 = (fun i j => raw39647step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39647step2 raw39647step1; decide +kernel
      have hl : raw39647step2Labels = raw39647step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39647step1 raw39647step1Labels permutation12 permutation5
    mixedMoment B raw39647step2 raw39647step2Labels = mixedMoment B raw39647step3 raw39647step3Labels := by
      have ha : raw39647step3 = -raw39647step2 := by apply Matrix.ext; change ∀ i j, raw39647step3 i j = -(raw39647step2 i j); unfold raw39647step3 raw39647step2; decide +kernel
      have hl : raw39647step3Labels = raw39647step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node412 node412Labels := by rfl

def raw39648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39648Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39648step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39648step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39648step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39648step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39648 raw39648Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw39648 raw39648Labels = mixedMoment B raw39648step0 raw39648step0Labels := by
      have hz : ∀ j, raw39648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39648step0 = (fun i j => raw39648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39648step0 raw39648; decide +kernel
      have hl : raw39648step0Labels = raw39648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39648 raw39648Labels permutation346 hz
    mixedMoment B raw39648step0 raw39648step0Labels = mixedMoment B raw39648step1 raw39648step1Labels := by
      have hz : ∀ j, raw39648step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39648step1 = (fun i j => raw39648step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39648step1 raw39648step0; decide +kernel
      have hl : raw39648step1Labels = raw39648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39648step0 raw39648step0Labels permutation56 hz
    mixedMoment B raw39648step1 raw39648step1Labels = mixedMoment B raw39648step2 raw39648step2Labels := by
      have ha : raw39648step2 = (fun i j => raw39648step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39648step2 raw39648step1; decide +kernel
      have hl : raw39648step2Labels = raw39648step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39648step1 raw39648step1Labels permutation10 permutation5
    mixedMoment B raw39648step2 raw39648step2Labels = mixedMoment B raw39648step3 raw39648step3Labels := by
      have ha : raw39648step3 = -raw39648step2 := by apply Matrix.ext; change ∀ i j, raw39648step3 i j = -(raw39648step2 i j); unfold raw39648step3 raw39648step2; decide +kernel
      have hl : raw39648step3Labels = raw39648step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node404 node404Labels := by rfl

def raw39649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw39649Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw39649step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw39649step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39649step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39649step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39649step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39649 raw39649Labels = mixedMoment B node417 node417Labels := by
  calc
    mixedMoment B raw39649 raw39649Labels = mixedMoment B raw39649step0 raw39649step0Labels := by
      have hz : ∀ j, raw39649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39649step0 = (fun i j => raw39649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39649step0 raw39649; decide +kernel
      have hl : raw39649step0Labels = raw39649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39649 raw39649Labels permutation346 hz
    mixedMoment B raw39649step0 raw39649step0Labels = mixedMoment B raw39649step1 raw39649step1Labels := by
      have hz : ∀ j, raw39649step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39649step1 = (fun i j => raw39649step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39649step1 raw39649step0; decide +kernel
      have hl : raw39649step1Labels = raw39649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39649step0 raw39649step0Labels permutation56 hz
    mixedMoment B raw39649step1 raw39649step1Labels = mixedMoment B raw39649step2 raw39649step2Labels := by
      have ha : raw39649step2 = (fun i j => raw39649step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39649step2 raw39649step1; decide +kernel
      have hl : raw39649step2Labels = raw39649step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39649step1 raw39649step1Labels permutation8 permutation5
    mixedMoment B raw39649step2 raw39649step2Labels = mixedMoment B raw39649step3 raw39649step3Labels := by
      have ha : raw39649step3 = -raw39649step2 := by apply Matrix.ext; change ∀ i j, raw39649step3 i j = -(raw39649step2 i j); unfold raw39649step3 raw39649step2; decide +kernel
      have hl : raw39649step3Labels = raw39649step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node417 node417Labels := by rfl

def raw39650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39650Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39650step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39650step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39650step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39650step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39650step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39650 raw39650Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw39650 raw39650Labels = mixedMoment B raw39650step0 raw39650step0Labels := by
      have hz : ∀ j, raw39650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39650step0 = (fun i j => raw39650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39650step0 raw39650; decide +kernel
      have hl : raw39650step0Labels = raw39650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39650 raw39650Labels permutation346 hz
    mixedMoment B raw39650step0 raw39650step0Labels = mixedMoment B raw39650step1 raw39650step1Labels := by
      have hz : ∀ j, raw39650step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39650step1 = (fun i j => raw39650step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39650step1 raw39650step0; decide +kernel
      have hl : raw39650step1Labels = raw39650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39650step0 raw39650step0Labels permutation56 hz
    mixedMoment B raw39650step1 raw39650step1Labels = mixedMoment B raw39650step2 raw39650step2Labels := by
      have ha : raw39650step2 = (fun i j => raw39650step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39650step2 raw39650step1; decide +kernel
      have hl : raw39650step2Labels = raw39650step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39650step1 raw39650step1Labels permutation11 permutation5
    mixedMoment B raw39650step2 raw39650step2Labels = mixedMoment B raw39650step3 raw39650step3Labels := by
      have ha : raw39650step3 = -raw39650step2 := by apply Matrix.ext; change ∀ i j, raw39650step3 i j = -(raw39650step2 i j); unfold raw39650step3 raw39650step2; decide +kernel
      have hl : raw39650step3Labels = raw39650step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node405 node405Labels := by rfl

def raw39651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39651Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39651step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw39651step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39651step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39651 raw39651Labels = mixedMoment B node397 node397Labels := by
  calc
    mixedMoment B raw39651 raw39651Labels = mixedMoment B raw39651step0 raw39651step0Labels := by
      have hz : ∀ j, raw39651 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39651step0 = (fun i j => raw39651 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39651step0 raw39651; decide +kernel
      have hl : raw39651step0Labels = raw39651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39651 raw39651Labels permutation265 hz
    mixedMoment B raw39651step0 raw39651step0Labels = mixedMoment B raw39651step1 raw39651step1Labels := by
      have ha : raw39651step1 = (fun i j => raw39651step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39651step1 raw39651step0; decide +kernel
      have hl : raw39651step1Labels = raw39651step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39651step0 raw39651step0Labels permutation48 permutation5
    mixedMoment B raw39651step1 raw39651step1Labels = mixedMoment B raw39651step2 raw39651step2Labels := by
      have ha : raw39651step2 = -raw39651step1 := by apply Matrix.ext; change ∀ i j, raw39651step2 i j = -(raw39651step1 i j); unfold raw39651step2 raw39651step1; decide +kernel
      have hl : raw39651step2Labels = raw39651step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node397 node397Labels := by rfl

def raw39652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39652Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw39652step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39652step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39652 raw39652Labels = mixedMoment B node396 node396Labels := by
  calc
    mixedMoment B raw39652 raw39652Labels = mixedMoment B raw39652step0 raw39652step0Labels := by
      have ha : raw39652step0 = (fun i j => raw39652 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39652step0 raw39652; decide +kernel
      have hl : raw39652step0Labels = raw39652Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39652 raw39652Labels permutation240 permutation5
    mixedMoment B raw39652step0 raw39652step0Labels = mixedMoment B raw39652step1 raw39652step1Labels := by
      have ha : raw39652step1 = -raw39652step0 := by apply Matrix.ext; change ∀ i j, raw39652step1 i j = -(raw39652step0 i j); unfold raw39652step1 raw39652step0; decide +kernel
      have hl : raw39652step1Labels = raw39652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node396 node396Labels := by rfl

def raw39653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39653Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39653step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39653step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39653step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw39653step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39653step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw39653step3Labels : Fin 2 → Fin 1 := ![0, 0]

def raw39653step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw39653step4Labels : Fin 2 → Fin 1 := ![0, 0]

def raw39653step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw39653step5Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical39653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39653 raw39653Labels = mixedMoment B node1 node1Labels := by
  calc
    mixedMoment B raw39653 raw39653Labels = mixedMoment B raw39653step0 raw39653step0Labels := by
      have hz : ∀ j, raw39653 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39653step0 = (fun i j => raw39653 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39653step0 raw39653; decide +kernel
      have hl : raw39653step0Labels = raw39653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39653 raw39653Labels permutation520 hz
    mixedMoment B raw39653step0 raw39653step0Labels = mixedMoment B raw39653step1 raw39653step1Labels := by
      have hz : ∀ j, raw39653step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39653step1 = (fun i j => raw39653step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39653step1 raw39653step0; decide +kernel
      have hl : raw39653step1Labels = raw39653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39653step0 raw39653step0Labels permutation104 hz
    mixedMoment B raw39653step1 raw39653step1Labels = mixedMoment B raw39653step2 raw39653step2Labels := by
      have hz : ∀ j, raw39653step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39653step2 = (fun i j => raw39653step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39653step2 raw39653step1; decide +kernel
      have hl : raw39653step2Labels = raw39653step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39653step1 raw39653step1Labels permutation20 hz
    mixedMoment B raw39653step2 raw39653step2Labels = mixedMoment B raw39653step3 raw39653step3Labels := by
      have hz : ∀ i, raw39653step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39653step3 = (fun i j => raw39653step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39653step3 raw39653step2; decide +kernel
      have hl : raw39653step3Labels = (fun j => raw39653step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39653step2 raw39653step2Labels permutation6 hz
    mixedMoment B raw39653step3 raw39653step3Labels = mixedMoment B raw39653step4 raw39653step4Labels := by
      have ha : raw39653step4 = (fun i j => raw39653step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw39653step4 raw39653step3; decide +kernel
      have hl : raw39653step4Labels = raw39653step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39653step3 raw39653step3Labels permutation7 permutation0
    mixedMoment B raw39653step4 raw39653step4Labels = mixedMoment B raw39653step5 raw39653step5Labels := by
      have ha : raw39653step5 = -raw39653step4 := by apply Matrix.ext; change ∀ i j, raw39653step5 i j = -(raw39653step4 i j); unfold raw39653step5 raw39653step4; decide +kernel
      have hl : raw39653step5Labels = raw39653step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1 node1Labels := by rfl

def raw39654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39654Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39654step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39654step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39654step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw39654step2Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical39654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39654 raw39654Labels = mixedMoment B node4 node4Labels := by
  calc
    mixedMoment B raw39654 raw39654Labels = mixedMoment B raw39654step0 raw39654step0Labels := by
      have hz : ∀ j, raw39654 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39654step0 = (fun i j => raw39654 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39654step0 raw39654; decide +kernel
      have hl : raw39654step0Labels = raw39654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39654 raw39654Labels permutation434 hz
    mixedMoment B raw39654step0 raw39654step0Labels = mixedMoment B raw39654step1 raw39654step1Labels := by
      have hz : ∀ j, raw39654step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39654step1 = (fun i j => raw39654step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39654step1 raw39654step0; decide +kernel
      have hl : raw39654step1Labels = raw39654step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39654step0 raw39654step0Labels permutation80 hz
    mixedMoment B raw39654step1 raw39654step1Labels = mixedMoment B raw39654step2 raw39654step2Labels := by
      have hz : ∀ i, raw39654step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39654step2 = (fun i j => raw39654step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39654step2 raw39654step1; decide +kernel
      have hl : raw39654step2Labels = (fun j => raw39654step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39654step1 raw39654step1Labels permutation6 hz
    _ = mixedMoment B node4 node4Labels := by rfl

def raw39655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39655Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39655step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39655step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39655step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39655step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39655 raw39655Labels = mixedMoment B node469 node469Labels := by
  calc
    mixedMoment B raw39655 raw39655Labels = mixedMoment B raw39655step0 raw39655step0Labels := by
      have hz : ∀ j, raw39655 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39655step0 = (fun i j => raw39655 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39655step0 raw39655; decide +kernel
      have hl : raw39655step0Labels = raw39655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39655 raw39655Labels permutation434 hz
    mixedMoment B raw39655step0 raw39655step0Labels = mixedMoment B raw39655step1 raw39655step1Labels := by
      have hz : ∀ j, raw39655step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39655step1 = (fun i j => raw39655step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39655step1 raw39655step0; decide +kernel
      have hl : raw39655step1Labels = raw39655step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39655step0 raw39655step0Labels permutation80 hz
    mixedMoment B raw39655step1 raw39655step1Labels = mixedMoment B raw39655step2 raw39655step2Labels := by
      have ha : raw39655step2 = (fun i j => raw39655step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39655step2 raw39655step1; decide +kernel
      have hl : raw39655step2Labels = raw39655step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39655step1 raw39655step1Labels permutation8 permutation3
    _ = mixedMoment B node469 node469Labels := by rfl

def raw39656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39656Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39656step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39656step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39656step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39656 raw39656Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39656 raw39656Labels = mixedMoment B raw39656step0 raw39656step0Labels := by
      have hz : ∀ j, raw39656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39656step0 = (fun i j => raw39656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39656step0 raw39656; decide +kernel
      have hl : raw39656step0Labels = raw39656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39656 raw39656Labels permutation434 hz
    mixedMoment B raw39656step0 raw39656step0Labels = mixedMoment B raw39656step1 raw39656step1Labels := by
      have hz : ∀ j, raw39656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39656step1 = (fun i j => raw39656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39656step1 raw39656step0; decide +kernel
      have hl : raw39656step1Labels = raw39656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39656step0 raw39656step0Labels permutation80 hz
    mixedMoment B raw39656step1 raw39656step1Labels = mixedMoment B raw39656step2 raw39656step2Labels := by
      have ha : raw39656step2 = (fun i j => raw39656step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39656step2 raw39656step1; decide +kernel
      have hl : raw39656step2Labels = raw39656step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39656step1 raw39656step1Labels permutation25 permutation4
    _ = mixedMoment B node412 node412Labels := by rfl

def raw39657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39657Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39657step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39657step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39657 raw39657Labels = mixedMoment B node465 node465Labels := by
  calc
    mixedMoment B raw39657 raw39657Labels = mixedMoment B raw39657step0 raw39657step0Labels := by
      have hz : ∀ j, raw39657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39657step0 = (fun i j => raw39657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39657step0 raw39657; decide +kernel
      have hl : raw39657step0Labels = raw39657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39657 raw39657Labels permutation346 hz
    mixedMoment B raw39657step0 raw39657step0Labels = mixedMoment B raw39657step1 raw39657step1Labels := by
      have ha : raw39657step1 = (fun i j => raw39657step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39657step1 raw39657step0; decide +kernel
      have hl : raw39657step1Labels = raw39657step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39657step0 raw39657step0Labels permutation32 permutation3
    _ = mixedMoment B node465 node465Labels := by rfl

def raw39658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39658Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39658step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39658step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39658 raw39658Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw39658 raw39658Labels = mixedMoment B raw39658step0 raw39658step0Labels := by
      have hz : ∀ j, raw39658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39658step0 = (fun i j => raw39658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39658step0 raw39658; decide +kernel
      have hl : raw39658step0Labels = raw39658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39658 raw39658Labels permutation346 hz
    mixedMoment B raw39658step0 raw39658step0Labels = mixedMoment B raw39658step1 raw39658step1Labels := by
      have ha : raw39658step1 = (fun i j => raw39658step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39658step1 raw39658step0; decide +kernel
      have hl : raw39658step1Labels = raw39658step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39658step0 raw39658step0Labels permutation32 permutation3
    _ = mixedMoment B node467 node467Labels := by rfl

def raw39659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39659Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39659step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39659step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39659 raw39659Labels = mixedMoment B node468 node468Labels := by
  calc
    mixedMoment B raw39659 raw39659Labels = mixedMoment B raw39659step0 raw39659step0Labels := by
      have hz : ∀ j, raw39659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39659step0 = (fun i j => raw39659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39659step0 raw39659; decide +kernel
      have hl : raw39659step0Labels = raw39659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39659 raw39659Labels permutation346 hz
    mixedMoment B raw39659step0 raw39659step0Labels = mixedMoment B raw39659step1 raw39659step1Labels := by
      have ha : raw39659step1 = (fun i j => raw39659step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39659step1 raw39659step0; decide +kernel
      have hl : raw39659step1Labels = raw39659step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39659step0 raw39659step0Labels permutation32 permutation3
    _ = mixedMoment B node468 node468Labels := by rfl

def raw39660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39660Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39660step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39660step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39660step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39660 raw39660Labels = mixedMoment B node466 node466Labels := by
  calc
    mixedMoment B raw39660 raw39660Labels = mixedMoment B raw39660step0 raw39660step0Labels := by
      have hz : ∀ j, raw39660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39660step0 = (fun i j => raw39660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39660step0 raw39660; decide +kernel
      have hl : raw39660step0Labels = raw39660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39660 raw39660Labels permutation346 hz
    mixedMoment B raw39660step0 raw39660step0Labels = mixedMoment B raw39660step1 raw39660step1Labels := by
      have ha : raw39660step1 = (fun i j => raw39660step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39660step1 raw39660step0; decide +kernel
      have hl : raw39660step1Labels = raw39660step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39660step0 raw39660step0Labels permutation32 permutation5
    mixedMoment B raw39660step1 raw39660step1Labels = mixedMoment B raw39660step2 raw39660step2Labels := by
      have ha : raw39660step2 = -raw39660step1 := by apply Matrix.ext; change ∀ i j, raw39660step2 i j = -(raw39660step1 i j); unfold raw39660step2 raw39660step1; decide +kernel
      have hl : raw39660step2Labels = raw39660step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node466 node466Labels := by rfl

def raw39661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39661Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39661step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39661step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw39661step1Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical39661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39661 raw39661Labels = mixedMoment B node3 node3Labels := by
  calc
    mixedMoment B raw39661 raw39661Labels = mixedMoment B raw39661step0 raw39661step0Labels := by
      have hz : ∀ j, raw39661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39661step0 = (fun i j => raw39661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39661step0 raw39661; decide +kernel
      have hl : raw39661step0Labels = raw39661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39661 raw39661Labels permutation346 hz
    mixedMoment B raw39661step0 raw39661step0Labels = mixedMoment B raw39661step1 raw39661step1Labels := by
      have hz : ∀ i, raw39661step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39661step1 = (fun i j => raw39661step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39661step1 raw39661step0; decide +kernel
      have hl : raw39661step1Labels = (fun j => raw39661step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39661step0 raw39661step0Labels permutation6 hz
    _ = mixedMoment B node3 node3Labels := by rfl

def raw39662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39662Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39662step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39662step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39662 raw39662Labels = mixedMoment B node461 node461Labels := by
  calc
    mixedMoment B raw39662 raw39662Labels = mixedMoment B raw39662step0 raw39662step0Labels := by
      have ha : raw39662step0 = (fun i j => raw39662 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39662step0 raw39662; decide +kernel
      have hl : raw39662step0Labels = raw39662Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39662 raw39662Labels permutation160 permutation5
    mixedMoment B raw39662step0 raw39662step0Labels = mixedMoment B raw39662step1 raw39662step1Labels := by
      have ha : raw39662step1 = -raw39662step0 := by apply Matrix.ext; change ∀ i j, raw39662step1 i j = -(raw39662step0 i j); unfold raw39662step1 raw39662step0; decide +kernel
      have hl : raw39662step1Labels = raw39662step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node461 node461Labels := by rfl

def raw39663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39663Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39663step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39663 raw39663Labels = mixedMoment B node464 node464Labels := by
  calc
    mixedMoment B raw39663 raw39663Labels = mixedMoment B raw39663step0 raw39663step0Labels := by
      have ha : raw39663step0 = (fun i j => raw39663 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39663step0 raw39663; decide +kernel
      have hl : raw39663step0Labels = raw39663Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39663 raw39663Labels permutation152 permutation3
    _ = mixedMoment B node464 node464Labels := by rfl

def raw39664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39664Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw39664step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw39664step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39664step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39664step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39664 raw39664Labels = mixedMoment B node266 node266Labels := by
  calc
    mixedMoment B raw39664 raw39664Labels = mixedMoment B raw39664step0 raw39664step0Labels := by
      have hz : ∀ j, raw39664 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39664step0 = (fun i j => raw39664 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39664step0 raw39664; decide +kernel
      have hl : raw39664step0Labels = raw39664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39664 raw39664Labels permutation520 hz
    mixedMoment B raw39664step0 raw39664step0Labels = mixedMoment B raw39664step1 raw39664step1Labels := by
      have hz : ∀ j, raw39664step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39664step1 = (fun i j => raw39664step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39664step1 raw39664step0; decide +kernel
      have hl : raw39664step1Labels = raw39664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39664step0 raw39664step0Labels permutation104 hz
    mixedMoment B raw39664step1 raw39664step1Labels = mixedMoment B raw39664step2 raw39664step2Labels := by
      have ha : raw39664step2 = (fun i j => raw39664step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39664step2 raw39664step1; decide +kernel
      have hl : raw39664step2Labels = raw39664step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39664step1 raw39664step1Labels permutation31 permutation3
    mixedMoment B raw39664step2 raw39664step2Labels = mixedMoment B raw39664step3 raw39664step3Labels := by
      have ha : raw39664step3 = -raw39664step2 := by apply Matrix.ext; change ∀ i j, raw39664step3 i j = -(raw39664step2 i j); unfold raw39664step3 raw39664step2; decide +kernel
      have hl : raw39664step3Labels = raw39664step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node266 node266Labels := by rfl

def raw39665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39665Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39665step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39665step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39665step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39665 raw39665Labels = mixedMoment B node465 node465Labels := by
  calc
    mixedMoment B raw39665 raw39665Labels = mixedMoment B raw39665step0 raw39665step0Labels := by
      have hz : ∀ j, raw39665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39665step0 = (fun i j => raw39665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39665step0 raw39665; decide +kernel
      have hl : raw39665step0Labels = raw39665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39665 raw39665Labels permutation434 hz
    mixedMoment B raw39665step0 raw39665step0Labels = mixedMoment B raw39665step1 raw39665step1Labels := by
      have ha : raw39665step1 = (fun i j => raw39665step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39665step1 raw39665step0; decide +kernel
      have hl : raw39665step1Labels = raw39665step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39665step0 raw39665step0Labels permutation151 permutation3
    mixedMoment B raw39665step1 raw39665step1Labels = mixedMoment B raw39665step2 raw39665step2Labels := by
      have ha : raw39665step2 = -raw39665step1 := by apply Matrix.ext; change ∀ i j, raw39665step2 i j = -(raw39665step1 i j); unfold raw39665step2 raw39665step1; decide +kernel
      have hl : raw39665step2Labels = raw39665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node465 node465Labels := by rfl

def raw39666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39666Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39666step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39666step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39666 raw39666Labels = mixedMoment B node483 node483Labels := by
  calc
    mixedMoment B raw39666 raw39666Labels = mixedMoment B raw39666step0 raw39666step0Labels := by
      have hz : ∀ j, raw39666 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39666step0 = (fun i j => raw39666 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39666step0 raw39666; decide +kernel
      have hl : raw39666step0Labels = raw39666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39666 raw39666Labels permutation434 hz
    mixedMoment B raw39666step0 raw39666step0Labels = mixedMoment B raw39666step1 raw39666step1Labels := by
      have ha : raw39666step1 = (fun i j => raw39666step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39666step1 raw39666step0; decide +kernel
      have hl : raw39666step1Labels = raw39666step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39666step0 raw39666step0Labels permutation32 permutation3
    _ = mixedMoment B node483 node483Labels := by rfl

def raw39667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39667Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39667step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39667step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39667 raw39667Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39667 raw39667Labels = mixedMoment B raw39667step0 raw39667step0Labels := by
      have hz : ∀ j, raw39667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39667step0 = (fun i j => raw39667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39667step0 raw39667; decide +kernel
      have hl : raw39667step0Labels = raw39667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39667 raw39667Labels permutation434 hz
    mixedMoment B raw39667step0 raw39667step0Labels = mixedMoment B raw39667step1 raw39667step1Labels := by
      have ha : raw39667step1 = (fun i j => raw39667step0 (permutation115 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39667step1 raw39667step0; decide +kernel
      have hl : raw39667step1Labels = raw39667step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39667step0 raw39667step0Labels permutation115 permutation4
    _ = mixedMoment B node384 node384Labels := by rfl

def raw39668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39668Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39668step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39668 raw39668Labels = mixedMoment B node478 node478Labels := by
  calc
    mixedMoment B raw39668 raw39668Labels = mixedMoment B raw39668step0 raw39668step0Labels := by
      have ha : raw39668step0 = (fun i j => raw39668 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39668step0 raw39668; decide +kernel
      have hl : raw39668step0Labels = raw39668Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39668 raw39668Labels permutation152 permutation3
    _ = mixedMoment B node478 node478Labels := by rfl

def raw39669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39669Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39669step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39669 raw39669Labels = mixedMoment B node480 node480Labels := by
  calc
    mixedMoment B raw39669 raw39669Labels = mixedMoment B raw39669step0 raw39669step0Labels := by
      have ha : raw39669step0 = (fun i j => raw39669 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39669step0 raw39669; decide +kernel
      have hl : raw39669step0Labels = raw39669Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39669 raw39669Labels permutation152 permutation3
    _ = mixedMoment B node480 node480Labels := by rfl

def raw39670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39670Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39670step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39670step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39670 raw39670Labels = mixedMoment B node481 node481Labels := by
  calc
    mixedMoment B raw39670 raw39670Labels = mixedMoment B raw39670step0 raw39670step0Labels := by
      have ha : raw39670step0 = (fun i j => raw39670 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39670step0 raw39670; decide +kernel
      have hl : raw39670step0Labels = raw39670Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39670 raw39670Labels permutation682 permutation2
    mixedMoment B raw39670step0 raw39670step0Labels = mixedMoment B raw39670step1 raw39670step1Labels := by
      have ha : raw39670step1 = -raw39670step0 := by apply Matrix.ext; change ∀ i j, raw39670step1 i j = -(raw39670step0 i j); unfold raw39670step1 raw39670step0; decide +kernel
      have hl : raw39670step1Labels = raw39670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node481 node481Labels := by rfl

def raw39671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39671Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39671step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39671step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39671 raw39671Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw39671 raw39671Labels = mixedMoment B raw39671step0 raw39671step0Labels := by
      have ha : raw39671step0 = (fun i j => raw39671 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39671step0 raw39671; decide +kernel
      have hl : raw39671step0Labels = raw39671Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39671 raw39671Labels permutation176 permutation5
    mixedMoment B raw39671step0 raw39671step0Labels = mixedMoment B raw39671step1 raw39671step1Labels := by
      have ha : raw39671step1 = -raw39671step0 := by apply Matrix.ext; change ∀ i j, raw39671step1 i j = -(raw39671step0 i j); unfold raw39671step1 raw39671step0; decide +kernel
      have hl : raw39671step1Labels = raw39671step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node479 node479Labels := by rfl

def raw39672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39672Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39672step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39672 raw39672Labels = mixedMoment B node482 node482Labels := by
  calc
    mixedMoment B raw39672 raw39672Labels = mixedMoment B raw39672step0 raw39672step0Labels := by
      have ha : raw39672step0 = (fun i j => raw39672 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39672step0 raw39672; decide +kernel
      have hl : raw39672step0Labels = raw39672Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39672 raw39672Labels permutation152 permutation3
    _ = mixedMoment B node482 node482Labels := by rfl

def raw39673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39673Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39673step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39673step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39673step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39673 raw39673Labels = mixedMoment B node5505 node5505Labels := by
  calc
    mixedMoment B raw39673 raw39673Labels = mixedMoment B raw39673step0 raw39673step0Labels := by
      have hz : ∀ j, raw39673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39673step0 = (fun i j => raw39673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39673step0 raw39673; decide +kernel
      have hl : raw39673step0Labels = raw39673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39673 raw39673Labels permutation434 hz
    mixedMoment B raw39673step0 raw39673step0Labels = mixedMoment B raw39673step1 raw39673step1Labels := by
      have hz : ∀ j, raw39673step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39673step1 = (fun i j => raw39673step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39673step1 raw39673step0; decide +kernel
      have hl : raw39673step1Labels = raw39673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39673step0 raw39673step0Labels permutation80 hz
    mixedMoment B raw39673step1 raw39673step1Labels = mixedMoment B raw39673step2 raw39673step2Labels := by
      have ha : raw39673step2 = (fun i j => raw39673step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39673step2 raw39673step1; decide +kernel
      have hl : raw39673step2Labels = raw39673step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39673step1 raw39673step1Labels permutation8 permutation3
    _ = mixedMoment B node5505 node5505Labels := by rfl

def raw39674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39674Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39674step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39674step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39674 raw39674Labels = mixedMoment B node487 node487Labels := by
  calc
    mixedMoment B raw39674 raw39674Labels = mixedMoment B raw39674step0 raw39674step0Labels := by
      have hz : ∀ j, raw39674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39674step0 = (fun i j => raw39674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39674step0 raw39674; decide +kernel
      have hl : raw39674step0Labels = raw39674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39674 raw39674Labels permutation346 hz
    mixedMoment B raw39674step0 raw39674step0Labels = mixedMoment B raw39674step1 raw39674step1Labels := by
      have ha : raw39674step1 = (fun i j => raw39674step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39674step1 raw39674step0; decide +kernel
      have hl : raw39674step1Labels = raw39674step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39674step0 raw39674step0Labels permutation32 permutation3
    _ = mixedMoment B node487 node487Labels := by rfl

def raw39675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39675Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39675step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39675step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39675step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39675 raw39675Labels = mixedMoment B node490 node490Labels := by
  calc
    mixedMoment B raw39675 raw39675Labels = mixedMoment B raw39675step0 raw39675step0Labels := by
      have hz : ∀ j, raw39675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39675step0 = (fun i j => raw39675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39675step0 raw39675; decide +kernel
      have hl : raw39675step0Labels = raw39675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39675 raw39675Labels permutation346 hz
    mixedMoment B raw39675step0 raw39675step0Labels = mixedMoment B raw39675step1 raw39675step1Labels := by
      have ha : raw39675step1 = (fun i j => raw39675step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39675step1 raw39675step0; decide +kernel
      have hl : raw39675step1Labels = raw39675step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39675step0 raw39675step0Labels permutation151 permutation2
    mixedMoment B raw39675step1 raw39675step1Labels = mixedMoment B raw39675step2 raw39675step2Labels := by
      have ha : raw39675step2 = -raw39675step1 := by apply Matrix.ext; change ∀ i j, raw39675step2 i j = -(raw39675step1 i j); unfold raw39675step2 raw39675step1; decide +kernel
      have hl : raw39675step2Labels = raw39675step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node490 node490Labels := by rfl

def raw39676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39676Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39676step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39676step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39676 raw39676Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39676 raw39676Labels = mixedMoment B raw39676step0 raw39676step0Labels := by
      have hz : ∀ j, raw39676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39676step0 = (fun i j => raw39676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39676step0 raw39676; decide +kernel
      have hl : raw39676step0Labels = raw39676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39676 raw39676Labels permutation346 hz
    mixedMoment B raw39676step0 raw39676step0Labels = mixedMoment B raw39676step1 raw39676step1Labels := by
      have ha : raw39676step1 = (fun i j => raw39676step0 (permutation133 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39676step1 raw39676step0; decide +kernel
      have hl : raw39676step1Labels = raw39676step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39676step0 raw39676step0Labels permutation133 permutation7
    _ = mixedMoment B node409 node409Labels := by rfl

def raw39677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39677Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39677step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39677step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39677 raw39677Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39677 raw39677Labels = mixedMoment B raw39677step0 raw39677step0Labels := by
      have hz : ∀ j, raw39677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39677step0 = (fun i j => raw39677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39677step0 raw39677; decide +kernel
      have hl : raw39677step0Labels = raw39677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39677 raw39677Labels permutation346 hz
    mixedMoment B raw39677step0 raw39677step0Labels = mixedMoment B raw39677step1 raw39677step1Labels := by
      have ha : raw39677step1 = (fun i j => raw39677step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39677step1 raw39677step0; decide +kernel
      have hl : raw39677step1Labels = raw39677step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39677step0 raw39677step0Labels permutation146 permutation7
    _ = mixedMoment B node384 node384Labels := by rfl

def raw39678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39678Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw39678step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39678 raw39678Labels = mixedMoment B node485 node485Labels := by
  calc
    mixedMoment B raw39678 raw39678Labels = mixedMoment B raw39678step0 raw39678step0Labels := by
      have ha : raw39678step0 = (fun i j => raw39678 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39678step0 raw39678; decide +kernel
      have hl : raw39678step0Labels = raw39678Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39678 raw39678Labels permutation152 permutation3
    _ = mixedMoment B node485 node485Labels := by rfl

def raw39679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39679Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39679step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39679 raw39679Labels = mixedMoment B node486 node486Labels := by
  calc
    mixedMoment B raw39679 raw39679Labels = mixedMoment B raw39679step0 raw39679step0Labels := by
      have ha : raw39679step0 = (fun i j => raw39679 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39679step0 raw39679; decide +kernel
      have hl : raw39679step0Labels = raw39679Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39679 raw39679Labels permutation152 permutation3
    _ = mixedMoment B node486 node486Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
