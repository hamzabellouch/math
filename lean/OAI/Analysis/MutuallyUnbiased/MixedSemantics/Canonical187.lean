import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw23936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw23936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23936 raw23936Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw23936 raw23936Labels = mixedMoment B raw23936step0 raw23936step0Labels := by
      have hz : ∀ j, raw23936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23936step0 = (fun i j => raw23936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23936step0 raw23936; decide +kernel
      have hl : raw23936step0Labels = raw23936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23936 raw23936Labels permutation346 hz
    mixedMoment B raw23936step0 raw23936step0Labels = mixedMoment B raw23936step1 raw23936step1Labels := by
      have ha : raw23936step1 = (fun i j => raw23936step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23936step1 raw23936step0; decide +kernel
      have hl : raw23936step1Labels = raw23936step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23936step0 raw23936step0Labels permutation44 permutation2
    _ = mixedMoment B node1270 node1270Labels := by rfl

def raw23937 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23937 raw23937Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw23937 raw23937Labels = mixedMoment B raw23937step0 raw23937step0Labels := by
      have hz : ∀ j, raw23937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23937step0 = (fun i j => raw23937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23937step0 raw23937; decide +kernel
      have hl : raw23937step0Labels = raw23937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23937 raw23937Labels permutation346 hz
    mixedMoment B raw23937step0 raw23937step0Labels = mixedMoment B raw23937step1 raw23937step1Labels := by
      have ha : raw23937step1 = (fun i j => raw23937step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23937step1 raw23937step0; decide +kernel
      have hl : raw23937step1Labels = raw23937step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23937step0 raw23937step0Labels permutation145 permutation4
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw23938 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23938step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23938 raw23938Labels = mixedMoment B node1658 node1658Labels := by
  calc
    mixedMoment B raw23938 raw23938Labels = mixedMoment B raw23938step0 raw23938step0Labels := by
      have hz : ∀ j, raw23938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23938step0 = (fun i j => raw23938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23938step0 raw23938; decide +kernel
      have hl : raw23938step0Labels = raw23938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23938 raw23938Labels permutation346 hz
    mixedMoment B raw23938step0 raw23938step0Labels = mixedMoment B raw23938step1 raw23938step1Labels := by
      have ha : raw23938step1 = (fun i j => raw23938step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23938step1 raw23938step0; decide +kernel
      have hl : raw23938step1Labels = raw23938step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23938step0 raw23938step0Labels permutation53 permutation2
    mixedMoment B raw23938step1 raw23938step1Labels = mixedMoment B raw23938step2 raw23938step2Labels := by
      have ha : raw23938step2 = -raw23938step1 := by apply Matrix.ext; change ∀ i j, raw23938step2 i j = -(raw23938step1 i j); unfold raw23938step2 raw23938step1; decide +kernel
      have hl : raw23938step2Labels = raw23938step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1658 node1658Labels := by rfl

def raw23939 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23939step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23939 raw23939Labels = mixedMoment B node1654 node1654Labels := by
  calc
    mixedMoment B raw23939 raw23939Labels = mixedMoment B raw23939step0 raw23939step0Labels := by
      have ha : raw23939step0 = (fun i j => raw23939 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23939step0 raw23939; decide +kernel
      have hl : raw23939step0Labels = raw23939Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23939 raw23939Labels permutation246 permutation2
    mixedMoment B raw23939step0 raw23939step0Labels = mixedMoment B raw23939step1 raw23939step1Labels := by
      have ha : raw23939step1 = -raw23939step0 := by apply Matrix.ext; change ∀ i j, raw23939step1 i j = -(raw23939step0 i j); unfold raw23939step1 raw23939step0; decide +kernel
      have hl : raw23939step1Labels = raw23939step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1654 node1654Labels := by rfl

def raw23940 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23940step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23940 raw23940Labels = mixedMoment B node1656 node1656Labels := by
  calc
    mixedMoment B raw23940 raw23940Labels = mixedMoment B raw23940step0 raw23940step0Labels := by
      have hz : ∀ j, raw23940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23940step0 = (fun i j => raw23940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23940step0 raw23940; decide +kernel
      have hl : raw23940step0Labels = raw23940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23940 raw23940Labels permutation346 hz
    mixedMoment B raw23940step0 raw23940step0Labels = mixedMoment B raw23940step1 raw23940step1Labels := by
      have ha : raw23940step1 = (fun i j => raw23940step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23940step1 raw23940step0; decide +kernel
      have hl : raw23940step1Labels = raw23940step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23940step0 raw23940step0Labels permutation51 permutation2
    mixedMoment B raw23940step1 raw23940step1Labels = mixedMoment B raw23940step2 raw23940step2Labels := by
      have ha : raw23940step2 = -raw23940step1 := by apply Matrix.ext; change ∀ i j, raw23940step2 i j = -(raw23940step1 i j); unfold raw23940step2 raw23940step1; decide +kernel
      have hl : raw23940step2Labels = raw23940step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1656 node1656Labels := by rfl

def raw23941 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23941step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23941step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23941 raw23941Labels = mixedMoment B node1656 node1656Labels := by
  calc
    mixedMoment B raw23941 raw23941Labels = mixedMoment B raw23941step0 raw23941step0Labels := by
      have hz : ∀ j, raw23941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23941step0 = (fun i j => raw23941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23941step0 raw23941; decide +kernel
      have hl : raw23941step0Labels = raw23941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23941 raw23941Labels permutation346 hz
    mixedMoment B raw23941step0 raw23941step0Labels = mixedMoment B raw23941step1 raw23941step1Labels := by
      have ha : raw23941step1 = (fun i j => raw23941step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23941step1 raw23941step0; decide +kernel
      have hl : raw23941step1Labels = raw23941step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23941step0 raw23941step0Labels permutation50 permutation2
    mixedMoment B raw23941step1 raw23941step1Labels = mixedMoment B raw23941step2 raw23941step2Labels := by
      have ha : raw23941step2 = -raw23941step1 := by apply Matrix.ext; change ∀ i j, raw23941step2 i j = -(raw23941step1 i j); unfold raw23941step2 raw23941step1; decide +kernel
      have hl : raw23941step2Labels = raw23941step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1656 node1656Labels := by rfl

def raw23942 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23942step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23942step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23942 raw23942Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw23942 raw23942Labels = mixedMoment B raw23942step0 raw23942step0Labels := by
      have hz : ∀ j, raw23942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23942step0 = (fun i j => raw23942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23942step0 raw23942; decide +kernel
      have hl : raw23942step0Labels = raw23942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23942 raw23942Labels permutation346 hz
    mixedMoment B raw23942step0 raw23942step0Labels = mixedMoment B raw23942step1 raw23942step1Labels := by
      have ha : raw23942step1 = (fun i j => raw23942step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23942step1 raw23942step0; decide +kernel
      have hl : raw23942step1Labels = raw23942step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23942step0 raw23942step0Labels permutation50 permutation2
    mixedMoment B raw23942step1 raw23942step1Labels = mixedMoment B raw23942step2 raw23942step2Labels := by
      have ha : raw23942step2 = -raw23942step1 := by apply Matrix.ext; change ∀ i j, raw23942step2 i j = -(raw23942step1 i j); unfold raw23942step2 raw23942step1; decide +kernel
      have hl : raw23942step2Labels = raw23942step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw23943 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23943step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23943step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23943 raw23943Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw23943 raw23943Labels = mixedMoment B raw23943step0 raw23943step0Labels := by
      have hz : ∀ j, raw23943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23943step0 = (fun i j => raw23943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23943step0 raw23943; decide +kernel
      have hl : raw23943step0Labels = raw23943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23943 raw23943Labels permutation346 hz
    mixedMoment B raw23943step0 raw23943step0Labels = mixedMoment B raw23943step1 raw23943step1Labels := by
      have hz : ∀ j, raw23943step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23943step1 = (fun i j => raw23943step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23943step1 raw23943step0; decide +kernel
      have hl : raw23943step1Labels = raw23943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23943step0 raw23943step0Labels permutation56 hz
    mixedMoment B raw23943step1 raw23943step1Labels = mixedMoment B raw23943step2 raw23943step2Labels := by
      have ha : raw23943step2 = (fun i j => raw23943step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23943step2 raw23943step1; decide +kernel
      have hl : raw23943step2Labels = raw23943step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23943step1 raw23943step1Labels permutation8 permutation4
    mixedMoment B raw23943step2 raw23943step2Labels = mixedMoment B raw23943step3 raw23943step3Labels := by
      have ha : raw23943step3 = -raw23943step2 := by apply Matrix.ext; change ∀ i j, raw23943step3 i j = -(raw23943step2 i j); unfold raw23943step3 raw23943step2; decide +kernel
      have hl : raw23943step3Labels = raw23943step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw23944 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23944Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23944step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23944 raw23944Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw23944 raw23944Labels = mixedMoment B raw23944step0 raw23944step0Labels := by
      have hz : ∀ j, raw23944 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23944step0 = (fun i j => raw23944 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23944step0 raw23944; decide +kernel
      have hl : raw23944step0Labels = raw23944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23944 raw23944Labels permutation265 hz
    mixedMoment B raw23944step0 raw23944step0Labels = mixedMoment B raw23944step1 raw23944step1Labels := by
      have ha : raw23944step1 = (fun i j => raw23944step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23944step1 raw23944step0; decide +kernel
      have hl : raw23944step1Labels = raw23944step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23944step0 raw23944step0Labels permutation145 permutation4
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw23945 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23945step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw23945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23945 raw23945Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw23945 raw23945Labels = mixedMoment B raw23945step0 raw23945step0Labels := by
      have hz : ∀ j, raw23945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23945step0 = (fun i j => raw23945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23945step0 raw23945; decide +kernel
      have hl : raw23945step0Labels = raw23945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23945 raw23945Labels permutation346 hz
    mixedMoment B raw23945step0 raw23945step0Labels = mixedMoment B raw23945step1 raw23945step1Labels := by
      have hz : ∀ j, raw23945step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23945step1 = (fun i j => raw23945step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23945step1 raw23945step0; decide +kernel
      have hl : raw23945step1Labels = raw23945step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23945step0 raw23945step0Labels permutation56 hz
    mixedMoment B raw23945step1 raw23945step1Labels = mixedMoment B raw23945step2 raw23945step2Labels := by
      have ha : raw23945step2 = (fun i j => raw23945step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23945step2 raw23945step1; decide +kernel
      have hl : raw23945step2Labels = raw23945step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23945step1 raw23945step1Labels permutation31 permutation4
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw23946 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23946step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw23946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23946 raw23946Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw23946 raw23946Labels = mixedMoment B raw23946step0 raw23946step0Labels := by
      have hz : ∀ j, raw23946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23946step0 = (fun i j => raw23946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23946step0 raw23946; decide +kernel
      have hl : raw23946step0Labels = raw23946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23946 raw23946Labels permutation346 hz
    mixedMoment B raw23946step0 raw23946step0Labels = mixedMoment B raw23946step1 raw23946step1Labels := by
      have hz : ∀ j, raw23946step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23946step1 = (fun i j => raw23946step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23946step1 raw23946step0; decide +kernel
      have hl : raw23946step1Labels = raw23946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23946step0 raw23946step0Labels permutation56 hz
    mixedMoment B raw23946step1 raw23946step1Labels = mixedMoment B raw23946step2 raw23946step2Labels := by
      have ha : raw23946step2 = (fun i j => raw23946step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23946step2 raw23946step1; decide +kernel
      have hl : raw23946step2Labels = raw23946step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23946step1 raw23946step1Labels permutation29 permutation4
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw23947 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23947step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23947step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw23947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23947 raw23947Labels = mixedMoment B node3308 node3308Labels := by
  calc
    mixedMoment B raw23947 raw23947Labels = mixedMoment B raw23947step0 raw23947step0Labels := by
      have hz : ∀ j, raw23947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23947step0 = (fun i j => raw23947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23947step0 raw23947; decide +kernel
      have hl : raw23947step0Labels = raw23947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23947 raw23947Labels permutation346 hz
    mixedMoment B raw23947step0 raw23947step0Labels = mixedMoment B raw23947step1 raw23947step1Labels := by
      have hz : ∀ j, raw23947step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23947step1 = (fun i j => raw23947step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23947step1 raw23947step0; decide +kernel
      have hl : raw23947step1Labels = raw23947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23947step0 raw23947step0Labels permutation56 hz
    mixedMoment B raw23947step1 raw23947step1Labels = mixedMoment B raw23947step2 raw23947step2Labels := by
      have ha : raw23947step2 = (fun i j => raw23947step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23947step2 raw23947step1; decide +kernel
      have hl : raw23947step2Labels = raw23947step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23947step1 raw23947step1Labels permutation8 permutation4
    mixedMoment B raw23947step2 raw23947step2Labels = mixedMoment B raw23947step3 raw23947step3Labels := by
      have ha : raw23947step3 = -raw23947step2 := by apply Matrix.ext; change ∀ i j, raw23947step3 i j = -(raw23947step2 i j); unfold raw23947step3 raw23947step2; decide +kernel
      have hl : raw23947step3Labels = raw23947step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3308 node3308Labels := by rfl

def raw23948 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw23948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw23948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23948 raw23948Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw23948 raw23948Labels = mixedMoment B raw23948step0 raw23948step0Labels := by
      have hz : ∀ j, raw23948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23948step0 = (fun i j => raw23948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23948step0 raw23948; decide +kernel
      have hl : raw23948step0Labels = raw23948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23948 raw23948Labels permutation346 hz
    mixedMoment B raw23948step0 raw23948step0Labels = mixedMoment B raw23948step1 raw23948step1Labels := by
      have ha : raw23948step1 = (fun i j => raw23948step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23948step1 raw23948step0; decide +kernel
      have hl : raw23948step1Labels = raw23948step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23948step0 raw23948step0Labels permutation34 permutation4
    mixedMoment B raw23948step1 raw23948step1Labels = mixedMoment B raw23948step2 raw23948step2Labels := by
      have ha : raw23948step2 = -raw23948step1 := by apply Matrix.ext; change ∀ i j, raw23948step2 i j = -(raw23948step1 i j); unfold raw23948step2 raw23948step1; decide +kernel
      have hl : raw23948step2Labels = raw23948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1602 node1602Labels := by rfl

def raw23949 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23949 raw23949Labels = mixedMoment B node2466 node2466Labels := by
  calc
    mixedMoment B raw23949 raw23949Labels = mixedMoment B raw23949step0 raw23949step0Labels := by
      have hz : ∀ j, raw23949 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23949step0 = (fun i j => raw23949 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23949step0 raw23949; decide +kernel
      have hl : raw23949step0Labels = raw23949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23949 raw23949Labels permutation346 hz
    mixedMoment B raw23949step0 raw23949step0Labels = mixedMoment B raw23949step1 raw23949step1Labels := by
      have ha : raw23949step1 = (fun i j => raw23949step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23949step1 raw23949step0; decide +kernel
      have hl : raw23949step1Labels = raw23949step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23949step0 raw23949step0Labels permutation145 permutation4
    _ = mixedMoment B node2466 node2466Labels := by rfl

def raw23950 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw23950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw23950step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23950 raw23950Labels = mixedMoment B node2457 node2457Labels := by
  calc
    mixedMoment B raw23950 raw23950Labels = mixedMoment B raw23950step0 raw23950step0Labels := by
      have ha : raw23950step0 = (fun i j => raw23950 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23950step0 raw23950; decide +kernel
      have hl : raw23950step0Labels = raw23950Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23950 raw23950Labels permutation662 permutation4
    _ = mixedMoment B node2457 node2457Labels := by rfl

def raw23951 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw23951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23951step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23951 raw23951Labels = mixedMoment B node2502 node2502Labels := by
  calc
    mixedMoment B raw23951 raw23951Labels = mixedMoment B raw23951step0 raw23951step0Labels := by
      have hz : ∀ j, raw23951 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23951step0 = (fun i j => raw23951 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23951step0 raw23951; decide +kernel
      have hl : raw23951step0Labels = raw23951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23951 raw23951Labels permutation346 hz
    mixedMoment B raw23951step0 raw23951step0Labels = mixedMoment B raw23951step1 raw23951step1Labels := by
      have ha : raw23951step1 = (fun i j => raw23951step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23951step1 raw23951step0; decide +kernel
      have hl : raw23951step1Labels = raw23951step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23951step0 raw23951step0Labels permutation145 permutation4
    _ = mixedMoment B node2502 node2502Labels := by rfl

def raw23952 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23952 raw23952Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw23952 raw23952Labels = mixedMoment B raw23952step0 raw23952step0Labels := by
      have hz : ∀ j, raw23952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23952step0 = (fun i j => raw23952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23952step0 raw23952; decide +kernel
      have hl : raw23952step0Labels = raw23952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23952 raw23952Labels permutation346 hz
    mixedMoment B raw23952step0 raw23952step0Labels = mixedMoment B raw23952step1 raw23952step1Labels := by
      have ha : raw23952step1 = (fun i j => raw23952step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23952step1 raw23952step0; decide +kernel
      have hl : raw23952step1Labels = raw23952step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23952step0 raw23952step0Labels permutation34 permutation4
    mixedMoment B raw23952step1 raw23952step1Labels = mixedMoment B raw23952step2 raw23952step2Labels := by
      have ha : raw23952step2 = -raw23952step1 := by apply Matrix.ext; change ∀ i j, raw23952step2 i j = -(raw23952step1 i j); unfold raw23952step2 raw23952step1; decide +kernel
      have hl : raw23952step2Labels = raw23952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw23953 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23953 raw23953Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw23953 raw23953Labels = mixedMoment B raw23953step0 raw23953step0Labels := by
      have ha : raw23953step0 = (fun i j => raw23953 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23953step0 raw23953; decide +kernel
      have hl : raw23953step0Labels = raw23953Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23953 raw23953Labels permutation160 permutation4
    mixedMoment B raw23953step0 raw23953step0Labels = mixedMoment B raw23953step1 raw23953step1Labels := by
      have ha : raw23953step1 = -raw23953step0 := by apply Matrix.ext; change ∀ i j, raw23953step1 i j = -(raw23953step0 i j); unfold raw23953step1 raw23953step0; decide +kernel
      have hl : raw23953step1Labels = raw23953step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3288 node3288Labels := by rfl

def raw23954 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw23954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw23954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23954 raw23954Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw23954 raw23954Labels = mixedMoment B raw23954step0 raw23954step0Labels := by
      have hz : ∀ j, raw23954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23954step0 = (fun i j => raw23954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23954step0 raw23954; decide +kernel
      have hl : raw23954step0Labels = raw23954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23954 raw23954Labels permutation346 hz
    mixedMoment B raw23954step0 raw23954step0Labels = mixedMoment B raw23954step1 raw23954step1Labels := by
      have ha : raw23954step1 = (fun i j => raw23954step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23954step1 raw23954step0; decide +kernel
      have hl : raw23954step1Labels = raw23954step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23954step0 raw23954step0Labels permutation32 permutation4
    mixedMoment B raw23954step1 raw23954step1Labels = mixedMoment B raw23954step2 raw23954step2Labels := by
      have ha : raw23954step2 = -raw23954step1 := by apply Matrix.ext; change ∀ i j, raw23954step2 i j = -(raw23954step1 i j); unfold raw23954step2 raw23954step1; decide +kernel
      have hl : raw23954step2Labels = raw23954step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw23955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23955Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23955 raw23955Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw23955 raw23955Labels = mixedMoment B raw23955step0 raw23955step0Labels := by
      have hz : ∀ j, raw23955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23955step0 = (fun i j => raw23955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23955step0 raw23955; decide +kernel
      have hl : raw23955step0Labels = raw23955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23955 raw23955Labels permutation346 hz
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw23956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23956Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23956step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23956 raw23956Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw23956 raw23956Labels = mixedMoment B raw23956step0 raw23956step0Labels := by
      have hz : ∀ j, raw23956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23956step0 = (fun i j => raw23956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23956step0 raw23956; decide +kernel
      have hl : raw23956step0Labels = raw23956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23956 raw23956Labels permutation346 hz
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw23957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23957 raw23957Labels = mixedMoment B node1127 node1127Labels := by
  calc
    _ = mixedMoment B node1127 node1127Labels := by rfl

def raw23958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23958 raw23958Labels = mixedMoment B node1141 node1141Labels := by
  calc
    mixedMoment B raw23958 raw23958Labels = mixedMoment B raw23958step0 raw23958step0Labels := by
      have hz : ∀ j, raw23958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23958step0 = (fun i j => raw23958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23958step0 raw23958; decide +kernel
      have hl : raw23958step0Labels = raw23958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23958 raw23958Labels permutation346 hz
    mixedMoment B raw23958step0 raw23958step0Labels = mixedMoment B raw23958step1 raw23958step1Labels := by
      have ha : raw23958step1 = (fun i j => raw23958step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23958step1 raw23958step0; decide +kernel
      have hl : raw23958step1Labels = raw23958step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23958step0 raw23958step0Labels permutation34 permutation2
    _ = mixedMoment B node1141 node1141Labels := by rfl

def raw23959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23959 raw23959Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw23959 raw23959Labels = mixedMoment B raw23959step0 raw23959step0Labels := by
      have hz : ∀ j, raw23959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23959step0 = (fun i j => raw23959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23959step0 raw23959; decide +kernel
      have hl : raw23959step0Labels = raw23959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23959 raw23959Labels permutation346 hz
    mixedMoment B raw23959step0 raw23959step0Labels = mixedMoment B raw23959step1 raw23959step1Labels := by
      have ha : raw23959step1 = (fun i j => raw23959step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23959step1 raw23959step0; decide +kernel
      have hl : raw23959step1Labels = raw23959step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23959step0 raw23959step0Labels permutation33 permutation2
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw23960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23960 raw23960Labels = mixedMoment B node640 node640Labels := by
  calc
    mixedMoment B raw23960 raw23960Labels = mixedMoment B raw23960step0 raw23960step0Labels := by
      have hz : ∀ j, raw23960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23960step0 = (fun i j => raw23960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23960step0 raw23960; decide +kernel
      have hl : raw23960step0Labels = raw23960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23960 raw23960Labels permutation346 hz
    mixedMoment B raw23960step0 raw23960step0Labels = mixedMoment B raw23960step1 raw23960step1Labels := by
      have ha : raw23960step1 = (fun i j => raw23960step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23960step1 raw23960step0; decide +kernel
      have hl : raw23960step1Labels = raw23960step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23960step0 raw23960step0Labels permutation44 permutation2
    _ = mixedMoment B node640 node640Labels := by rfl

def raw23961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw23961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23961 raw23961Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw23961 raw23961Labels = mixedMoment B raw23961step0 raw23961step0Labels := by
      have hz : ∀ j, raw23961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23961step0 = (fun i j => raw23961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23961step0 raw23961; decide +kernel
      have hl : raw23961step0Labels = raw23961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23961 raw23961Labels permutation346 hz
    mixedMoment B raw23961step0 raw23961step0Labels = mixedMoment B raw23961step1 raw23961step1Labels := by
      have ha : raw23961step1 = (fun i j => raw23961step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23961step1 raw23961step0; decide +kernel
      have hl : raw23961step1Labels = raw23961step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23961step0 raw23961step0Labels permutation34 permutation2
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw23962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23962 raw23962Labels = mixedMoment B node1158 node1158Labels := by
  calc
    mixedMoment B raw23962 raw23962Labels = mixedMoment B raw23962step0 raw23962step0Labels := by
      have ha : raw23962step0 = (fun i j => raw23962 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23962step0 raw23962; decide +kernel
      have hl : raw23962step0Labels = raw23962Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23962 raw23962Labels permutation188 permutation2
    _ = mixedMoment B node1158 node1158Labels := by rfl

def raw23963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw23963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw23963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23963 raw23963Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw23963 raw23963Labels = mixedMoment B raw23963step0 raw23963step0Labels := by
      have hz : ∀ j, raw23963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23963step0 = (fun i j => raw23963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23963step0 raw23963; decide +kernel
      have hl : raw23963step0Labels = raw23963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23963 raw23963Labels permutation346 hz
    mixedMoment B raw23963step0 raw23963step0Labels = mixedMoment B raw23963step1 raw23963step1Labels := by
      have ha : raw23963step1 = (fun i j => raw23963step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23963step1 raw23963step0; decide +kernel
      have hl : raw23963step1Labels = raw23963step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23963step0 raw23963step0Labels permutation40 permutation2
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw23964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw23964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw23964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23964 raw23964Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw23964 raw23964Labels = mixedMoment B raw23964step0 raw23964step0Labels := by
      have hz : ∀ j, raw23964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23964step0 = (fun i j => raw23964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23964step0 raw23964; decide +kernel
      have hl : raw23964step0Labels = raw23964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23964 raw23964Labels permutation346 hz
    mixedMoment B raw23964step0 raw23964step0Labels = mixedMoment B raw23964step1 raw23964step1Labels := by
      have ha : raw23964step1 = (fun i j => raw23964step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23964step1 raw23964step0; decide +kernel
      have hl : raw23964step1Labels = raw23964step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23964step0 raw23964step0Labels permutation44 permutation2
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw23965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw23965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw23965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw23965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23965 raw23965Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw23965 raw23965Labels = mixedMoment B raw23965step0 raw23965step0Labels := by
      have hz : ∀ j, raw23965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23965step0 = (fun i j => raw23965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23965step0 raw23965; decide +kernel
      have hl : raw23965step0Labels = raw23965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23965 raw23965Labels permutation346 hz
    mixedMoment B raw23965step0 raw23965step0Labels = mixedMoment B raw23965step1 raw23965step1Labels := by
      have ha : raw23965step1 = (fun i j => raw23965step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23965step1 raw23965step0; decide +kernel
      have hl : raw23965step1Labels = raw23965step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23965step0 raw23965step0Labels permutation44 permutation2
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw23966 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23966 raw23966Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw23966 raw23966Labels = mixedMoment B raw23966step0 raw23966step0Labels := by
      have hz : ∀ j, raw23966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23966step0 = (fun i j => raw23966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23966step0 raw23966; decide +kernel
      have hl : raw23966step0Labels = raw23966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23966 raw23966Labels permutation346 hz
    mixedMoment B raw23966step0 raw23966step0Labels = mixedMoment B raw23966step1 raw23966step1Labels := by
      have ha : raw23966step1 = (fun i j => raw23966step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23966step1 raw23966step0; decide +kernel
      have hl : raw23966step1Labels = raw23966step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23966step0 raw23966step0Labels permutation33 permutation4
    mixedMoment B raw23966step1 raw23966step1Labels = mixedMoment B raw23966step2 raw23966step2Labels := by
      have ha : raw23966step2 = -raw23966step1 := by apply Matrix.ext; change ∀ i j, raw23966step2 i j = -(raw23966step1 i j); unfold raw23966step2 raw23966step1; decide +kernel
      have hl : raw23966step2Labels = raw23966step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw23967 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23967 raw23967Labels = mixedMoment B node1649 node1649Labels := by
  calc
    mixedMoment B raw23967 raw23967Labels = mixedMoment B raw23967step0 raw23967step0Labels := by
      have hz : ∀ j, raw23967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23967step0 = (fun i j => raw23967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23967step0 raw23967; decide +kernel
      have hl : raw23967step0Labels = raw23967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23967 raw23967Labels permutation346 hz
    mixedMoment B raw23967step0 raw23967step0Labels = mixedMoment B raw23967step1 raw23967step1Labels := by
      have ha : raw23967step1 = (fun i j => raw23967step0 (permutation47 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23967step1 raw23967step0; decide +kernel
      have hl : raw23967step1Labels = raw23967step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23967step0 raw23967step0Labels permutation47 permutation2
    mixedMoment B raw23967step1 raw23967step1Labels = mixedMoment B raw23967step2 raw23967step2Labels := by
      have ha : raw23967step2 = -raw23967step1 := by apply Matrix.ext; change ∀ i j, raw23967step2 i j = -(raw23967step1 i j); unfold raw23967step2 raw23967step1; decide +kernel
      have hl : raw23967step2Labels = raw23967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1649 node1649Labels := by rfl

def raw23968 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23968 raw23968Labels = mixedMoment B node1642 node1642Labels := by
  calc
    mixedMoment B raw23968 raw23968Labels = mixedMoment B raw23968step0 raw23968step0Labels := by
      have ha : raw23968step0 = (fun i j => raw23968 (permutation224 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23968step0 raw23968; decide +kernel
      have hl : raw23968step0Labels = raw23968Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23968 raw23968Labels permutation224 permutation2
    mixedMoment B raw23968step0 raw23968step0Labels = mixedMoment B raw23968step1 raw23968step1Labels := by
      have ha : raw23968step1 = -raw23968step0 := by apply Matrix.ext; change ∀ i j, raw23968step1 i j = -(raw23968step0 i j); unfold raw23968step1 raw23968step0; decide +kernel
      have hl : raw23968step1Labels = raw23968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1642 node1642Labels := by rfl

def raw23969 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23969 raw23969Labels = mixedMoment B node1646 node1646Labels := by
  calc
    mixedMoment B raw23969 raw23969Labels = mixedMoment B raw23969step0 raw23969step0Labels := by
      have hz : ∀ j, raw23969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23969step0 = (fun i j => raw23969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23969step0 raw23969; decide +kernel
      have hl : raw23969step0Labels = raw23969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23969 raw23969Labels permutation346 hz
    mixedMoment B raw23969step0 raw23969step0Labels = mixedMoment B raw23969step1 raw23969step1Labels := by
      have ha : raw23969step1 = (fun i j => raw23969step0 (permutation45 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23969step1 raw23969step0; decide +kernel
      have hl : raw23969step1Labels = raw23969step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23969step0 raw23969step0Labels permutation45 permutation2
    mixedMoment B raw23969step1 raw23969step1Labels = mixedMoment B raw23969step2 raw23969step2Labels := by
      have ha : raw23969step2 = -raw23969step1 := by apply Matrix.ext; change ∀ i j, raw23969step2 i j = -(raw23969step1 i j); unfold raw23969step2 raw23969step1; decide +kernel
      have hl : raw23969step2Labels = raw23969step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1646 node1646Labels := by rfl

def raw23970 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23970 raw23970Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw23970 raw23970Labels = mixedMoment B raw23970step0 raw23970step0Labels := by
      have hz : ∀ j, raw23970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23970step0 = (fun i j => raw23970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23970step0 raw23970; decide +kernel
      have hl : raw23970step0Labels = raw23970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23970 raw23970Labels permutation346 hz
    mixedMoment B raw23970step0 raw23970step0Labels = mixedMoment B raw23970step1 raw23970step1Labels := by
      have ha : raw23970step1 = (fun i j => raw23970step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23970step1 raw23970step0; decide +kernel
      have hl : raw23970step1Labels = raw23970step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23970step0 raw23970step0Labels permutation44 permutation2
    mixedMoment B raw23970step1 raw23970step1Labels = mixedMoment B raw23970step2 raw23970step2Labels := by
      have ha : raw23970step2 = -raw23970step1 := by apply Matrix.ext; change ∀ i j, raw23970step2 i j = -(raw23970step1 i j); unfold raw23970step2 raw23970step1; decide +kernel
      have hl : raw23970step2Labels = raw23970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw23971 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23971 raw23971Labels = mixedMoment B node1645 node1645Labels := by
  calc
    mixedMoment B raw23971 raw23971Labels = mixedMoment B raw23971step0 raw23971step0Labels := by
      have hz : ∀ j, raw23971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23971step0 = (fun i j => raw23971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23971step0 raw23971; decide +kernel
      have hl : raw23971step0Labels = raw23971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23971 raw23971Labels permutation346 hz
    mixedMoment B raw23971step0 raw23971step0Labels = mixedMoment B raw23971step1 raw23971step1Labels := by
      have ha : raw23971step1 = (fun i j => raw23971step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23971step1 raw23971step0; decide +kernel
      have hl : raw23971step1Labels = raw23971step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23971step0 raw23971step0Labels permutation44 permutation2
    mixedMoment B raw23971step1 raw23971step1Labels = mixedMoment B raw23971step2 raw23971step2Labels := by
      have ha : raw23971step2 = -raw23971step1 := by apply Matrix.ext; change ∀ i j, raw23971step2 i j = -(raw23971step1 i j); unfold raw23971step2 raw23971step1; decide +kernel
      have hl : raw23971step2Labels = raw23971step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1645 node1645Labels := by rfl

def raw23972 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23972 raw23972Labels = mixedMoment B node1623 node1623Labels := by
  calc
    mixedMoment B raw23972 raw23972Labels = mixedMoment B raw23972step0 raw23972step0Labels := by
      have hz : ∀ j, raw23972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23972step0 = (fun i j => raw23972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23972step0 raw23972; decide +kernel
      have hl : raw23972step0Labels = raw23972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23972 raw23972Labels permutation346 hz
    mixedMoment B raw23972step0 raw23972step0Labels = mixedMoment B raw23972step1 raw23972step1Labels := by
      have ha : raw23972step1 = (fun i j => raw23972step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23972step1 raw23972step0; decide +kernel
      have hl : raw23972step1Labels = raw23972step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23972step0 raw23972step0Labels permutation33 permutation4
    mixedMoment B raw23972step1 raw23972step1Labels = mixedMoment B raw23972step2 raw23972step2Labels := by
      have ha : raw23972step2 = -raw23972step1 := by apply Matrix.ext; change ∀ i j, raw23972step2 i j = -(raw23972step1 i j); unfold raw23972step2 raw23972step1; decide +kernel
      have hl : raw23972step2Labels = raw23972step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1623 node1623Labels := by rfl

def raw23973 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-1, -1, 2]]
def raw23973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-1, -1, 2]]
def raw23973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw23973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw23973step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23973 raw23973Labels = mixedMoment B node1603 node1603Labels := by
  calc
    mixedMoment B raw23973 raw23973Labels = mixedMoment B raw23973step0 raw23973step0Labels := by
      have hz : ∀ j, raw23973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23973step0 = (fun i j => raw23973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23973step0 raw23973; decide +kernel
      have hl : raw23973step0Labels = raw23973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23973 raw23973Labels permutation346 hz
    mixedMoment B raw23973step0 raw23973step0Labels = mixedMoment B raw23973step1 raw23973step1Labels := by
      have ha : raw23973step1 = (fun i j => raw23973step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23973step1 raw23973step0; decide +kernel
      have hl : raw23973step1Labels = raw23973step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23973step0 raw23973step0Labels permutation33 permutation4
    mixedMoment B raw23973step1 raw23973step1Labels = mixedMoment B raw23973step2 raw23973step2Labels := by
      have ha : raw23973step2 = -raw23973step1 := by apply Matrix.ext; change ∀ i j, raw23973step2 i j = -(raw23973step1 i j); unfold raw23973step2 raw23973step1; decide +kernel
      have hl : raw23973step2Labels = raw23973step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1603 node1603Labels := by rfl

def raw23974 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23974 raw23974Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw23974 raw23974Labels = mixedMoment B raw23974step0 raw23974step0Labels := by
      have hz : ∀ j, raw23974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23974step0 = (fun i j => raw23974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23974step0 raw23974; decide +kernel
      have hl : raw23974step0Labels = raw23974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23974 raw23974Labels permutation346 hz
    mixedMoment B raw23974step0 raw23974step0Labels = mixedMoment B raw23974step1 raw23974step1Labels := by
      have ha : raw23974step1 = (fun i j => raw23974step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23974step1 raw23974step0; decide +kernel
      have hl : raw23974step1Labels = raw23974step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23974step0 raw23974step0Labels permutation32 permutation4
    mixedMoment B raw23974step1 raw23974step1Labels = mixedMoment B raw23974step2 raw23974step2Labels := by
      have ha : raw23974step2 = -raw23974step1 := by apply Matrix.ext; change ∀ i j, raw23974step2 i j = -(raw23974step1 i j); unfold raw23974step2 raw23974step1; decide +kernel
      have hl : raw23974step2Labels = raw23974step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1605 node1605Labels := by rfl

def raw23975 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23975 raw23975Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw23975 raw23975Labels = mixedMoment B raw23975step0 raw23975step0Labels := by
      have hz : ∀ j, raw23975 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23975step0 = (fun i j => raw23975 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23975step0 raw23975; decide +kernel
      have hl : raw23975step0Labels = raw23975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23975 raw23975Labels permutation265 hz
    mixedMoment B raw23975step0 raw23975step0Labels = mixedMoment B raw23975step1 raw23975step1Labels := by
      have ha : raw23975step1 = (fun i j => raw23975step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23975step1 raw23975step0; decide +kernel
      have hl : raw23975step1Labels = raw23975step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23975step0 raw23975step0Labels permutation33 permutation4
    mixedMoment B raw23975step1 raw23975step1Labels = mixedMoment B raw23975step2 raw23975step2Labels := by
      have ha : raw23975step2 = -raw23975step1 := by apply Matrix.ext; change ∀ i j, raw23975step2 i j = -(raw23975step1 i j); unfold raw23975step2 raw23975step1; decide +kernel
      have hl : raw23975step2Labels = raw23975step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw23976 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23976step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23976 raw23976Labels = mixedMoment B node3306 node3306Labels := by
  calc
    mixedMoment B raw23976 raw23976Labels = mixedMoment B raw23976step0 raw23976step0Labels := by
      have hz : ∀ j, raw23976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23976step0 = (fun i j => raw23976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23976step0 raw23976; decide +kernel
      have hl : raw23976step0Labels = raw23976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23976 raw23976Labels permutation346 hz
    mixedMoment B raw23976step0 raw23976step0Labels = mixedMoment B raw23976step1 raw23976step1Labels := by
      have hz : ∀ j, raw23976step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23976step1 = (fun i j => raw23976step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23976step1 raw23976step0; decide +kernel
      have hl : raw23976step1Labels = raw23976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23976step0 raw23976step0Labels permutation56 hz
    mixedMoment B raw23976step1 raw23976step1Labels = mixedMoment B raw23976step2 raw23976step2Labels := by
      have ha : raw23976step2 = (fun i j => raw23976step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23976step2 raw23976step1; decide +kernel
      have hl : raw23976step2Labels = raw23976step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23976step1 raw23976step1Labels permutation11 permutation2
    mixedMoment B raw23976step2 raw23976step2Labels = mixedMoment B raw23976step3 raw23976step3Labels := by
      have ha : raw23976step3 = -raw23976step2 := by apply Matrix.ext; change ∀ i j, raw23976step3 i j = -(raw23976step2 i j); unfold raw23976step3 raw23976step2; decide +kernel
      have hl : raw23976step3Labels = raw23976step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3306 node3306Labels := by rfl

def raw23977 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23977step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23977step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23977 raw23977Labels = mixedMoment B node3309 node3309Labels := by
  calc
    mixedMoment B raw23977 raw23977Labels = mixedMoment B raw23977step0 raw23977step0Labels := by
      have hz : ∀ j, raw23977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23977step0 = (fun i j => raw23977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23977step0 raw23977; decide +kernel
      have hl : raw23977step0Labels = raw23977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23977 raw23977Labels permutation346 hz
    mixedMoment B raw23977step0 raw23977step0Labels = mixedMoment B raw23977step1 raw23977step1Labels := by
      have hz : ∀ j, raw23977step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23977step1 = (fun i j => raw23977step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23977step1 raw23977step0; decide +kernel
      have hl : raw23977step1Labels = raw23977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23977step0 raw23977step0Labels permutation56 hz
    mixedMoment B raw23977step1 raw23977step1Labels = mixedMoment B raw23977step2 raw23977step2Labels := by
      have ha : raw23977step2 = (fun i j => raw23977step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23977step2 raw23977step1; decide +kernel
      have hl : raw23977step2Labels = raw23977step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23977step1 raw23977step1Labels permutation10 permutation2
    mixedMoment B raw23977step2 raw23977step2Labels = mixedMoment B raw23977step3 raw23977step3Labels := by
      have ha : raw23977step3 = -raw23977step2 := by apply Matrix.ext; change ∀ i j, raw23977step3 i j = -(raw23977step2 i j); unfold raw23977step3 raw23977step2; decide +kernel
      have hl : raw23977step3Labels = raw23977step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3309 node3309Labels := by rfl

def raw23978 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23978 raw23978Labels = mixedMoment B node3246 node3246Labels := by
  calc
    mixedMoment B raw23978 raw23978Labels = mixedMoment B raw23978step0 raw23978step0Labels := by
      have hz : ∀ j, raw23978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23978step0 = (fun i j => raw23978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23978step0 raw23978; decide +kernel
      have hl : raw23978step0Labels = raw23978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23978 raw23978Labels permutation346 hz
    mixedMoment B raw23978step0 raw23978step0Labels = mixedMoment B raw23978step1 raw23978step1Labels := by
      have ha : raw23978step1 = (fun i j => raw23978step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23978step1 raw23978step0; decide +kernel
      have hl : raw23978step1Labels = raw23978step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23978step0 raw23978step0Labels permutation33 permutation4
    mixedMoment B raw23978step1 raw23978step1Labels = mixedMoment B raw23978step2 raw23978step2Labels := by
      have ha : raw23978step2 = -raw23978step1 := by apply Matrix.ext; change ∀ i j, raw23978step2 i j = -(raw23978step1 i j); unfold raw23978step2 raw23978step1; decide +kernel
      have hl : raw23978step2Labels = raw23978step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3246 node3246Labels := by rfl

def raw23979 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23979 raw23979Labels = mixedMoment B node3282 node3282Labels := by
  calc
    mixedMoment B raw23979 raw23979Labels = mixedMoment B raw23979step0 raw23979step0Labels := by
      have ha : raw23979step0 = (fun i j => raw23979 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23979step0 raw23979; decide +kernel
      have hl : raw23979step0Labels = raw23979Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23979 raw23979Labels permutation153 permutation4
    mixedMoment B raw23979step0 raw23979step0Labels = mixedMoment B raw23979step1 raw23979step1Labels := by
      have ha : raw23979step1 = -raw23979step0 := by apply Matrix.ext; change ∀ i j, raw23979step1 i j = -(raw23979step0 i j); unfold raw23979step1 raw23979step0; decide +kernel
      have hl : raw23979step1Labels = raw23979step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3282 node3282Labels := by rfl

def raw23980 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23980 raw23980Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw23980 raw23980Labels = mixedMoment B raw23980step0 raw23980step0Labels := by
      have hz : ∀ j, raw23980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23980step0 = (fun i j => raw23980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23980step0 raw23980; decide +kernel
      have hl : raw23980step0Labels = raw23980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23980 raw23980Labels permutation346 hz
    mixedMoment B raw23980step0 raw23980step0Labels = mixedMoment B raw23980step1 raw23980step1Labels := by
      have ha : raw23980step1 = (fun i j => raw23980step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23980step1 raw23980step0; decide +kernel
      have hl : raw23980step1Labels = raw23980step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23980step0 raw23980step0Labels permutation32 permutation4
    mixedMoment B raw23980step1 raw23980step1Labels = mixedMoment B raw23980step2 raw23980step2Labels := by
      have ha : raw23980step2 = -raw23980step1 := by apply Matrix.ext; change ∀ i j, raw23980step2 i j = -(raw23980step1 i j); unfold raw23980step2 raw23980step1; decide +kernel
      have hl : raw23980step2Labels = raw23980step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw23981 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw23981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw23981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23981 raw23981Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw23981 raw23981Labels = mixedMoment B raw23981step0 raw23981step0Labels := by
      have hz : ∀ j, raw23981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23981step0 = (fun i j => raw23981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23981step0 raw23981; decide +kernel
      have hl : raw23981step0Labels = raw23981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23981 raw23981Labels permutation346 hz
    mixedMoment B raw23981step0 raw23981step0Labels = mixedMoment B raw23981step1 raw23981step1Labels := by
      have ha : raw23981step1 = (fun i j => raw23981step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23981step1 raw23981step0; decide +kernel
      have hl : raw23981step1Labels = raw23981step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23981step0 raw23981step0Labels permutation36 permutation4
    mixedMoment B raw23981step1 raw23981step1Labels = mixedMoment B raw23981step2 raw23981step2Labels := by
      have ha : raw23981step2 = -raw23981step1 := by apply Matrix.ext; change ∀ i j, raw23981step2 i j = -(raw23981step1 i j); unfold raw23981step2 raw23981step1; decide +kernel
      have hl : raw23981step2Labels = raw23981step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw23982 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23982 raw23982Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw23982 raw23982Labels = mixedMoment B raw23982step0 raw23982step0Labels := by
      have ha : raw23982step0 = (fun i j => raw23982 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23982step0 raw23982; decide +kernel
      have hl : raw23982step0Labels = raw23982Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23982 raw23982Labels permutation188 permutation2
    mixedMoment B raw23982step0 raw23982step0Labels = mixedMoment B raw23982step1 raw23982step1Labels := by
      have ha : raw23982step1 = -raw23982step0 := by apply Matrix.ext; change ∀ i j, raw23982step1 i j = -(raw23982step0 i j); unfold raw23982step1 raw23982step0; decide +kernel
      have hl : raw23982step1Labels = raw23982step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw23983 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23983 raw23983Labels = mixedMoment B node3240 node3240Labels := by
  calc
    mixedMoment B raw23983 raw23983Labels = mixedMoment B raw23983step0 raw23983step0Labels := by
      have hz : ∀ j, raw23983 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23983step0 = (fun i j => raw23983 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23983step0 raw23983; decide +kernel
      have hl : raw23983step0Labels = raw23983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23983 raw23983Labels permutation346 hz
    mixedMoment B raw23983step0 raw23983step0Labels = mixedMoment B raw23983step1 raw23983step1Labels := by
      have ha : raw23983step1 = (fun i j => raw23983step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23983step1 raw23983step0; decide +kernel
      have hl : raw23983step1Labels = raw23983step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23983step0 raw23983step0Labels permutation32 permutation4
    mixedMoment B raw23983step1 raw23983step1Labels = mixedMoment B raw23983step2 raw23983step2Labels := by
      have ha : raw23983step2 = -raw23983step1 := by apply Matrix.ext; change ∀ i j, raw23983step2 i j = -(raw23983step1 i j); unfold raw23983step2 raw23983step1; decide +kernel
      have hl : raw23983step2Labels = raw23983step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3240 node3240Labels := by rfl

def raw23984 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23984 raw23984Labels = mixedMoment B node3278 node3278Labels := by
  calc
    mixedMoment B raw23984 raw23984Labels = mixedMoment B raw23984step0 raw23984step0Labels := by
      have ha : raw23984step0 = (fun i j => raw23984 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23984step0 raw23984; decide +kernel
      have hl : raw23984step0Labels = raw23984Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23984 raw23984Labels permutation152 permutation4
    mixedMoment B raw23984step0 raw23984step0Labels = mixedMoment B raw23984step1 raw23984step1Labels := by
      have ha : raw23984step1 = -raw23984step0 := by apply Matrix.ext; change ∀ i j, raw23984step1 i j = -(raw23984step0 i j); unfold raw23984step1 raw23984step0; decide +kernel
      have hl : raw23984step1Labels = raw23984step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3278 node3278Labels := by rfl

def raw23985 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw23985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23985step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23985 raw23985Labels = mixedMoment B node3287 node3287Labels := by
  calc
    mixedMoment B raw23985 raw23985Labels = mixedMoment B raw23985step0 raw23985step0Labels := by
      have hz : ∀ j, raw23985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23985step0 = (fun i j => raw23985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23985step0 raw23985; decide +kernel
      have hl : raw23985step0Labels = raw23985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23985 raw23985Labels permutation346 hz
    mixedMoment B raw23985step0 raw23985step0Labels = mixedMoment B raw23985step1 raw23985step1Labels := by
      have ha : raw23985step1 = (fun i j => raw23985step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23985step1 raw23985step0; decide +kernel
      have hl : raw23985step1Labels = raw23985step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23985step0 raw23985step0Labels permutation32 permutation4
    mixedMoment B raw23985step1 raw23985step1Labels = mixedMoment B raw23985step2 raw23985step2Labels := by
      have ha : raw23985step2 = -raw23985step1 := by apply Matrix.ext; change ∀ i j, raw23985step2 i j = -(raw23985step1 i j); unfold raw23985step2 raw23985step1; decide +kernel
      have hl : raw23985step2Labels = raw23985step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3287 node3287Labels := by rfl

def raw23986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23986 raw23986Labels = mixedMoment B node1257 node1257Labels := by
  calc
    mixedMoment B raw23986 raw23986Labels = mixedMoment B raw23986step0 raw23986step0Labels := by
      have hz : ∀ j, raw23986 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23986step0 = (fun i j => raw23986 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23986step0 raw23986; decide +kernel
      have hl : raw23986step0Labels = raw23986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23986 raw23986Labels permutation346 hz
    mixedMoment B raw23986step0 raw23986step0Labels = mixedMoment B raw23986step1 raw23986step1Labels := by
      have ha : raw23986step1 = (fun i j => raw23986step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23986step1 raw23986step0; decide +kernel
      have hl : raw23986step1Labels = raw23986step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23986step0 raw23986step0Labels permutation34 permutation2
    _ = mixedMoment B node1257 node1257Labels := by rfl

def raw23987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23987 raw23987Labels = mixedMoment B node2629 node2629Labels := by
  calc
    mixedMoment B raw23987 raw23987Labels = mixedMoment B raw23987step0 raw23987step0Labels := by
      have hz : ∀ j, raw23987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23987step0 = (fun i j => raw23987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23987step0 raw23987; decide +kernel
      have hl : raw23987step0Labels = raw23987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23987 raw23987Labels permutation346 hz
    mixedMoment B raw23987step0 raw23987step0Labels = mixedMoment B raw23987step1 raw23987step1Labels := by
      have ha : raw23987step1 = (fun i j => raw23987step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23987step1 raw23987step0; decide +kernel
      have hl : raw23987step1Labels = raw23987step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23987step0 raw23987step0Labels permutation34 permutation2
    _ = mixedMoment B node2629 node2629Labels := by rfl

def raw23988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23988 raw23988Labels = mixedMoment B node2565 node2565Labels := by
  calc
    mixedMoment B raw23988 raw23988Labels = mixedMoment B raw23988step0 raw23988step0Labels := by
      have ha : raw23988step0 = (fun i j => raw23988 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23988step0 raw23988; decide +kernel
      have hl : raw23988step0Labels = raw23988Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23988 raw23988Labels permutation178 permutation2
    _ = mixedMoment B node2565 node2565Labels := by rfl

def raw23989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw23989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23989 raw23989Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw23989 raw23989Labels = mixedMoment B raw23989step0 raw23989step0Labels := by
      have hz : ∀ j, raw23989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23989step0 = (fun i j => raw23989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23989step0 raw23989; decide +kernel
      have hl : raw23989step0Labels = raw23989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23989 raw23989Labels permutation346 hz
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw23990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw23990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw23990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23990 raw23990Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw23990 raw23990Labels = mixedMoment B raw23990step0 raw23990step0Labels := by
      have hz : ∀ j, raw23990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23990step0 = (fun i j => raw23990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23990step0 raw23990; decide +kernel
      have hl : raw23990step0Labels = raw23990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23990 raw23990Labels permutation346 hz
    mixedMoment B raw23990step0 raw23990step0Labels = mixedMoment B raw23990step1 raw23990step1Labels := by
      have ha : raw23990step1 = (fun i j => raw23990step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23990step1 raw23990step0; decide +kernel
      have hl : raw23990step1Labels = raw23990step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23990step0 raw23990step0Labels permutation44 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw23991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2], ![1, 1, -2]]
def raw23991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2], ![1, 1, -2]]
def raw23991step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw23991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23991 raw23991Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw23991 raw23991Labels = mixedMoment B raw23991step0 raw23991step0Labels := by
      have hz : ∀ j, raw23991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23991step0 = (fun i j => raw23991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23991step0 raw23991; decide +kernel
      have hl : raw23991step0Labels = raw23991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23991 raw23991Labels permutation346 hz
    mixedMoment B raw23991step0 raw23991step0Labels = mixedMoment B raw23991step1 raw23991step1Labels := by
      have ha : raw23991step1 = (fun i j => raw23991step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23991step1 raw23991step0; decide +kernel
      have hl : raw23991step1Labels = raw23991step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23991step0 raw23991step0Labels permutation34 permutation2
    _ = mixedMoment B node2760 node2760Labels := by rfl

def raw23992 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![-2, 2], ![2, -2]]
def raw23992Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23992step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-2, 2], ![2, -2]]
def raw23992step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23992step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw23992step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23992 raw23992Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw23992 raw23992Labels = mixedMoment B raw23992step0 raw23992step0Labels := by
      have hz : ∀ j, raw23992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23992step0 = (fun i j => raw23992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23992step0 raw23992; decide +kernel
      have hl : raw23992step0Labels = raw23992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23992 raw23992Labels permutation346 hz
    mixedMoment B raw23992step0 raw23992step0Labels = mixedMoment B raw23992step1 raw23992step1Labels := by
      have ha : raw23992step1 = (fun i j => raw23992step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23992step1 raw23992step0; decide +kernel
      have hl : raw23992step1Labels = raw23992step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23992step0 raw23992step0Labels permutation44 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw23993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23993 raw23993Labels = mixedMoment B node1130 node1130Labels := by
  calc
    _ = mixedMoment B node1130 node1130Labels := by rfl

def raw23994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23994 raw23994Labels = mixedMoment B node1141 node1141Labels := by
  calc
    mixedMoment B raw23994 raw23994Labels = mixedMoment B raw23994step0 raw23994step0Labels := by
      have hz : ∀ j, raw23994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23994step0 = (fun i j => raw23994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23994step0 raw23994; decide +kernel
      have hl : raw23994step0Labels = raw23994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23994 raw23994Labels permutation346 hz
    mixedMoment B raw23994step0 raw23994step0Labels = mixedMoment B raw23994step1 raw23994step1Labels := by
      have ha : raw23994step1 = (fun i j => raw23994step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23994step1 raw23994step0; decide +kernel
      have hl : raw23994step1Labels = raw23994step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23994step0 raw23994step0Labels permutation35 permutation2
    _ = mixedMoment B node1141 node1141Labels := by rfl

def raw23995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23995 raw23995Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw23995 raw23995Labels = mixedMoment B raw23995step0 raw23995step0Labels := by
      have hz : ∀ j, raw23995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23995step0 = (fun i j => raw23995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23995step0 raw23995; decide +kernel
      have hl : raw23995step0Labels = raw23995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23995 raw23995Labels permutation346 hz
    mixedMoment B raw23995step0 raw23995step0Labels = mixedMoment B raw23995step1 raw23995step1Labels := by
      have ha : raw23995step1 = (fun i j => raw23995step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23995step1 raw23995step0; decide +kernel
      have hl : raw23995step1Labels = raw23995step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23995step0 raw23995step0Labels permutation33 permutation2
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw23996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw23996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw23996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23996 raw23996Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw23996 raw23996Labels = mixedMoment B raw23996step0 raw23996step0Labels := by
      have hz : ∀ j, raw23996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23996step0 = (fun i j => raw23996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23996step0 raw23996; decide +kernel
      have hl : raw23996step0Labels = raw23996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23996 raw23996Labels permutation346 hz
    _ = mixedMoment B node1137 node1137Labels := by rfl

def raw23997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw23997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw23997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23997 raw23997Labels = mixedMoment B node638 node638Labels := by
  calc
    mixedMoment B raw23997 raw23997Labels = mixedMoment B raw23997step0 raw23997step0Labels := by
      have hz : ∀ j, raw23997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23997step0 = (fun i j => raw23997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23997step0 raw23997; decide +kernel
      have hl : raw23997step0Labels = raw23997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23997 raw23997Labels permutation346 hz
    mixedMoment B raw23997step0 raw23997step0Labels = mixedMoment B raw23997step1 raw23997step1Labels := by
      have ha : raw23997step1 = (fun i j => raw23997step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23997step1 raw23997step0; decide +kernel
      have hl : raw23997step1Labels = raw23997step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23997step0 raw23997step0Labels permutation46 permutation2
    _ = mixedMoment B node638 node638Labels := by rfl

def raw23998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw23998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23998 raw23998Labels = mixedMoment B node1156 node1156Labels := by
  calc
    mixedMoment B raw23998 raw23998Labels = mixedMoment B raw23998step0 raw23998step0Labels := by
      have ha : raw23998step0 = (fun i j => raw23998 (permutation190 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23998step0 raw23998; decide +kernel
      have hl : raw23998step0Labels = raw23998Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23998 raw23998Labels permutation190 permutation2
    _ = mixedMoment B node1156 node1156Labels := by rfl

def raw23999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw23999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw23999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23999 raw23999Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw23999 raw23999Labels = mixedMoment B raw23999step0 raw23999step0Labels := by
      have hz : ∀ j, raw23999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23999step0 = (fun i j => raw23999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23999step0 raw23999; decide +kernel
      have hl : raw23999step0Labels = raw23999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23999 raw23999Labels permutation346 hz
    mixedMoment B raw23999step0 raw23999step0Labels = mixedMoment B raw23999step1 raw23999step1Labels := by
      have ha : raw23999step1 = (fun i j => raw23999step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23999step1 raw23999step0; decide +kernel
      have hl : raw23999step1Labels = raw23999step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23999step0 raw23999step0Labels permutation46 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw24000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24000 raw24000Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw24000 raw24000Labels = mixedMoment B raw24000step0 raw24000step0Labels := by
      have hz : ∀ j, raw24000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24000step0 = (fun i j => raw24000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24000step0 raw24000; decide +kernel
      have hl : raw24000step0Labels = raw24000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24000 raw24000Labels permutation346 hz
    mixedMoment B raw24000step0 raw24000step0Labels = mixedMoment B raw24000step1 raw24000step1Labels := by
      have ha : raw24000step1 = (fun i j => raw24000step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24000step1 raw24000step0; decide +kernel
      have hl : raw24000step1Labels = raw24000step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24000step0 raw24000step0Labels permutation46 permutation2
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw24001 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw24001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24001 raw24001Labels = mixedMoment B node1640 node1640Labels := by
  calc
    mixedMoment B raw24001 raw24001Labels = mixedMoment B raw24001step0 raw24001step0Labels := by
      have hz : ∀ j, raw24001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24001step0 = (fun i j => raw24001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24001step0 raw24001; decide +kernel
      have hl : raw24001step0Labels = raw24001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24001 raw24001Labels permutation346 hz
    mixedMoment B raw24001step0 raw24001step0Labels = mixedMoment B raw24001step1 raw24001step1Labels := by
      have ha : raw24001step1 = (fun i j => raw24001step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24001step1 raw24001step0; decide +kernel
      have hl : raw24001step1Labels = raw24001step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24001step0 raw24001step0Labels permutation46 permutation2
    mixedMoment B raw24001step1 raw24001step1Labels = mixedMoment B raw24001step2 raw24001step2Labels := by
      have ha : raw24001step2 = -raw24001step1 := by apply Matrix.ext; change ∀ i j, raw24001step2 i j = -(raw24001step1 i j); unfold raw24001step2 raw24001step1; decide +kernel
      have hl : raw24001step2Labels = raw24001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1640 node1640Labels := by rfl

def raw24002 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw24002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24002 raw24002Labels = mixedMoment B node1635 node1635Labels := by
  calc
    mixedMoment B raw24002 raw24002Labels = mixedMoment B raw24002step0 raw24002step0Labels := by
      have ha : raw24002step0 = (fun i j => raw24002 (permutation234 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24002step0 raw24002; decide +kernel
      have hl : raw24002step0Labels = raw24002Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24002 raw24002Labels permutation234 permutation2
    mixedMoment B raw24002step0 raw24002step0Labels = mixedMoment B raw24002step1 raw24002step1Labels := by
      have ha : raw24002step1 = -raw24002step0 := by apply Matrix.ext; change ∀ i j, raw24002step1 i j = -(raw24002step0 i j); unfold raw24002step1 raw24002step0; decide +kernel
      have hl : raw24002step1Labels = raw24002step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1635 node1635Labels := by rfl

def raw24003 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24003 raw24003Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw24003 raw24003Labels = mixedMoment B raw24003step0 raw24003step0Labels := by
      have hz : ∀ j, raw24003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24003step0 = (fun i j => raw24003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24003step0 raw24003; decide +kernel
      have hl : raw24003step0Labels = raw24003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24003 raw24003Labels permutation346 hz
    mixedMoment B raw24003step0 raw24003step0Labels = mixedMoment B raw24003step1 raw24003step1Labels := by
      have ha : raw24003step1 = (fun i j => raw24003step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24003step1 raw24003step0; decide +kernel
      have hl : raw24003step1Labels = raw24003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24003step0 raw24003step0Labels permutation40 permutation2
    mixedMoment B raw24003step1 raw24003step1Labels = mixedMoment B raw24003step2 raw24003step2Labels := by
      have ha : raw24003step2 = -raw24003step1 := by apply Matrix.ext; change ∀ i j, raw24003step2 i j = -(raw24003step1 i j); unfold raw24003step2 raw24003step1; decide +kernel
      have hl : raw24003step2Labels = raw24003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw24004 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw24004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24004 raw24004Labels = mixedMoment B node1637 node1637Labels := by
  calc
    mixedMoment B raw24004 raw24004Labels = mixedMoment B raw24004step0 raw24004step0Labels := by
      have hz : ∀ j, raw24004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24004step0 = (fun i j => raw24004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24004step0 raw24004; decide +kernel
      have hl : raw24004step0Labels = raw24004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24004 raw24004Labels permutation346 hz
    mixedMoment B raw24004step0 raw24004step0Labels = mixedMoment B raw24004step1 raw24004step1Labels := by
      have ha : raw24004step1 = (fun i j => raw24004step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24004step1 raw24004step0; decide +kernel
      have hl : raw24004step1Labels = raw24004step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24004step0 raw24004step0Labels permutation46 permutation2
    mixedMoment B raw24004step1 raw24004step1Labels = mixedMoment B raw24004step2 raw24004step2Labels := by
      have ha : raw24004step2 = -raw24004step1 := by apply Matrix.ext; change ∀ i j, raw24004step2 i j = -(raw24004step1 i j); unfold raw24004step2 raw24004step1; decide +kernel
      have hl : raw24004step2Labels = raw24004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1637 node1637Labels := by rfl

def raw24005 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw24005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw24005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24005 raw24005Labels = mixedMoment B node1612 node1612Labels := by
  calc
    mixedMoment B raw24005 raw24005Labels = mixedMoment B raw24005step0 raw24005step0Labels := by
      have hz : ∀ j, raw24005 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24005step0 = (fun i j => raw24005 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24005step0 raw24005; decide +kernel
      have hl : raw24005step0Labels = raw24005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24005 raw24005Labels permutation346 hz
    mixedMoment B raw24005step0 raw24005step0Labels = mixedMoment B raw24005step1 raw24005step1Labels := by
      have ha : raw24005step1 = (fun i j => raw24005step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24005step1 raw24005step0; decide +kernel
      have hl : raw24005step1Labels = raw24005step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24005step0 raw24005step0Labels permutation36 permutation4
    mixedMoment B raw24005step1 raw24005step1Labels = mixedMoment B raw24005step2 raw24005step2Labels := by
      have ha : raw24005step2 = -raw24005step1 := by apply Matrix.ext; change ∀ i j, raw24005step2 i j = -(raw24005step1 i j); unfold raw24005step2 raw24005step1; decide +kernel
      have hl : raw24005step2Labels = raw24005step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1612 node1612Labels := by rfl

def raw24006 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw24006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw24006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24006 raw24006Labels = mixedMoment B node1610 node1610Labels := by
  calc
    mixedMoment B raw24006 raw24006Labels = mixedMoment B raw24006step0 raw24006step0Labels := by
      have hz : ∀ j, raw24006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24006step0 = (fun i j => raw24006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24006step0 raw24006; decide +kernel
      have hl : raw24006step0Labels = raw24006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24006 raw24006Labels permutation346 hz
    mixedMoment B raw24006step0 raw24006step0Labels = mixedMoment B raw24006step1 raw24006step1Labels := by
      have ha : raw24006step1 = (fun i j => raw24006step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24006step1 raw24006step0; decide +kernel
      have hl : raw24006step1Labels = raw24006step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24006step0 raw24006step0Labels permutation36 permutation4
    mixedMoment B raw24006step1 raw24006step1Labels = mixedMoment B raw24006step2 raw24006step2Labels := by
      have ha : raw24006step2 = -raw24006step1 := by apply Matrix.ext; change ∀ i j, raw24006step2 i j = -(raw24006step1 i j); unfold raw24006step2 raw24006step1; decide +kernel
      have hl : raw24006step2Labels = raw24006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1610 node1610Labels := by rfl

def raw24007 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24007 raw24007Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw24007 raw24007Labels = mixedMoment B raw24007step0 raw24007step0Labels := by
      have hz : ∀ j, raw24007 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24007step0 = (fun i j => raw24007 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24007step0 raw24007; decide +kernel
      have hl : raw24007step0Labels = raw24007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24007 raw24007Labels permutation265 hz
    mixedMoment B raw24007step0 raw24007step0Labels = mixedMoment B raw24007step1 raw24007step1Labels := by
      have ha : raw24007step1 = (fun i j => raw24007step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24007step1 raw24007step0; decide +kernel
      have hl : raw24007step1Labels = raw24007step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24007step0 raw24007step0Labels permutation36 permutation4
    mixedMoment B raw24007step1 raw24007step1Labels = mixedMoment B raw24007step2 raw24007step2Labels := by
      have ha : raw24007step2 = -raw24007step1 := by apply Matrix.ext; change ∀ i j, raw24007step2 i j = -(raw24007step1 i j); unfold raw24007step2 raw24007step1; decide +kernel
      have hl : raw24007step2Labels = raw24007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw24008 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24008step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw24008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24008 raw24008Labels = mixedMoment B node3308 node3308Labels := by
  calc
    mixedMoment B raw24008 raw24008Labels = mixedMoment B raw24008step0 raw24008step0Labels := by
      have hz : ∀ j, raw24008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24008step0 = (fun i j => raw24008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24008step0 raw24008; decide +kernel
      have hl : raw24008step0Labels = raw24008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24008 raw24008Labels permutation346 hz
    mixedMoment B raw24008step0 raw24008step0Labels = mixedMoment B raw24008step1 raw24008step1Labels := by
      have hz : ∀ j, raw24008step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24008step1 = (fun i j => raw24008step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24008step1 raw24008step0; decide +kernel
      have hl : raw24008step1Labels = raw24008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24008step0 raw24008step0Labels permutation56 hz
    mixedMoment B raw24008step1 raw24008step1Labels = mixedMoment B raw24008step2 raw24008step2Labels := by
      have ha : raw24008step2 = -raw24008step1 := by apply Matrix.ext; change ∀ i j, raw24008step2 i j = -(raw24008step1 i j); unfold raw24008step2 raw24008step1; decide +kernel
      have hl : raw24008step2Labels = raw24008step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3308 node3308Labels := by rfl

def raw24009 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw24009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24009 raw24009Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw24009 raw24009Labels = mixedMoment B raw24009step0 raw24009step0Labels := by
      have hz : ∀ j, raw24009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24009step0 = (fun i j => raw24009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24009step0 raw24009; decide +kernel
      have hl : raw24009step0Labels = raw24009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24009 raw24009Labels permutation346 hz
    mixedMoment B raw24009step0 raw24009step0Labels = mixedMoment B raw24009step1 raw24009step1Labels := by
      have hz : ∀ j, raw24009step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24009step1 = (fun i j => raw24009step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24009step1 raw24009step0; decide +kernel
      have hl : raw24009step1Labels = raw24009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24009step0 raw24009step0Labels permutation56 hz
    mixedMoment B raw24009step1 raw24009step1Labels = mixedMoment B raw24009step2 raw24009step2Labels := by
      have ha : raw24009step2 = (fun i j => raw24009step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24009step2 raw24009step1; decide +kernel
      have hl : raw24009step2Labels = raw24009step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24009step1 raw24009step1Labels permutation29 permutation2
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw24010 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24010 raw24010Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw24010 raw24010Labels = mixedMoment B raw24010step0 raw24010step0Labels := by
      have ha : raw24010step0 = (fun i j => raw24010 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24010step0 raw24010; decide +kernel
      have hl : raw24010step0Labels = raw24010Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24010 raw24010Labels permutation184 permutation2
    mixedMoment B raw24010step0 raw24010step0Labels = mixedMoment B raw24010step1 raw24010step1Labels := by
      have ha : raw24010step1 = -raw24010step0 := by apply Matrix.ext; change ∀ i j, raw24010step1 i j = -(raw24010step0 i j); unfold raw24010step1 raw24010step0; decide +kernel
      have hl : raw24010step1Labels = raw24010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3288 node3288Labels := by rfl

def raw24011 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24011step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24011 raw24011Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw24011 raw24011Labels = mixedMoment B raw24011step0 raw24011step0Labels := by
      have hz : ∀ j, raw24011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24011step0 = (fun i j => raw24011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24011step0 raw24011; decide +kernel
      have hl : raw24011step0Labels = raw24011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24011 raw24011Labels permutation346 hz
    mixedMoment B raw24011step0 raw24011step0Labels = mixedMoment B raw24011step1 raw24011step1Labels := by
      have ha : raw24011step1 = (fun i j => raw24011step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24011step1 raw24011step0; decide +kernel
      have hl : raw24011step1Labels = raw24011step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24011step0 raw24011step0Labels permutation37 permutation4
    mixedMoment B raw24011step1 raw24011step1Labels = mixedMoment B raw24011step2 raw24011step2Labels := by
      have ha : raw24011step2 = -raw24011step1 := by apply Matrix.ext; change ∀ i j, raw24011step2 i j = -(raw24011step1 i j); unfold raw24011step2 raw24011step1; decide +kernel
      have hl : raw24011step2Labels = raw24011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw24012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24012 raw24012Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw24012 raw24012Labels = mixedMoment B raw24012step0 raw24012step0Labels := by
      have ha : raw24012step0 = (fun i j => raw24012 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24012step0 raw24012; decide +kernel
      have hl : raw24012step0Labels = raw24012Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24012 raw24012Labels permutation160 permutation2
    _ = mixedMoment B node1126 node1126Labels := by rfl

def raw24013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24013 raw24013Labels = mixedMoment B node1113 node1113Labels := by
  calc
    mixedMoment B raw24013 raw24013Labels = mixedMoment B raw24013step0 raw24013step0Labels := by
      have ha : raw24013step0 = (fun i j => raw24013 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24013step0 raw24013; decide +kernel
      have hl : raw24013step0Labels = raw24013Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24013 raw24013Labels permutation154 permutation2
    _ = mixedMoment B node1113 node1113Labels := by rfl

def raw24014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24014 raw24014Labels = mixedMoment B node1113 node1113Labels := by
  calc
    _ = mixedMoment B node1113 node1113Labels := by rfl

def raw24015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw24015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24015 raw24015Labels = mixedMoment B node1111 node1111Labels := by
  calc
    _ = mixedMoment B node1111 node1111Labels := by rfl

def raw24016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24016 raw24016Labels = mixedMoment B node623 node623Labels := by
  calc
    mixedMoment B raw24016 raw24016Labels = mixedMoment B raw24016step0 raw24016step0Labels := by
      have ha : raw24016step0 = (fun i j => raw24016 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24016step0 raw24016; decide +kernel
      have hl : raw24016step0Labels = raw24016Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24016 raw24016Labels permutation160 permutation2
    _ = mixedMoment B node623 node623Labels := by rfl

def raw24017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24017 raw24017Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24017 raw24017Labels = mixedMoment B raw24017step0 raw24017step0Labels := by
      have hz : ∀ j, raw24017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24017step0 = (fun i j => raw24017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24017step0 raw24017; decide +kernel
      have hl : raw24017step0Labels = raw24017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24017 raw24017Labels permutation434 hz
    mixedMoment B raw24017step0 raw24017step0Labels = mixedMoment B raw24017step1 raw24017step1Labels := by
      have ha : raw24017step1 = (fun i j => raw24017step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24017step1 raw24017step0; decide +kernel
      have hl : raw24017step1Labels = raw24017step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24017step0 raw24017step0Labels permutation34 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw24018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24018 raw24018Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24018 raw24018Labels = mixedMoment B raw24018step0 raw24018step0Labels := by
      have hz : ∀ j, raw24018 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24018step0 = (fun i j => raw24018 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24018step0 raw24018; decide +kernel
      have hl : raw24018step0Labels = raw24018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24018 raw24018Labels permutation520 hz
    mixedMoment B raw24018step0 raw24018step0Labels = mixedMoment B raw24018step1 raw24018step1Labels := by
      have ha : raw24018step1 = (fun i j => raw24018step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24018step1 raw24018step0; decide +kernel
      have hl : raw24018step1Labels = raw24018step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24018step0 raw24018step0Labels permutation34 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw24019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24019 raw24019Labels = mixedMoment B node629 node629Labels := by
  calc
    mixedMoment B raw24019 raw24019Labels = mixedMoment B raw24019step0 raw24019step0Labels := by
      have ha : raw24019step0 = (fun i j => raw24019 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24019step0 raw24019; decide +kernel
      have hl : raw24019step0Labels = raw24019Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24019 raw24019Labels permutation176 permutation2
    _ = mixedMoment B node629 node629Labels := by rfl

def raw24020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24020 raw24020Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw24020 raw24020Labels = mixedMoment B raw24020step0 raw24020step0Labels := by
      have ha : raw24020step0 = (fun i j => raw24020 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24020step0 raw24020; decide +kernel
      have hl : raw24020step0Labels = raw24020Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24020 raw24020Labels permutation176 permutation2
    _ = mixedMoment B node1216 node1216Labels := by rfl

def raw24021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24021 raw24021Labels = mixedMoment B node1135 node1135Labels := by
  calc
    mixedMoment B raw24021 raw24021Labels = mixedMoment B raw24021step0 raw24021step0Labels := by
      have ha : raw24021step0 = (fun i j => raw24021 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24021step0 raw24021; decide +kernel
      have hl : raw24021step0Labels = raw24021Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24021 raw24021Labels permutation176 permutation2
    _ = mixedMoment B node1135 node1135Labels := by rfl

def raw24022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24022 raw24022Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw24022 raw24022Labels = mixedMoment B raw24022step0 raw24022step0Labels := by
      have ha : raw24022step0 = (fun i j => raw24022 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24022step0 raw24022; decide +kernel
      have hl : raw24022step0Labels = raw24022Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24022 raw24022Labels permutation182 permutation2
    _ = mixedMoment B node1216 node1216Labels := by rfl

def raw24023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw24023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24023 raw24023Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw24023 raw24023Labels = mixedMoment B raw24023step0 raw24023step0Labels := by
      have ha : raw24023step0 = (fun i j => raw24023 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24023step0 raw24023; decide +kernel
      have hl : raw24023step0Labels = raw24023Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24023 raw24023Labels permutation188 permutation2
    _ = mixedMoment B node1216 node1216Labels := by rfl

def raw24024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24024 raw24024Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw24024 raw24024Labels = mixedMoment B raw24024step0 raw24024step0Labels := by
      have ha : raw24024step0 = (fun i j => raw24024 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24024step0 raw24024; decide +kernel
      have hl : raw24024step0Labels = raw24024Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24024 raw24024Labels permutation176 permutation2
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw24025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24025 raw24025Labels = mixedMoment B node1117 node1117Labels := by
  calc
    mixedMoment B raw24025 raw24025Labels = mixedMoment B raw24025step0 raw24025step0Labels := by
      have ha : raw24025step0 = (fun i j => raw24025 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24025step0 raw24025; decide +kernel
      have hl : raw24025step0Labels = raw24025Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24025 raw24025Labels permutation179 permutation2
    _ = mixedMoment B node1117 node1117Labels := by rfl

def raw24026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24026 raw24026Labels = mixedMoment B node1117 node1117Labels := by
  calc
    mixedMoment B raw24026 raw24026Labels = mixedMoment B raw24026step0 raw24026step0Labels := by
      have ha : raw24026step0 = (fun i j => raw24026 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24026step0 raw24026; decide +kernel
      have hl : raw24026step0Labels = raw24026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24026 raw24026Labels permutation177 permutation2
    _ = mixedMoment B node1117 node1117Labels := by rfl

def raw24027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24027 raw24027Labels = mixedMoment B node1116 node1116Labels := by
  calc
    mixedMoment B raw24027 raw24027Labels = mixedMoment B raw24027step0 raw24027step0Labels := by
      have ha : raw24027step0 = (fun i j => raw24027 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24027step0 raw24027; decide +kernel
      have hl : raw24027step0Labels = raw24027Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24027 raw24027Labels permutation176 permutation2
    _ = mixedMoment B node1116 node1116Labels := by rfl

def raw24028 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw24028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24028 raw24028Labels = mixedMoment B node1609 node1609Labels := by
  calc
    mixedMoment B raw24028 raw24028Labels = mixedMoment B raw24028step0 raw24028step0Labels := by
      have ha : raw24028step0 = (fun i j => raw24028 (permutation197 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24028step0 raw24028; decide +kernel
      have hl : raw24028step0Labels = raw24028Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24028 raw24028Labels permutation197 permutation2
    mixedMoment B raw24028step0 raw24028step0Labels = mixedMoment B raw24028step1 raw24028step1Labels := by
      have ha : raw24028step1 = -raw24028step0 := by apply Matrix.ext; change ∀ i j, raw24028step1 i j = -(raw24028step0 i j); unfold raw24028step1 raw24028step0; decide +kernel
      have hl : raw24028step1Labels = raw24028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1609 node1609Labels := by rfl

def raw24029 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw24029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24029 raw24029Labels = mixedMoment B node1607 node1607Labels := by
  calc
    mixedMoment B raw24029 raw24029Labels = mixedMoment B raw24029step0 raw24029step0Labels := by
      have ha : raw24029step0 = (fun i j => raw24029 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24029step0 raw24029; decide +kernel
      have hl : raw24029step0Labels = raw24029Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24029 raw24029Labels permutation195 permutation2
    mixedMoment B raw24029step0 raw24029step0Labels = mixedMoment B raw24029step1 raw24029step1Labels := by
      have ha : raw24029step1 = -raw24029step0 := by apply Matrix.ext; change ∀ i j, raw24029step1 i j = -(raw24029step0 i j); unfold raw24029step1 raw24029step0; decide +kernel
      have hl : raw24029step1Labels = raw24029step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1607 node1607Labels := by rfl

def raw24030 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw24030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24030 raw24030Labels = mixedMoment B node1607 node1607Labels := by
  calc
    mixedMoment B raw24030 raw24030Labels = mixedMoment B raw24030step0 raw24030step0Labels := by
      have ha : raw24030step0 = (fun i j => raw24030 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24030step0 raw24030; decide +kernel
      have hl : raw24030step0Labels = raw24030Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24030 raw24030Labels permutation194 permutation2
    mixedMoment B raw24030step0 raw24030step0Labels = mixedMoment B raw24030step1 raw24030step1Labels := by
      have ha : raw24030step1 = -raw24030step0 := by apply Matrix.ext; change ∀ i j, raw24030step1 i j = -(raw24030step0 i j); unfold raw24030step1 raw24030step0; decide +kernel
      have hl : raw24030step1Labels = raw24030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1607 node1607Labels := by rfl

def raw24031 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24031 raw24031Labels = mixedMoment B node1616 node1616Labels := by
  calc
    mixedMoment B raw24031 raw24031Labels = mixedMoment B raw24031step0 raw24031step0Labels := by
      have ha : raw24031step0 = (fun i j => raw24031 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24031step0 raw24031; decide +kernel
      have hl : raw24031step0Labels = raw24031Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24031 raw24031Labels permutation176 permutation2
    mixedMoment B raw24031step0 raw24031step0Labels = mixedMoment B raw24031step1 raw24031step1Labels := by
      have ha : raw24031step1 = -raw24031step0 := by apply Matrix.ext; change ∀ i j, raw24031step1 i j = -(raw24031step0 i j); unfold raw24031step1 raw24031step0; decide +kernel
      have hl : raw24031step1Labels = raw24031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1616 node1616Labels := by rfl

def raw24032 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw24032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24032 raw24032Labels = mixedMoment B node1594 node1594Labels := by
  calc
    mixedMoment B raw24032 raw24032Labels = mixedMoment B raw24032step0 raw24032step0Labels := by
      have ha : raw24032step0 = (fun i j => raw24032 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24032step0 raw24032; decide +kernel
      have hl : raw24032step0Labels = raw24032Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24032 raw24032Labels permutation160 permutation4
    mixedMoment B raw24032step0 raw24032step0Labels = mixedMoment B raw24032step1 raw24032step1Labels := by
      have ha : raw24032step1 = -raw24032step0 := by apply Matrix.ext; change ∀ i j, raw24032step1 i j = -(raw24032step0 i j); unfold raw24032step1 raw24032step0; decide +kernel
      have hl : raw24032step1Labels = raw24032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1594 node1594Labels := by rfl

def raw24033 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24033 raw24033Labels = mixedMoment B node1597 node1597Labels := by
  calc
    mixedMoment B raw24033 raw24033Labels = mixedMoment B raw24033step0 raw24033step0Labels := by
      have ha : raw24033step0 = (fun i j => raw24033 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24033step0 raw24033; decide +kernel
      have hl : raw24033step0Labels = raw24033Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24033 raw24033Labels permutation164 permutation4
    mixedMoment B raw24033step0 raw24033step0Labels = mixedMoment B raw24033step1 raw24033step1Labels := by
      have ha : raw24033step1 = -raw24033step0 := by apply Matrix.ext; change ∀ i j, raw24033step1 i j = -(raw24033step0 i j); unfold raw24033step1 raw24033step0; decide +kernel
      have hl : raw24033step1Labels = raw24033step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1597 node1597Labels := by rfl

def raw24034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24034 raw24034Labels = mixedMoment B node1597 node1597Labels := by
  calc
    mixedMoment B raw24034 raw24034Labels = mixedMoment B raw24034step0 raw24034step0Labels := by
      have ha : raw24034step0 = (fun i j => raw24034 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24034step0 raw24034; decide +kernel
      have hl : raw24034step0Labels = raw24034Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24034 raw24034Labels permutation158 permutation4
    mixedMoment B raw24034step0 raw24034step0Labels = mixedMoment B raw24034step1 raw24034step1Labels := by
      have ha : raw24034step1 = -raw24034step0 := by apply Matrix.ext; change ∀ i j, raw24034step1 i j = -(raw24034step0 i j); unfold raw24034step1 raw24034step0; decide +kernel
      have hl : raw24034step1Labels = raw24034step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1597 node1597Labels := by rfl

def raw24035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw24035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24035 raw24035Labels = mixedMoment B node1592 node1592Labels := by
  calc
    mixedMoment B raw24035 raw24035Labels = mixedMoment B raw24035step0 raw24035step0Labels := by
      have ha : raw24035step0 = (fun i j => raw24035 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24035step0 raw24035; decide +kernel
      have hl : raw24035step0Labels = raw24035Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24035 raw24035Labels permutation160 permutation4
    mixedMoment B raw24035step0 raw24035step0Labels = mixedMoment B raw24035step1 raw24035step1Labels := by
      have ha : raw24035step1 = -raw24035step0 := by apply Matrix.ext; change ∀ i j, raw24035step1 i j = -(raw24035step0 i j); unfold raw24035step1 raw24035step0; decide +kernel
      have hl : raw24035step1Labels = raw24035step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1592 node1592Labels := by rfl

def raw24036 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24036 raw24036Labels = mixedMoment B node3238 node3238Labels := by
  calc
    mixedMoment B raw24036 raw24036Labels = mixedMoment B raw24036step0 raw24036step0Labels := by
      have ha : raw24036step0 = (fun i j => raw24036 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24036step0 raw24036; decide +kernel
      have hl : raw24036step0Labels = raw24036Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24036 raw24036Labels permutation164 permutation4
    mixedMoment B raw24036step0 raw24036step0Labels = mixedMoment B raw24036step1 raw24036step1Labels := by
      have ha : raw24036step1 = -raw24036step0 := by apply Matrix.ext; change ∀ i j, raw24036step1 i j = -(raw24036step0 i j); unfold raw24036step1 raw24036step0; decide +kernel
      have hl : raw24036step1Labels = raw24036step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3238 node3238Labels := by rfl

def raw24037 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24037 raw24037Labels = mixedMoment B node3285 node3285Labels := by
  calc
    mixedMoment B raw24037 raw24037Labels = mixedMoment B raw24037step0 raw24037step0Labels := by
      have ha : raw24037step0 = (fun i j => raw24037 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24037step0 raw24037; decide +kernel
      have hl : raw24037step0Labels = raw24037Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24037 raw24037Labels permutation164 permutation4
    mixedMoment B raw24037step0 raw24037step0Labels = mixedMoment B raw24037step1 raw24037step1Labels := by
      have ha : raw24037step1 = -raw24037step0 := by apply Matrix.ext; change ∀ i j, raw24037step1 i j = -(raw24037step0 i j); unfold raw24037step1 raw24037step0; decide +kernel
      have hl : raw24037step1Labels = raw24037step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3285 node3285Labels := by rfl

def raw24038 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24038 raw24038Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw24038 raw24038Labels = mixedMoment B raw24038step0 raw24038step0Labels := by
      have ha : raw24038step0 = (fun i j => raw24038 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24038step0 raw24038; decide +kernel
      have hl : raw24038step0Labels = raw24038Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24038 raw24038Labels permutation182 permutation2
    mixedMoment B raw24038step0 raw24038step0Labels = mixedMoment B raw24038step1 raw24038step1Labels := by
      have ha : raw24038step1 = -raw24038step0 := by apply Matrix.ext; change ∀ i j, raw24038step1 i j = -(raw24038step0 i j); unfold raw24038step1 raw24038step0; decide +kernel
      have hl : raw24038step1Labels = raw24038step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw24039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24039 raw24039Labels = mixedMoment B node2480 node2480Labels := by
  calc
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw24040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24040 raw24040Labels = mixedMoment B node1213 node1213Labels := by
  calc
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw24041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24041 raw24041Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw24041 raw24041Labels = mixedMoment B raw24041step0 raw24041step0Labels := by
      have ha : raw24041step0 = (fun i j => raw24041 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24041step0 raw24041; decide +kernel
      have hl : raw24041step0Labels = raw24041Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24041 raw24041Labels permutation158 permutation2
    _ = mixedMoment B node1129 node1129Labels := by rfl

def raw24042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24042 raw24042Labels = mixedMoment B node1117 node1117Labels := by
  calc
    mixedMoment B raw24042 raw24042Labels = mixedMoment B raw24042step0 raw24042step0Labels := by
      have ha : raw24042step0 = (fun i j => raw24042 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24042step0 raw24042; decide +kernel
      have hl : raw24042step0Labels = raw24042Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24042 raw24042Labels permutation154 permutation2
    _ = mixedMoment B node1117 node1117Labels := by rfl

def raw24043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw24043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24043 raw24043Labels = mixedMoment B node1114 node1114Labels := by
  calc
    _ = mixedMoment B node1114 node1114Labels := by rfl

def raw24044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24044 raw24044Labels = mixedMoment B node1112 node1112Labels := by
  calc
    _ = mixedMoment B node1112 node1112Labels := by rfl

def raw24045 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw24045Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24045step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw24045step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24045 raw24045Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw24045 raw24045Labels = mixedMoment B raw24045step0 raw24045step0Labels := by
      have hz : ∀ j, raw24045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24045step0 = (fun i j => raw24045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24045step0 raw24045; decide +kernel
      have hl : raw24045step0Labels = raw24045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24045 raw24045Labels permutation434 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw24046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24046 raw24046Labels = mixedMoment B node625 node625Labels := by
  calc
    mixedMoment B raw24046 raw24046Labels = mixedMoment B raw24046step0 raw24046step0Labels := by
      have ha : raw24046step0 = (fun i j => raw24046 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24046step0 raw24046; decide +kernel
      have hl : raw24046step0Labels = raw24046Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24046 raw24046Labels permutation158 permutation2
    _ = mixedMoment B node625 node625Labels := by rfl

def raw24047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24047 raw24047Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw24047 raw24047Labels = mixedMoment B raw24047step0 raw24047step0Labels := by
      have hz : ∀ j, raw24047 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24047step0 = (fun i j => raw24047 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24047step0 raw24047; decide +kernel
      have hl : raw24047step0Labels = raw24047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24047 raw24047Labels permutation434 hz
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw24048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24048 raw24048Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw24048 raw24048Labels = mixedMoment B raw24048step0 raw24048step0Labels := by
      have ha : raw24048step0 = (fun i j => raw24048 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24048step0 raw24048; decide +kernel
      have hl : raw24048step0Labels = raw24048Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24048 raw24048Labels permutation166 permutation2
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw24049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24049 raw24049Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw24049 raw24049Labels = mixedMoment B raw24049step0 raw24049step0Labels := by
      have ha : raw24049step0 = (fun i j => raw24049 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24049step0 raw24049; decide +kernel
      have hl : raw24049step0Labels = raw24049Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24049 raw24049Labels permutation158 permutation2
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw24050 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw24050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24050 raw24050Labels = mixedMoment B node1601 node1601Labels := by
  calc
    mixedMoment B raw24050 raw24050Labels = mixedMoment B raw24050step0 raw24050step0Labels := by
      have ha : raw24050step0 = (fun i j => raw24050 (permutation191 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24050step0 raw24050; decide +kernel
      have hl : raw24050step0Labels = raw24050Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24050 raw24050Labels permutation191 permutation2
    mixedMoment B raw24050step0 raw24050step0Labels = mixedMoment B raw24050step1 raw24050step1Labels := by
      have ha : raw24050step1 = -raw24050step0 := by apply Matrix.ext; change ∀ i j, raw24050step1 i j = -(raw24050step0 i j); unfold raw24050step1 raw24050step0; decide +kernel
      have hl : raw24050step1Labels = raw24050step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1601 node1601Labels := by rfl

def raw24051 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw24051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24051 raw24051Labels = mixedMoment B node1598 node1598Labels := by
  calc
    mixedMoment B raw24051 raw24051Labels = mixedMoment B raw24051step0 raw24051step0Labels := by
      have ha : raw24051step0 = (fun i j => raw24051 (permutation189 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24051step0 raw24051; decide +kernel
      have hl : raw24051step0Labels = raw24051Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24051 raw24051Labels permutation189 permutation2
    mixedMoment B raw24051step0 raw24051step0Labels = mixedMoment B raw24051step1 raw24051step1Labels := by
      have ha : raw24051step1 = -raw24051step0 := by apply Matrix.ext; change ∀ i j, raw24051step1 i j = -(raw24051step0 i j); unfold raw24051step1 raw24051step0; decide +kernel
      have hl : raw24051step1Labels = raw24051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1598 node1598Labels := by rfl

def raw24052 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24052 raw24052Labels = mixedMoment B node1597 node1597Labels := by
  calc
    mixedMoment B raw24052 raw24052Labels = mixedMoment B raw24052step0 raw24052step0Labels := by
      have ha : raw24052step0 = (fun i j => raw24052 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24052step0 raw24052; decide +kernel
      have hl : raw24052step0Labels = raw24052Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24052 raw24052Labels permutation188 permutation2
    mixedMoment B raw24052step0 raw24052step0Labels = mixedMoment B raw24052step1 raw24052step1Labels := by
      have ha : raw24052step1 = -raw24052step0 := by apply Matrix.ext; change ∀ i j, raw24052step1 i j = -(raw24052step0 i j); unfold raw24052step1 raw24052step0; decide +kernel
      have hl : raw24052step1Labels = raw24052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1597 node1597Labels := by rfl

def raw24053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24053 raw24053Labels = mixedMoment B node1210 node1210Labels := by
  calc
    mixedMoment B raw24053 raw24053Labels = mixedMoment B raw24053step0 raw24053step0Labels := by
      have ha : raw24053step0 = (fun i j => raw24053 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24053step0 raw24053; decide +kernel
      have hl : raw24053step0Labels = raw24053Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24053 raw24053Labels permutation178 permutation2
    _ = mixedMoment B node1210 node1210Labels := by rfl

def raw24054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24054 raw24054Labels = mixedMoment B node2613 node2613Labels := by
  calc
    mixedMoment B raw24054 raw24054Labels = mixedMoment B raw24054step0 raw24054step0Labels := by
      have ha : raw24054step0 = (fun i j => raw24054 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24054step0 raw24054; decide +kernel
      have hl : raw24054step0Labels = raw24054Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24054 raw24054Labels permutation154 permutation2
    _ = mixedMoment B node2613 node2613Labels := by rfl

def raw24055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24055 raw24055Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw24055 raw24055Labels = mixedMoment B raw24055step0 raw24055step0Labels := by
      have ha : raw24055step0 = (fun i j => raw24055 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24055step0 raw24055; decide +kernel
      have hl : raw24055step0Labels = raw24055Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24055 raw24055Labels permutation178 permutation2
    _ = mixedMoment B node2477 node2477Labels := by rfl

def raw24056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24056 raw24056Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw24056 raw24056Labels = mixedMoment B raw24056step0 raw24056step0Labels := by
      have ha : raw24056step0 = (fun i j => raw24056 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24056step0 raw24056; decide +kernel
      have hl : raw24056step0Labels = raw24056Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24056 raw24056Labels permutation176 permutation2
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw24057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24057 raw24057Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw24057 raw24057Labels = mixedMoment B raw24057step0 raw24057step0Labels := by
      have ha : raw24057step0 = (fun i j => raw24057 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24057step0 raw24057; decide +kernel
      have hl : raw24057step0Labels = raw24057Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24057 raw24057Labels permutation188 permutation2
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw24058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw24058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24058 raw24058Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw24058 raw24058Labels = mixedMoment B raw24058step0 raw24058step0Labels := by
      have ha : raw24058step0 = (fun i j => raw24058 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24058step0 raw24058; decide +kernel
      have hl : raw24058step0Labels = raw24058Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24058 raw24058Labels permutation178 permutation2
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw24059 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw24059Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24059step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24059step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24059 raw24059Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw24059 raw24059Labels = mixedMoment B raw24059step0 raw24059step0Labels := by
      have ha : raw24059step0 = (fun i j => raw24059 (permutation188 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24059step0 raw24059; decide +kernel
      have hl : raw24059step0Labels = raw24059Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24059 raw24059Labels permutation188 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw24060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24060 raw24060Labels = mixedMoment B node1180 node1180Labels := by
  calc
    mixedMoment B raw24060 raw24060Labels = mixedMoment B raw24060step0 raw24060step0Labels := by
      have ha : raw24060step0 = (fun i j => raw24060 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24060step0 raw24060; decide +kernel
      have hl : raw24060step0Labels = raw24060Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24060 raw24060Labels permutation176 permutation2
    _ = mixedMoment B node1180 node1180Labels := by rfl

def raw24061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24061 raw24061Labels = mixedMoment B node2607 node2607Labels := by
  calc
    _ = mixedMoment B node2607 node2607Labels := by rfl

def raw24062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24062 raw24062Labels = mixedMoment B node2383 node2383Labels := by
  calc
    mixedMoment B raw24062 raw24062Labels = mixedMoment B raw24062step0 raw24062step0Labels := by
      have ha : raw24062step0 = (fun i j => raw24062 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24062step0 raw24062; decide +kernel
      have hl : raw24062step0Labels = raw24062Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24062 raw24062Labels permutation176 permutation2
    _ = mixedMoment B node2383 node2383Labels := by rfl

def raw24063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24063 raw24063Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw24063 raw24063Labels = mixedMoment B raw24063step0 raw24063step0Labels := by
      have ha : raw24063step0 = (fun i j => raw24063 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24063step0 raw24063; decide +kernel
      have hl : raw24063step0Labels = raw24063Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24063 raw24063Labels permutation176 permutation2
    _ = mixedMoment B node2662 node2662Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
