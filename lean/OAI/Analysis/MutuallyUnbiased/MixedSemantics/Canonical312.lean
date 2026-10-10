import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.ExtraNodes

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw39936Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw39936step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw39936step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw39936step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39936step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw39936step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39936 raw39936Labels = mixedMoment B node186 node186Labels := by
  calc
    mixedMoment B raw39936 raw39936Labels = mixedMoment B raw39936step0 raw39936step0Labels := by
      have hz : ∀ j, raw39936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39936step0 = (fun i j => raw39936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39936step0 raw39936; decide +kernel
      have hl : raw39936step0Labels = raw39936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39936 raw39936Labels permutation346 hz
    mixedMoment B raw39936step0 raw39936step0Labels = mixedMoment B raw39936step1 raw39936step1Labels := by
      have hz : ∀ j, raw39936step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39936step1 = (fun i j => raw39936step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39936step1 raw39936step0; decide +kernel
      have hl : raw39936step1Labels = raw39936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39936step0 raw39936step0Labels permutation56 hz
    mixedMoment B raw39936step1 raw39936step1Labels = mixedMoment B raw39936step2 raw39936step2Labels := by
      have ha : raw39936step2 = (fun i j => raw39936step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39936step2 raw39936step1; decide +kernel
      have hl : raw39936step2Labels = raw39936step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39936step1 raw39936step1Labels permutation15 permutation6
    mixedMoment B raw39936step2 raw39936step2Labels = mixedMoment B raw39936step3 raw39936step3Labels := by
      have ha : raw39936step3 = -raw39936step2 := by apply Matrix.ext; change ∀ i j, raw39936step3 i j = -(raw39936step2 i j); unfold raw39936step3 raw39936step2; decide +kernel
      have hl : raw39936step3Labels = raw39936step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node186 node186Labels := by rfl

def raw39937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw39937Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw39937step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39937step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39937 raw39937Labels = mixedMoment B node95 node95Labels := by
  calc
    mixedMoment B raw39937 raw39937Labels = mixedMoment B raw39937step0 raw39937step0Labels := by
      have hz : ∀ j, raw39937 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39937step0 = (fun i j => raw39937 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39937step0 raw39937; decide +kernel
      have hl : raw39937step0Labels = raw39937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39937 raw39937Labels permutation265 hz
    mixedMoment B raw39937step0 raw39937step0Labels = mixedMoment B raw39937step1 raw39937step1Labels := by
      have ha : raw39937step1 = (fun i j => raw39937step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39937step1 raw39937step0; decide +kernel
      have hl : raw39937step1Labels = raw39937step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39937step0 raw39937step0Labels permutation125 permutation6
    _ = mixedMoment B node95 node95Labels := by rfl

def raw39938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw39938Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw39938step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39938step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39938 raw39938Labels = mixedMoment B node339 node339Labels := by
  calc
    mixedMoment B raw39938 raw39938Labels = mixedMoment B raw39938step0 raw39938step0Labels := by
      have hz : ∀ j, raw39938 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39938step0 = (fun i j => raw39938 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39938step0 raw39938; decide +kernel
      have hl : raw39938step0Labels = raw39938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39938 raw39938Labels permutation265 hz
    mixedMoment B raw39938step0 raw39938step0Labels = mixedMoment B raw39938step1 raw39938step1Labels := by
      have ha : raw39938step1 = (fun i j => raw39938step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39938step1 raw39938step0; decide +kernel
      have hl : raw39938step1Labels = raw39938step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39938step0 raw39938step0Labels permutation125 permutation6
    _ = mixedMoment B node339 node339Labels := by rfl

def raw39939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw39939Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw39939step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39939step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39939 raw39939Labels = mixedMoment B node68 node68Labels := by
  calc
    mixedMoment B raw39939 raw39939Labels = mixedMoment B raw39939step0 raw39939step0Labels := by
      have hz : ∀ j, raw39939 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39939step0 = (fun i j => raw39939 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39939step0 raw39939; decide +kernel
      have hl : raw39939step0Labels = raw39939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39939 raw39939Labels permutation265 hz
    mixedMoment B raw39939step0 raw39939step0Labels = mixedMoment B raw39939step1 raw39939step1Labels := by
      have ha : raw39939step1 = (fun i j => raw39939step0 (permutation124 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39939step1 raw39939step0; decide +kernel
      have hl : raw39939step1Labels = raw39939step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39939step0 raw39939step0Labels permutation124 permutation6
    _ = mixedMoment B node68 node68Labels := by rfl

def raw39940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw39940Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw39940step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39940step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39940 raw39940Labels = mixedMoment B node275 node275Labels := by
  calc
    mixedMoment B raw39940 raw39940Labels = mixedMoment B raw39940step0 raw39940step0Labels := by
      have hz : ∀ j, raw39940 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39940step0 = (fun i j => raw39940 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39940step0 raw39940; decide +kernel
      have hl : raw39940step0Labels = raw39940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39940 raw39940Labels permutation265 hz
    mixedMoment B raw39940step0 raw39940step0Labels = mixedMoment B raw39940step1 raw39940step1Labels := by
      have ha : raw39940step1 = (fun i j => raw39940step0 (permutation124 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39940step1 raw39940step0; decide +kernel
      have hl : raw39940step1Labels = raw39940step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39940step0 raw39940step0Labels permutation124 permutation6
    _ = mixedMoment B node275 node275Labels := by rfl

def raw39941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw39941Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39941step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39941 raw39941Labels = mixedMoment B node65 node65Labels := by
  calc
    mixedMoment B raw39941 raw39941Labels = mixedMoment B raw39941step0 raw39941step0Labels := by
      have ha : raw39941step0 = (fun i j => raw39941 (permutation577 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39941step0 raw39941; decide +kernel
      have hl : raw39941step0Labels = raw39941Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39941 raw39941Labels permutation577 permutation6
    _ = mixedMoment B node65 node65Labels := by rfl

def raw39942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39942Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39942step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39942step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw39942step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39942step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39942 raw39942Labels = mixedMoment B node406 node406Labels := by
  calc
    mixedMoment B raw39942 raw39942Labels = mixedMoment B raw39942step0 raw39942step0Labels := by
      have hz : ∀ j, raw39942 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39942step0 = (fun i j => raw39942 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39942step0 raw39942; decide +kernel
      have hl : raw39942step0Labels = raw39942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39942 raw39942Labels permutation434 hz
    mixedMoment B raw39942step0 raw39942step0Labels = mixedMoment B raw39942step1 raw39942step1Labels := by
      have hz : ∀ j, raw39942step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39942step1 = (fun i j => raw39942step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39942step1 raw39942step0; decide +kernel
      have hl : raw39942step1Labels = raw39942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39942step0 raw39942step0Labels permutation80 hz
    mixedMoment B raw39942step1 raw39942step1Labels = mixedMoment B raw39942step2 raw39942step2Labels := by
      have ha : raw39942step2 = (fun i j => raw39942step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39942step2 raw39942step1; decide +kernel
      have hl : raw39942step2Labels = raw39942step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39942step1 raw39942step1Labels permutation11 permutation7
    mixedMoment B raw39942step2 raw39942step2Labels = mixedMoment B raw39942step3 raw39942step3Labels := by
      have ha : raw39942step3 = -raw39942step2 := by apply Matrix.ext; change ∀ i j, raw39942step3 i j = -(raw39942step2 i j); unfold raw39942step3 raw39942step2; decide +kernel
      have hl : raw39942step3Labels = raw39942step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node406 node406Labels := by rfl

def raw39943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39943Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39943step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39943step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw39943step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw39943step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39943 raw39943Labels = mixedMoment B node354 node354Labels := by
  calc
    mixedMoment B raw39943 raw39943Labels = mixedMoment B raw39943step0 raw39943step0Labels := by
      have hz : ∀ j, raw39943 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39943step0 = (fun i j => raw39943 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39943step0 raw39943; decide +kernel
      have hl : raw39943step0Labels = raw39943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39943 raw39943Labels permutation434 hz
    mixedMoment B raw39943step0 raw39943step0Labels = mixedMoment B raw39943step1 raw39943step1Labels := by
      have hz : ∀ j, raw39943step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39943step1 = (fun i j => raw39943step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39943step1 raw39943step0; decide +kernel
      have hl : raw39943step1Labels = raw39943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39943step0 raw39943step0Labels permutation80 hz
    mixedMoment B raw39943step1 raw39943step1Labels = mixedMoment B raw39943step2 raw39943step2Labels := by
      have ha : raw39943step2 = (fun i j => raw39943step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39943step2 raw39943step1; decide +kernel
      have hl : raw39943step2Labels = raw39943step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39943step1 raw39943step1Labels permutation10 permutation7
    mixedMoment B raw39943step2 raw39943step2Labels = mixedMoment B raw39943step3 raw39943step3Labels := by
      have ha : raw39943step3 = -raw39943step2 := by apply Matrix.ext; change ∀ i j, raw39943step3 i j = -(raw39943step2 i j); unfold raw39943step3 raw39943step2; decide +kernel
      have hl : raw39943step3Labels = raw39943step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node354 node354Labels := by rfl

def raw39944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39944Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39944step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw39944step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw39944step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39944 raw39944Labels = mixedMoment B node328 node328Labels := by
  calc
    mixedMoment B raw39944 raw39944Labels = mixedMoment B raw39944step0 raw39944step0Labels := by
      have hz : ∀ j, raw39944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39944step0 = (fun i j => raw39944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39944step0 raw39944; decide +kernel
      have hl : raw39944step0Labels = raw39944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39944 raw39944Labels permutation346 hz
    mixedMoment B raw39944step0 raw39944step0Labels = mixedMoment B raw39944step1 raw39944step1Labels := by
      have ha : raw39944step1 = (fun i j => raw39944step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39944step1 raw39944step0; decide +kernel
      have hl : raw39944step1Labels = raw39944step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39944step0 raw39944step0Labels permutation40 permutation7
    mixedMoment B raw39944step1 raw39944step1Labels = mixedMoment B raw39944step2 raw39944step2Labels := by
      have ha : raw39944step2 = -raw39944step1 := by apply Matrix.ext; change ∀ i j, raw39944step2 i j = -(raw39944step1 i j); unfold raw39944step2 raw39944step1; decide +kernel
      have hl : raw39944step2Labels = raw39944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node328 node328Labels := by rfl

def raw39945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39945Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39945step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw39945step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39945step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39945 raw39945Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39945 raw39945Labels = mixedMoment B raw39945step0 raw39945step0Labels := by
      have hz : ∀ j, raw39945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39945step0 = (fun i j => raw39945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39945step0 raw39945; decide +kernel
      have hl : raw39945step0Labels = raw39945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39945 raw39945Labels permutation434 hz
    mixedMoment B raw39945step0 raw39945step0Labels = mixedMoment B raw39945step1 raw39945step1Labels := by
      have ha : raw39945step1 = (fun i j => raw39945step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39945step1 raw39945step0; decide +kernel
      have hl : raw39945step1Labels = raw39945step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39945step0 raw39945step0Labels permutation50 permutation7
    mixedMoment B raw39945step1 raw39945step1Labels = mixedMoment B raw39945step2 raw39945step2Labels := by
      have ha : raw39945step2 = -raw39945step1 := by apply Matrix.ext; change ∀ i j, raw39945step2 i j = -(raw39945step1 i j); unfold raw39945step2 raw39945step1; decide +kernel
      have hl : raw39945step2Labels = raw39945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node409 node409Labels := by rfl

def raw39946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39946Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39946step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39946step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39946step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39946 raw39946Labels = mixedMoment B node348 node348Labels := by
  calc
    mixedMoment B raw39946 raw39946Labels = mixedMoment B raw39946step0 raw39946step0Labels := by
      have hz : ∀ j, raw39946 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39946step0 = (fun i j => raw39946 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39946step0 raw39946; decide +kernel
      have hl : raw39946step0Labels = raw39946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39946 raw39946Labels permutation434 hz
    mixedMoment B raw39946step0 raw39946step0Labels = mixedMoment B raw39946step1 raw39946step1Labels := by
      have ha : raw39946step1 = (fun i j => raw39946step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39946step1 raw39946step0; decide +kernel
      have hl : raw39946step1Labels = raw39946step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39946step0 raw39946step0Labels permutation44 permutation7
    mixedMoment B raw39946step1 raw39946step1Labels = mixedMoment B raw39946step2 raw39946step2Labels := by
      have ha : raw39946step2 = -raw39946step1 := by apply Matrix.ext; change ∀ i j, raw39946step2 i j = -(raw39946step1 i j); unfold raw39946step2 raw39946step1; decide +kernel
      have hl : raw39946step2Labels = raw39946step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node348 node348Labels := by rfl

def raw39947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39947Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39947step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39947step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39947 raw39947Labels = mixedMoment B node347 node347Labels := by
  calc
    mixedMoment B raw39947 raw39947Labels = mixedMoment B raw39947step0 raw39947step0Labels := by
      have ha : raw39947step0 = (fun i j => raw39947 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39947step0 raw39947; decide +kernel
      have hl : raw39947step0Labels = raw39947Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39947 raw39947Labels permutation246 permutation7
    mixedMoment B raw39947step0 raw39947step0Labels = mixedMoment B raw39947step1 raw39947step1Labels := by
      have ha : raw39947step1 = -raw39947step0 := by apply Matrix.ext; change ∀ i j, raw39947step1 i j = -(raw39947step0 i j); unfold raw39947step1 raw39947step0; decide +kernel
      have hl : raw39947step1Labels = raw39947step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node347 node347Labels := by rfl

def raw39948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39948Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw39948step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39948step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39948 raw39948Labels = mixedMoment B node394 node394Labels := by
  calc
    mixedMoment B raw39948 raw39948Labels = mixedMoment B raw39948step0 raw39948step0Labels := by
      have ha : raw39948step0 = (fun i j => raw39948 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39948step0 raw39948; decide +kernel
      have hl : raw39948step0Labels = raw39948Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39948 raw39948Labels permutation240 permutation7
    mixedMoment B raw39948step0 raw39948step0Labels = mixedMoment B raw39948step1 raw39948step1Labels := by
      have ha : raw39948step1 = -raw39948step0 := by apply Matrix.ext; change ∀ i j, raw39948step1 i j = -(raw39948step0 i j); unfold raw39948step1 raw39948step0; decide +kernel
      have hl : raw39948step1Labels = raw39948step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node394 node394Labels := by rfl

def raw39949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39949Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39949step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39949step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw39949step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39949step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39949 raw39949Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39949 raw39949Labels = mixedMoment B raw39949step0 raw39949step0Labels := by
      have hz : ∀ j, raw39949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39949step0 = (fun i j => raw39949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39949step0 raw39949; decide +kernel
      have hl : raw39949step0Labels = raw39949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39949 raw39949Labels permutation434 hz
    mixedMoment B raw39949step0 raw39949step0Labels = mixedMoment B raw39949step1 raw39949step1Labels := by
      have hz : ∀ j, raw39949step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39949step1 = (fun i j => raw39949step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39949step1 raw39949step0; decide +kernel
      have hl : raw39949step1Labels = raw39949step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39949step0 raw39949step0Labels permutation80 hz
    mixedMoment B raw39949step1 raw39949step1Labels = mixedMoment B raw39949step2 raw39949step2Labels := by
      have ha : raw39949step2 = (fun i j => raw39949step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39949step2 raw39949step1; decide +kernel
      have hl : raw39949step2Labels = raw39949step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39949step1 raw39949step1Labels permutation12 permutation7
    mixedMoment B raw39949step2 raw39949step2Labels = mixedMoment B raw39949step3 raw39949step3Labels := by
      have ha : raw39949step3 = -raw39949step2 := by apply Matrix.ext; change ∀ i j, raw39949step3 i j = -(raw39949step2 i j); unfold raw39949step3 raw39949step2; decide +kernel
      have hl : raw39949step3Labels = raw39949step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node410 node410Labels := by rfl

def raw39950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39950Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39950step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39950step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw39950step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39950step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39950 raw39950Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw39950 raw39950Labels = mixedMoment B raw39950step0 raw39950step0Labels := by
      have hz : ∀ j, raw39950 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39950step0 = (fun i j => raw39950 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39950step0 raw39950; decide +kernel
      have hl : raw39950step0Labels = raw39950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39950 raw39950Labels permutation434 hz
    mixedMoment B raw39950step0 raw39950step0Labels = mixedMoment B raw39950step1 raw39950step1Labels := by
      have hz : ∀ j, raw39950step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39950step1 = (fun i j => raw39950step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39950step1 raw39950step0; decide +kernel
      have hl : raw39950step1Labels = raw39950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39950step0 raw39950step0Labels permutation80 hz
    mixedMoment B raw39950step1 raw39950step1Labels = mixedMoment B raw39950step2 raw39950step2Labels := by
      have ha : raw39950step2 = (fun i j => raw39950step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39950step2 raw39950step1; decide +kernel
      have hl : raw39950step2Labels = raw39950step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39950step1 raw39950step1Labels permutation10 permutation7
    mixedMoment B raw39950step2 raw39950step2Labels = mixedMoment B raw39950step3 raw39950step3Labels := by
      have ha : raw39950step3 = -raw39950step2 := by apply Matrix.ext; change ∀ i j, raw39950step3 i j = -(raw39950step2 i j); unfold raw39950step3 raw39950step2; decide +kernel
      have hl : raw39950step3Labels = raw39950step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node402 node402Labels := by rfl

def raw39951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39951Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39951step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw39951step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw39951step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39951 raw39951Labels = mixedMoment B node350 node350Labels := by
  calc
    mixedMoment B raw39951 raw39951Labels = mixedMoment B raw39951step0 raw39951step0Labels := by
      have hz : ∀ j, raw39951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39951step0 = (fun i j => raw39951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39951step0 raw39951; decide +kernel
      have hl : raw39951step0Labels = raw39951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39951 raw39951Labels permutation434 hz
    mixedMoment B raw39951step0 raw39951step0Labels = mixedMoment B raw39951step1 raw39951step1Labels := by
      have hz : ∀ j, raw39951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39951step1 = (fun i j => raw39951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39951step1 raw39951step0; decide +kernel
      have hl : raw39951step1Labels = raw39951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39951step0 raw39951step0Labels permutation80 hz
    mixedMoment B raw39951step1 raw39951step1Labels = mixedMoment B raw39951step2 raw39951step2Labels := by
      have ha : raw39951step2 = (fun i j => raw39951step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39951step2 raw39951step1; decide +kernel
      have hl : raw39951step2Labels = raw39951step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39951step1 raw39951step1Labels permutation29 permutation7
    _ = mixedMoment B node350 node350Labels := by rfl

def raw39952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39952Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39952step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39952step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw39952step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39952 raw39952Labels = mixedMoment B node349 node349Labels := by
  calc
    mixedMoment B raw39952 raw39952Labels = mixedMoment B raw39952step0 raw39952step0Labels := by
      have hz : ∀ j, raw39952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39952step0 = (fun i j => raw39952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39952step0 raw39952; decide +kernel
      have hl : raw39952step0Labels = raw39952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39952 raw39952Labels permutation346 hz
    mixedMoment B raw39952step0 raw39952step0Labels = mixedMoment B raw39952step1 raw39952step1Labels := by
      have ha : raw39952step1 = (fun i j => raw39952step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39952step1 raw39952step0; decide +kernel
      have hl : raw39952step1Labels = raw39952step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39952step0 raw39952step0Labels permutation51 permutation7
    mixedMoment B raw39952step1 raw39952step1Labels = mixedMoment B raw39952step2 raw39952step2Labels := by
      have ha : raw39952step2 = -raw39952step1 := by apply Matrix.ext; change ∀ i j, raw39952step2 i j = -(raw39952step1 i j); unfold raw39952step2 raw39952step1; decide +kernel
      have hl : raw39952step2Labels = raw39952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node349 node349Labels := by rfl

def raw39953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39953Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39953step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw39953step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39953step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39953 raw39953Labels = mixedMoment B node395 node395Labels := by
  calc
    mixedMoment B raw39953 raw39953Labels = mixedMoment B raw39953step0 raw39953step0Labels := by
      have hz : ∀ j, raw39953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39953step0 = (fun i j => raw39953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39953step0 raw39953; decide +kernel
      have hl : raw39953step0Labels = raw39953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39953 raw39953Labels permutation346 hz
    mixedMoment B raw39953step0 raw39953step0Labels = mixedMoment B raw39953step1 raw39953step1Labels := by
      have ha : raw39953step1 = (fun i j => raw39953step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39953step1 raw39953step0; decide +kernel
      have hl : raw39953step1Labels = raw39953step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39953step0 raw39953step0Labels permutation48 permutation7
    mixedMoment B raw39953step1 raw39953step1Labels = mixedMoment B raw39953step2 raw39953step2Labels := by
      have ha : raw39953step2 = -raw39953step1 := by apply Matrix.ext; change ∀ i j, raw39953step2 i j = -(raw39953step1 i j); unfold raw39953step2 raw39953step1; decide +kernel
      have hl : raw39953step2Labels = raw39953step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node395 node395Labels := by rfl

def raw39954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39954Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39954step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39954step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39954step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39954 raw39954Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39954 raw39954Labels = mixedMoment B raw39954step0 raw39954step0Labels := by
      have hz : ∀ j, raw39954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39954step0 = (fun i j => raw39954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39954step0 raw39954; decide +kernel
      have hl : raw39954step0Labels = raw39954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39954 raw39954Labels permutation434 hz
    mixedMoment B raw39954step0 raw39954step0Labels = mixedMoment B raw39954step1 raw39954step1Labels := by
      have ha : raw39954step1 = (fun i j => raw39954step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39954step1 raw39954step0; decide +kernel
      have hl : raw39954step1Labels = raw39954step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39954step0 raw39954step0Labels permutation37 permutation7
    mixedMoment B raw39954step1 raw39954step1Labels = mixedMoment B raw39954step2 raw39954step2Labels := by
      have ha : raw39954step2 = -raw39954step1 := by apply Matrix.ext; change ∀ i j, raw39954step2 i j = -(raw39954step1 i j); unfold raw39954step2 raw39954step1; decide +kernel
      have hl : raw39954step2Labels = raw39954step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node384 node384Labels := by rfl

def raw39955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39955Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39955step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39955step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw39955step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39955 raw39955Labels = mixedMoment B node346 node346Labels := by
  calc
    mixedMoment B raw39955 raw39955Labels = mixedMoment B raw39955step0 raw39955step0Labels := by
      have hz : ∀ j, raw39955 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39955step0 = (fun i j => raw39955 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39955step0 raw39955; decide +kernel
      have hl : raw39955step0Labels = raw39955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39955 raw39955Labels permutation434 hz
    mixedMoment B raw39955step0 raw39955step0Labels = mixedMoment B raw39955step1 raw39955step1Labels := by
      have ha : raw39955step1 = (fun i j => raw39955step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39955step1 raw39955step0; decide +kernel
      have hl : raw39955step1Labels = raw39955step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39955step0 raw39955step0Labels permutation44 permutation7
    mixedMoment B raw39955step1 raw39955step1Labels = mixedMoment B raw39955step2 raw39955step2Labels := by
      have ha : raw39955step2 = -raw39955step1 := by apply Matrix.ext; change ∀ i j, raw39955step2 i j = -(raw39955step1 i j); unfold raw39955step2 raw39955step1; decide +kernel
      have hl : raw39955step2Labels = raw39955step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node346 node346Labels := by rfl

def raw39956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39956Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39956step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39956step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39956 raw39956Labels = mixedMoment B node345 node345Labels := by
  calc
    mixedMoment B raw39956 raw39956Labels = mixedMoment B raw39956step0 raw39956step0Labels := by
      have ha : raw39956step0 = (fun i j => raw39956 (permutation249 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39956step0 raw39956; decide +kernel
      have hl : raw39956step0Labels = raw39956Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39956 raw39956Labels permutation249 permutation7
    mixedMoment B raw39956step0 raw39956step0Labels = mixedMoment B raw39956step1 raw39956step1Labels := by
      have ha : raw39956step1 = -raw39956step0 := by apply Matrix.ext; change ∀ i j, raw39956step1 i j = -(raw39956step0 i j); unfold raw39956step1 raw39956step0; decide +kernel
      have hl : raw39956step1Labels = raw39956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node345 node345Labels := by rfl

def raw39957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39957Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39957step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39957step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39957 raw39957Labels = mixedMoment B node373 node373Labels := by
  calc
    mixedMoment B raw39957 raw39957Labels = mixedMoment B raw39957step0 raw39957step0Labels := by
      have ha : raw39957step0 = (fun i j => raw39957 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39957step0 raw39957; decide +kernel
      have hl : raw39957step0Labels = raw39957Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39957 raw39957Labels permutation169 permutation7
    mixedMoment B raw39957step0 raw39957step0Labels = mixedMoment B raw39957step1 raw39957step1Labels := by
      have ha : raw39957step1 = -raw39957step0 := by apply Matrix.ext; change ∀ i j, raw39957step1 i j = -(raw39957step0 i j); unfold raw39957step1 raw39957step0; decide +kernel
      have hl : raw39957step1Labels = raw39957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node373 node373Labels := by rfl

def raw39958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39958Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39958step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39958step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39958step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39958 raw39958Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw39958 raw39958Labels = mixedMoment B raw39958step0 raw39958step0Labels := by
      have hz : ∀ j, raw39958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39958step0 = (fun i j => raw39958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39958step0 raw39958; decide +kernel
      have hl : raw39958step0Labels = raw39958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39958 raw39958Labels permutation434 hz
    mixedMoment B raw39958step0 raw39958step0Labels = mixedMoment B raw39958step1 raw39958step1Labels := by
      have ha : raw39958step1 = (fun i j => raw39958step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39958step1 raw39958step0; decide +kernel
      have hl : raw39958step1Labels = raw39958step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39958step0 raw39958step0Labels permutation34 permutation7
    mixedMoment B raw39958step1 raw39958step1Labels = mixedMoment B raw39958step2 raw39958step2Labels := by
      have ha : raw39958step2 = -raw39958step1 := by apply Matrix.ext; change ∀ i j, raw39958step2 i j = -(raw39958step1 i j); unfold raw39958step2 raw39958step1; decide +kernel
      have hl : raw39958step2Labels = raw39958step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node377 node377Labels := by rfl

def raw39959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39959Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39959step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39959step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw39959step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39959 raw39959Labels = mixedMoment B node385 node385Labels := by
  calc
    mixedMoment B raw39959 raw39959Labels = mixedMoment B raw39959step0 raw39959step0Labels := by
      have hz : ∀ j, raw39959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39959step0 = (fun i j => raw39959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39959step0 raw39959; decide +kernel
      have hl : raw39959step0Labels = raw39959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39959 raw39959Labels permutation434 hz
    mixedMoment B raw39959step0 raw39959step0Labels = mixedMoment B raw39959step1 raw39959step1Labels := by
      have hz : ∀ j, raw39959step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39959step1 = (fun i j => raw39959step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39959step1 raw39959step0; decide +kernel
      have hl : raw39959step1Labels = raw39959step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39959step0 raw39959step0Labels permutation80 hz
    mixedMoment B raw39959step1 raw39959step1Labels = mixedMoment B raw39959step2 raw39959step2Labels := by
      have ha : raw39959step2 = (fun i j => raw39959step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39959step2 raw39959step1; decide +kernel
      have hl : raw39959step2Labels = raw39959step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39959step1 raw39959step1Labels permutation23 permutation6
    _ = mixedMoment B node385 node385Labels := by rfl

def raw39960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39960Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39960step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39960step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw39960step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39960 raw39960Labels = mixedMoment B node379 node379Labels := by
  calc
    mixedMoment B raw39960 raw39960Labels = mixedMoment B raw39960step0 raw39960step0Labels := by
      have hz : ∀ j, raw39960 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39960step0 = (fun i j => raw39960 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39960step0 raw39960; decide +kernel
      have hl : raw39960step0Labels = raw39960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39960 raw39960Labels permutation434 hz
    mixedMoment B raw39960step0 raw39960step0Labels = mixedMoment B raw39960step1 raw39960step1Labels := by
      have hz : ∀ j, raw39960step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39960step1 = (fun i j => raw39960step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39960step1 raw39960step0; decide +kernel
      have hl : raw39960step1Labels = raw39960step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39960step0 raw39960step0Labels permutation80 hz
    mixedMoment B raw39960step1 raw39960step1Labels = mixedMoment B raw39960step2 raw39960step2Labels := by
      have ha : raw39960step2 = (fun i j => raw39960step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39960step2 raw39960step1; decide +kernel
      have hl : raw39960step2Labels = raw39960step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39960step1 raw39960step1Labels permutation31 permutation7
    _ = mixedMoment B node379 node379Labels := by rfl

def raw39961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39961Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39961step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39961step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw39961step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39961 raw39961Labels = mixedMoment B node147 node147Labels := by
  calc
    mixedMoment B raw39961 raw39961Labels = mixedMoment B raw39961step0 raw39961step0Labels := by
      have hz : ∀ j, raw39961 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39961step0 = (fun i j => raw39961 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39961step0 raw39961; decide +kernel
      have hl : raw39961step0Labels = raw39961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39961 raw39961Labels permutation434 hz
    mixedMoment B raw39961step0 raw39961step0Labels = mixedMoment B raw39961step1 raw39961step1Labels := by
      have hz : ∀ j, raw39961step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39961step1 = (fun i j => raw39961step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39961step1 raw39961step0; decide +kernel
      have hl : raw39961step1Labels = raw39961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39961step0 raw39961step0Labels permutation80 hz
    mixedMoment B raw39961step1 raw39961step1Labels = mixedMoment B raw39961step2 raw39961step2Labels := by
      have ha : raw39961step2 = (fun i j => raw39961step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39961step2 raw39961step1; decide +kernel
      have hl : raw39961step2Labels = raw39961step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39961step1 raw39961step1Labels permutation29 permutation6
    _ = mixedMoment B node147 node147Labels := by rfl

def raw39962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39962Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39962step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw39962step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39962 raw39962Labels = mixedMoment B node323 node323Labels := by
  calc
    mixedMoment B raw39962 raw39962Labels = mixedMoment B raw39962step0 raw39962step0Labels := by
      have hz : ∀ j, raw39962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39962step0 = (fun i j => raw39962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39962step0 raw39962; decide +kernel
      have hl : raw39962step0Labels = raw39962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39962 raw39962Labels permutation346 hz
    mixedMoment B raw39962step0 raw39962step0Labels = mixedMoment B raw39962step1 raw39962step1Labels := by
      have ha : raw39962step1 = (fun i j => raw39962step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39962step1 raw39962step0; decide +kernel
      have hl : raw39962step1Labels = raw39962step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39962step0 raw39962step0Labels permutation95 permutation6
    _ = mixedMoment B node323 node323Labels := by rfl

def raw39963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39963Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39963step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw39963step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39963 raw39963Labels = mixedMoment B node374 node374Labels := by
  calc
    mixedMoment B raw39963 raw39963Labels = mixedMoment B raw39963step0 raw39963step0Labels := by
      have hz : ∀ j, raw39963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39963step0 = (fun i j => raw39963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39963step0 raw39963; decide +kernel
      have hl : raw39963step0Labels = raw39963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39963 raw39963Labels permutation346 hz
    mixedMoment B raw39963step0 raw39963step0Labels = mixedMoment B raw39963step1 raw39963step1Labels := by
      have ha : raw39963step1 = (fun i j => raw39963step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39963step1 raw39963step0; decide +kernel
      have hl : raw39963step1Labels = raw39963step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39963step0 raw39963step0Labels permutation89 permutation6
    _ = mixedMoment B node374 node374Labels := by rfl

def raw39964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39964Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw39964step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39964step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39964 raw39964Labels = mixedMoment B node5503 node5503Labels := by
  calc
    mixedMoment B raw39964 raw39964Labels = mixedMoment B raw39964step0 raw39964step0Labels := by
      have hz : ∀ j, raw39964 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39964step0 = (fun i j => raw39964 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39964step0 raw39964; decide +kernel
      have hl : raw39964step0Labels = raw39964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39964 raw39964Labels permutation434 hz
    mixedMoment B raw39964step0 raw39964step0Labels = mixedMoment B raw39964step1 raw39964step1Labels := by
      have ha : raw39964step1 = (fun i j => raw39964step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39964step1 raw39964step0; decide +kernel
      have hl : raw39964step1Labels = raw39964step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39964step0 raw39964step0Labels permutation97 permutation6
    _ = mixedMoment B node5503 node5503Labels := by rfl

def raw39965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39965Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw39965step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw39965step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39965 raw39965Labels = mixedMoment B node239 node239Labels := by
  calc
    mixedMoment B raw39965 raw39965Labels = mixedMoment B raw39965step0 raw39965step0Labels := by
      have hz : ∀ j, raw39965 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39965step0 = (fun i j => raw39965 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39965step0 raw39965; decide +kernel
      have hl : raw39965step0Labels = raw39965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39965 raw39965Labels permutation434 hz
    mixedMoment B raw39965step0 raw39965step0Labels = mixedMoment B raw39965step1 raw39965step1Labels := by
      have ha : raw39965step1 = (fun i j => raw39965step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39965step1 raw39965step0; decide +kernel
      have hl : raw39965step1Labels = raw39965step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39965step0 raw39965step0Labels permutation103 permutation6
    _ = mixedMoment B node239 node239Labels := by rfl

def raw39966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39966Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw39966step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw39966step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39966 raw39966Labels = mixedMoment B node176 node176Labels := by
  calc
    mixedMoment B raw39966 raw39966Labels = mixedMoment B raw39966step0 raw39966step0Labels := by
      have hz : ∀ j, raw39966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39966step0 = (fun i j => raw39966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39966step0 raw39966; decide +kernel
      have hl : raw39966step0Labels = raw39966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39966 raw39966Labels permutation434 hz
    mixedMoment B raw39966step0 raw39966step0Labels = mixedMoment B raw39966step1 raw39966step1Labels := by
      have ha : raw39966step1 = (fun i j => raw39966step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39966step1 raw39966step0; decide +kernel
      have hl : raw39966step1Labels = raw39966step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39966step0 raw39966step0Labels permutation101 permutation6
    _ = mixedMoment B node176 node176Labels := by rfl

def raw39967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39967Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39967step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39967 raw39967Labels = mixedMoment B node164 node164Labels := by
  calc
    mixedMoment B raw39967 raw39967Labels = mixedMoment B raw39967step0 raw39967step0Labels := by
      have ha : raw39967step0 = (fun i j => raw39967 (permutation431 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39967step0 raw39967; decide +kernel
      have hl : raw39967step0Labels = raw39967Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39967 raw39967Labels permutation431 permutation6
    _ = mixedMoment B node164 node164Labels := by rfl

def raw39968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39968Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw39968step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39968step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39968 raw39968Labels = mixedMoment B node5508 node5508Labels := by
  calc
    mixedMoment B raw39968 raw39968Labels = mixedMoment B raw39968step0 raw39968step0Labels := by
      have ha : raw39968step0 = (fun i j => raw39968 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39968step0 raw39968; decide +kernel
      have hl : raw39968step0Labels = raw39968Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39968 raw39968Labels permutation173 permutation7
    mixedMoment B raw39968step0 raw39968step0Labels = mixedMoment B raw39968step1 raw39968step1Labels := by
      have ha : raw39968step1 = -raw39968step0 := by apply Matrix.ext; change ∀ i j, raw39968step1 i j = -(raw39968step0 i j); unfold raw39968step1 raw39968step0; decide +kernel
      have hl : raw39968step1Labels = raw39968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5508 node5508Labels := by rfl

def raw39969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39969Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39969step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39969step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39969 raw39969Labels = mixedMoment B node297 node297Labels := by
  calc
    mixedMoment B raw39969 raw39969Labels = mixedMoment B raw39969step0 raw39969step0Labels := by
      have ha : raw39969step0 = (fun i j => raw39969 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39969step0 raw39969; decide +kernel
      have hl : raw39969step0Labels = raw39969Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39969 raw39969Labels permutation166 permutation7
    mixedMoment B raw39969step0 raw39969step0Labels = mixedMoment B raw39969step1 raw39969step1Labels := by
      have ha : raw39969step1 = -raw39969step0 := by apply Matrix.ext; change ∀ i j, raw39969step1 i j = -(raw39969step0 i j); unfold raw39969step1 raw39969step0; decide +kernel
      have hl : raw39969step1Labels = raw39969step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node297 node297Labels := by rfl

def raw39970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39970Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw39970step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw39970step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39970step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39970 raw39970Labels = mixedMoment B node309 node309Labels := by
  calc
    mixedMoment B raw39970 raw39970Labels = mixedMoment B raw39970step0 raw39970step0Labels := by
      have hz : ∀ j, raw39970 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39970step0 = (fun i j => raw39970 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39970step0 raw39970; decide +kernel
      have hl : raw39970step0Labels = raw39970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39970 raw39970Labels permutation434 hz
    mixedMoment B raw39970step0 raw39970step0Labels = mixedMoment B raw39970step1 raw39970step1Labels := by
      have ha : raw39970step1 = (fun i j => raw39970step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39970step1 raw39970step0; decide +kernel
      have hl : raw39970step1Labels = raw39970step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39970step0 raw39970step0Labels permutation36 permutation7
    mixedMoment B raw39970step1 raw39970step1Labels = mixedMoment B raw39970step2 raw39970step2Labels := by
      have ha : raw39970step2 = -raw39970step1 := by apply Matrix.ext; change ∀ i j, raw39970step2 i j = -(raw39970step1 i j); unfold raw39970step2 raw39970step1; decide +kernel
      have hl : raw39970step2Labels = raw39970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node309 node309Labels := by rfl

def raw39971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39971Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39971step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39971step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39971step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39971 raw39971Labels = mixedMoment B node306 node306Labels := by
  calc
    mixedMoment B raw39971 raw39971Labels = mixedMoment B raw39971step0 raw39971step0Labels := by
      have hz : ∀ j, raw39971 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39971step0 = (fun i j => raw39971 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39971step0 raw39971; decide +kernel
      have hl : raw39971step0Labels = raw39971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39971 raw39971Labels permutation434 hz
    mixedMoment B raw39971step0 raw39971step0Labels = mixedMoment B raw39971step1 raw39971step1Labels := by
      have ha : raw39971step1 = (fun i j => raw39971step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39971step1 raw39971step0; decide +kernel
      have hl : raw39971step1Labels = raw39971step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39971step0 raw39971step0Labels permutation34 permutation7
    mixedMoment B raw39971step1 raw39971step1Labels = mixedMoment B raw39971step2 raw39971step2Labels := by
      have ha : raw39971step2 = -raw39971step1 := by apply Matrix.ext; change ∀ i j, raw39971step2 i j = -(raw39971step1 i j); unfold raw39971step2 raw39971step1; decide +kernel
      have hl : raw39971step2Labels = raw39971step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node306 node306Labels := by rfl

def raw39972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39972Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw39972step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw39972step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39972 raw39972Labels = mixedMoment B node281 node281Labels := by
  calc
    mixedMoment B raw39972 raw39972Labels = mixedMoment B raw39972step0 raw39972step0Labels := by
      have hz : ∀ j, raw39972 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39972step0 = (fun i j => raw39972 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39972step0 raw39972; decide +kernel
      have hl : raw39972step0Labels = raw39972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39972 raw39972Labels permutation434 hz
    mixedMoment B raw39972step0 raw39972step0Labels = mixedMoment B raw39972step1 raw39972step1Labels := by
      have ha : raw39972step1 = (fun i j => raw39972step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39972step1 raw39972step0; decide +kernel
      have hl : raw39972step1Labels = raw39972step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39972step0 raw39972step0Labels permutation145 permutation7
    _ = mixedMoment B node281 node281Labels := by rfl

def raw39973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39973Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39973step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39973step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39973step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39973 raw39973Labels = mixedMoment B node298 node298Labels := by
  calc
    mixedMoment B raw39973 raw39973Labels = mixedMoment B raw39973step0 raw39973step0Labels := by
      have ha : raw39973step0 = (fun i j => raw39973 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39973step0 raw39973; decide +kernel
      have hl : raw39973step0Labels = raw39973Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39973 raw39973Labels permutation174 permutation7
    mixedMoment B raw39973step0 raw39973step0Labels = mixedMoment B raw39973step1 raw39973step1Labels := by
      have ha : raw39973step1 = -raw39973step0 := by apply Matrix.ext; change ∀ i j, raw39973step1 i j = -(raw39973step0 i j); unfold raw39973step1 raw39973step0; decide +kernel
      have hl : raw39973step1Labels = raw39973step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node298 node298Labels := by rfl

def raw39974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39974Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39974step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39974step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39974 raw39974Labels = mixedMoment B node300 node300Labels := by
  calc
    mixedMoment B raw39974 raw39974Labels = mixedMoment B raw39974step0 raw39974step0Labels := by
      have ha : raw39974step0 = (fun i j => raw39974 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39974step0 raw39974; decide +kernel
      have hl : raw39974step0Labels = raw39974Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39974 raw39974Labels permutation168 permutation7
    mixedMoment B raw39974step0 raw39974step0Labels = mixedMoment B raw39974step1 raw39974step1Labels := by
      have ha : raw39974step1 = -raw39974step0 := by apply Matrix.ext; change ∀ i j, raw39974step1 i j = -(raw39974step0 i j); unfold raw39974step1 raw39974step0; decide +kernel
      have hl : raw39974step1Labels = raw39974step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node300 node300Labels := by rfl

def raw39975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39975Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39975step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39975step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39975 raw39975Labels = mixedMoment B node301 node301Labels := by
  calc
    mixedMoment B raw39975 raw39975Labels = mixedMoment B raw39975step0 raw39975step0Labels := by
      have ha : raw39975step0 = (fun i j => raw39975 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39975step0 raw39975; decide +kernel
      have hl : raw39975step0Labels = raw39975Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39975 raw39975Labels permutation164 permutation7
    mixedMoment B raw39975step0 raw39975step0Labels = mixedMoment B raw39975step1 raw39975step1Labels := by
      have ha : raw39975step1 = -raw39975step0 := by apply Matrix.ext; change ∀ i j, raw39975step1 i j = -(raw39975step0 i j); unfold raw39975step1 raw39975step0; decide +kernel
      have hl : raw39975step1Labels = raw39975step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node301 node301Labels := by rfl

def raw39976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39976Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw39976step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39976step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39976 raw39976Labels = mixedMoment B node308 node308Labels := by
  calc
    mixedMoment B raw39976 raw39976Labels = mixedMoment B raw39976step0 raw39976step0Labels := by
      have hz : ∀ j, raw39976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39976step0 = (fun i j => raw39976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39976step0 raw39976; decide +kernel
      have hl : raw39976step0Labels = raw39976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39976 raw39976Labels permutation434 hz
    mixedMoment B raw39976step0 raw39976step0Labels = mixedMoment B raw39976step1 raw39976step1Labels := by
      have ha : raw39976step1 = (fun i j => raw39976step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39976step1 raw39976step0; decide +kernel
      have hl : raw39976step1Labels = raw39976step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39976step0 raw39976step0Labels permutation121 permutation6
    _ = mixedMoment B node308 node308Labels := by rfl

def raw39977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39977Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw39977step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw39977step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw39977step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39977 raw39977Labels = mixedMoment B node303 node303Labels := by
  calc
    mixedMoment B raw39977 raw39977Labels = mixedMoment B raw39977step0 raw39977step0Labels := by
      have hz : ∀ j, raw39977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39977step0 = (fun i j => raw39977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39977step0 raw39977; decide +kernel
      have hl : raw39977step0Labels = raw39977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39977 raw39977Labels permutation434 hz
    mixedMoment B raw39977step0 raw39977step0Labels = mixedMoment B raw39977step1 raw39977step1Labels := by
      have ha : raw39977step1 = (fun i j => raw39977step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39977step1 raw39977step0; decide +kernel
      have hl : raw39977step1Labels = raw39977step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39977step0 raw39977step0Labels permutation34 permutation7
    mixedMoment B raw39977step1 raw39977step1Labels = mixedMoment B raw39977step2 raw39977step2Labels := by
      have ha : raw39977step2 = -raw39977step1 := by apply Matrix.ext; change ∀ i j, raw39977step2 i j = -(raw39977step1 i j); unfold raw39977step2 raw39977step1; decide +kernel
      have hl : raw39977step2Labels = raw39977step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node303 node303Labels := by rfl

def raw39978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39978Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw39978step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw39978step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39978 raw39978Labels = mixedMoment B node122 node122Labels := by
  calc
    mixedMoment B raw39978 raw39978Labels = mixedMoment B raw39978step0 raw39978step0Labels := by
      have hz : ∀ j, raw39978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39978step0 = (fun i j => raw39978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39978step0 raw39978; decide +kernel
      have hl : raw39978step0Labels = raw39978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39978 raw39978Labels permutation434 hz
    mixedMoment B raw39978step0 raw39978step0Labels = mixedMoment B raw39978step1 raw39978step1Labels := by
      have ha : raw39978step1 = (fun i j => raw39978step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39978step1 raw39978step0; decide +kernel
      have hl : raw39978step1Labels = raw39978step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39978step0 raw39978step0Labels permutation143 permutation6
    _ = mixedMoment B node122 node122Labels := by rfl

def raw39979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39979Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw39979step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39979 raw39979Labels = mixedMoment B node292 node292Labels := by
  calc
    mixedMoment B raw39979 raw39979Labels = mixedMoment B raw39979step0 raw39979step0Labels := by
      have ha : raw39979step0 = (fun i j => raw39979 (permutation478 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39979step0 raw39979; decide +kernel
      have hl : raw39979step0Labels = raw39979Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39979 raw39979Labels permutation478 permutation6
    _ = mixedMoment B node292 node292Labels := by rfl

def raw39980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39980Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw39980step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39980 raw39980Labels = mixedMoment B node299 node299Labels := by
  calc
    mixedMoment B raw39980 raw39980Labels = mixedMoment B raw39980step0 raw39980step0Labels := by
      have ha : raw39980step0 = (fun i j => raw39980 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39980step0 raw39980; decide +kernel
      have hl : raw39980step0Labels = raw39980Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39980 raw39980Labels permutation480 permutation6
    _ = mixedMoment B node299 node299Labels := by rfl

def raw39981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39981Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39981step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39981step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39981step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39981 raw39981Labels = mixedMoment B node5504 node5504Labels := by
  calc
    mixedMoment B raw39981 raw39981Labels = mixedMoment B raw39981step0 raw39981step0Labels := by
      have hz : ∀ j, raw39981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39981step0 = (fun i j => raw39981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39981step0 raw39981; decide +kernel
      have hl : raw39981step0Labels = raw39981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39981 raw39981Labels permutation434 hz
    mixedMoment B raw39981step0 raw39981step0Labels = mixedMoment B raw39981step1 raw39981step1Labels := by
      have hz : ∀ j, raw39981step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39981step1 = (fun i j => raw39981step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39981step1 raw39981step0; decide +kernel
      have hl : raw39981step1Labels = raw39981step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39981step0 raw39981step0Labels permutation80 hz
    mixedMoment B raw39981step1 raw39981step1Labels = mixedMoment B raw39981step2 raw39981step2Labels := by
      have ha : raw39981step2 = (fun i j => raw39981step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39981step2 raw39981step1; decide +kernel
      have hl : raw39981step2Labels = raw39981step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39981step1 raw39981step1Labels permutation25 permutation6
    _ = mixedMoment B node5504 node5504Labels := by rfl

def raw39982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39982Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39982step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39982step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw39982step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39982 raw39982Labels = mixedMoment B node146 node146Labels := by
  calc
    mixedMoment B raw39982 raw39982Labels = mixedMoment B raw39982step0 raw39982step0Labels := by
      have hz : ∀ j, raw39982 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39982step0 = (fun i j => raw39982 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39982step0 raw39982; decide +kernel
      have hl : raw39982step0Labels = raw39982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39982 raw39982Labels permutation434 hz
    mixedMoment B raw39982step0 raw39982step0Labels = mixedMoment B raw39982step1 raw39982step1Labels := by
      have hz : ∀ j, raw39982step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39982step1 = (fun i j => raw39982step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39982step1 raw39982step0; decide +kernel
      have hl : raw39982step1Labels = raw39982step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39982step0 raw39982step0Labels permutation80 hz
    mixedMoment B raw39982step1 raw39982step1Labels = mixedMoment B raw39982step2 raw39982step2Labels := by
      have ha : raw39982step2 = (fun i j => raw39982step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39982step2 raw39982step1; decide +kernel
      have hl : raw39982step2Labels = raw39982step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39982step1 raw39982step1Labels permutation31 permutation7
    _ = mixedMoment B node146 node146Labels := by rfl

def raw39983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39983Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39983step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39983step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39983 raw39983Labels = mixedMoment B node11 node11Labels := by
  calc
    mixedMoment B raw39983 raw39983Labels = mixedMoment B raw39983step0 raw39983step0Labels := by
      have hz : ∀ j, raw39983 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39983step0 = (fun i j => raw39983 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39983step0 raw39983; decide +kernel
      have hl : raw39983step0Labels = raw39983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39983 raw39983Labels permutation346 hz
    mixedMoment B raw39983step0 raw39983step0Labels = mixedMoment B raw39983step1 raw39983step1Labels := by
      have ha : raw39983step1 = (fun i j => raw39983step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39983step1 raw39983step0; decide +kernel
      have hl : raw39983step1Labels = raw39983step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39983step0 raw39983step0Labels permutation149 permutation6
    _ = mixedMoment B node11 node11Labels := by rfl

def raw39984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39984Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw39984step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw39984step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39984 raw39984Labels = mixedMoment B node169 node169Labels := by
  calc
    mixedMoment B raw39984 raw39984Labels = mixedMoment B raw39984step0 raw39984step0Labels := by
      have hz : ∀ j, raw39984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39984step0 = (fun i j => raw39984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39984step0 raw39984; decide +kernel
      have hl : raw39984step0Labels = raw39984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39984 raw39984Labels permutation434 hz
    mixedMoment B raw39984step0 raw39984step0Labels = mixedMoment B raw39984step1 raw39984step1Labels := by
      have ha : raw39984step1 = (fun i j => raw39984step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39984step1 raw39984step0; decide +kernel
      have hl : raw39984step1Labels = raw39984step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39984step0 raw39984step0Labels permutation103 permutation6
    _ = mixedMoment B node169 node169Labels := by rfl

def raw39985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39985Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39985step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39985step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw39985step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39985 raw39985Labels = mixedMoment B node18 node18Labels := by
  calc
    mixedMoment B raw39985 raw39985Labels = mixedMoment B raw39985step0 raw39985step0Labels := by
      have hz : ∀ j, raw39985 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39985step0 = (fun i j => raw39985 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39985step0 raw39985; decide +kernel
      have hl : raw39985step0Labels = raw39985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39985 raw39985Labels permutation434 hz
    mixedMoment B raw39985step0 raw39985step0Labels = mixedMoment B raw39985step1 raw39985step1Labels := by
      have hz : ∀ j, raw39985step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39985step1 = (fun i j => raw39985step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39985step1 raw39985step0; decide +kernel
      have hl : raw39985step1Labels = raw39985step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39985step0 raw39985step0Labels permutation80 hz
    mixedMoment B raw39985step1 raw39985step1Labels = mixedMoment B raw39985step2 raw39985step2Labels := by
      have ha : raw39985step2 = (fun i j => raw39985step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39985step2 raw39985step1; decide +kernel
      have hl : raw39985step2Labels = raw39985step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39985step1 raw39985step1Labels permutation31 permutation6
    _ = mixedMoment B node18 node18Labels := by rfl

def raw39986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39986Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39986step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![2, -2, 0]]
def raw39986step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]
def raw39986step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39986step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39986 raw39986Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw39986 raw39986Labels = mixedMoment B raw39986step0 raw39986step0Labels := by
      have hz : ∀ j, raw39986 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39986step0 = (fun i j => raw39986 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39986step0 raw39986; decide +kernel
      have hl : raw39986step0Labels = raw39986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39986 raw39986Labels permutation520 hz
    mixedMoment B raw39986step0 raw39986step0Labels = mixedMoment B raw39986step1 raw39986step1Labels := by
      have hz : ∀ j, raw39986step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39986step1 = (fun i j => raw39986step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39986step1 raw39986step0; decide +kernel
      have hl : raw39986step1Labels = raw39986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39986step0 raw39986step0Labels permutation104 hz
    mixedMoment B raw39986step1 raw39986step1Labels = mixedMoment B raw39986step2 raw39986step2Labels := by
      have hz : ∀ j, raw39986step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39986step2 = (fun i j => raw39986step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39986step2 raw39986step1; decide +kernel
      have hl : raw39986step2Labels = raw39986step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39986step1 raw39986step1Labels permutation20 hz
    mixedMoment B raw39986step2 raw39986step2Labels = mixedMoment B raw39986step3 raw39986step3Labels := by
      have ha : raw39986step3 = (fun i j => raw39986step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39986step3 raw39986step2; decide +kernel
      have hl : raw39986step3Labels = raw39986step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39986step2 raw39986step2Labels permutation5 permutation6
    _ = mixedMoment B node270 node270Labels := by rfl

def raw39987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw39987Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw39987step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![2, -1, -1]]
def raw39987step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39987step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39987 raw39987Labels = mixedMoment B node249 node249Labels := by
  calc
    mixedMoment B raw39987 raw39987Labels = mixedMoment B raw39987step0 raw39987step0Labels := by
      have hz : ∀ j, raw39987 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39987step0 = (fun i j => raw39987 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39987step0 raw39987; decide +kernel
      have hl : raw39987step0Labels = raw39987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39987 raw39987Labels permutation434 hz
    mixedMoment B raw39987step0 raw39987step0Labels = mixedMoment B raw39987step1 raw39987step1Labels := by
      have hz : ∀ j, raw39987step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39987step1 = (fun i j => raw39987step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39987step1 raw39987step0; decide +kernel
      have hl : raw39987step1Labels = raw39987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39987step0 raw39987step0Labels permutation80 hz
    mixedMoment B raw39987step1 raw39987step1Labels = mixedMoment B raw39987step2 raw39987step2Labels := by
      have ha : raw39987step2 = (fun i j => raw39987step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39987step2 raw39987step1; decide +kernel
      have hl : raw39987step2Labels = raw39987step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39987step1 raw39987step1Labels permutation19 permutation6
    _ = mixedMoment B node249 node249Labels := by rfl

def raw39988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39988Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39988step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -2, 2], ![2, 0, -2]]
def raw39988step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw39988step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39988 raw39988Labels = mixedMoment B node187 node187Labels := by
  calc
    mixedMoment B raw39988 raw39988Labels = mixedMoment B raw39988step0 raw39988step0Labels := by
      have hz : ∀ j, raw39988 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39988step0 = (fun i j => raw39988 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39988step0 raw39988; decide +kernel
      have hl : raw39988step0Labels = raw39988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39988 raw39988Labels permutation434 hz
    mixedMoment B raw39988step0 raw39988step0Labels = mixedMoment B raw39988step1 raw39988step1Labels := by
      have hz : ∀ j, raw39988step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39988step1 = (fun i j => raw39988step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39988step1 raw39988step0; decide +kernel
      have hl : raw39988step1Labels = raw39988step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39988step0 raw39988step0Labels permutation80 hz
    mixedMoment B raw39988step1 raw39988step1Labels = mixedMoment B raw39988step2 raw39988step2Labels := by
      have ha : raw39988step2 = (fun i j => raw39988step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39988step2 raw39988step1; decide +kernel
      have hl : raw39988step2Labels = raw39988step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39988step1 raw39988step1Labels permutation19 permutation6
    _ = mixedMoment B node187 node187Labels := by rfl

def raw39989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39989Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39989step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39989step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw39989step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39989 raw39989Labels = mixedMoment B node236 node236Labels := by
  calc
    mixedMoment B raw39989 raw39989Labels = mixedMoment B raw39989step0 raw39989step0Labels := by
      have hz : ∀ j, raw39989 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39989step0 = (fun i j => raw39989 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39989step0 raw39989; decide +kernel
      have hl : raw39989step0Labels = raw39989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39989 raw39989Labels permutation434 hz
    mixedMoment B raw39989step0 raw39989step0Labels = mixedMoment B raw39989step1 raw39989step1Labels := by
      have hz : ∀ j, raw39989step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39989step1 = (fun i j => raw39989step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39989step1 raw39989step0; decide +kernel
      have hl : raw39989step1Labels = raw39989step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39989step0 raw39989step0Labels permutation80 hz
    mixedMoment B raw39989step1 raw39989step1Labels = mixedMoment B raw39989step2 raw39989step2Labels := by
      have ha : raw39989step2 = (fun i j => raw39989step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39989step2 raw39989step1; decide +kernel
      have hl : raw39989step2Labels = raw39989step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39989step1 raw39989step1Labels permutation17 permutation6
    _ = mixedMoment B node236 node236Labels := by rfl

def raw39990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39990Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39990step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39990step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw39990step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39990 raw39990Labels = mixedMoment B node262 node262Labels := by
  calc
    mixedMoment B raw39990 raw39990Labels = mixedMoment B raw39990step0 raw39990step0Labels := by
      have hz : ∀ j, raw39990 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39990step0 = (fun i j => raw39990 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39990step0 raw39990; decide +kernel
      have hl : raw39990step0Labels = raw39990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39990 raw39990Labels permutation434 hz
    mixedMoment B raw39990step0 raw39990step0Labels = mixedMoment B raw39990step1 raw39990step1Labels := by
      have hz : ∀ j, raw39990step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39990step1 = (fun i j => raw39990step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39990step1 raw39990step0; decide +kernel
      have hl : raw39990step1Labels = raw39990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39990step0 raw39990step0Labels permutation80 hz
    mixedMoment B raw39990step1 raw39990step1Labels = mixedMoment B raw39990step2 raw39990step2Labels := by
      have ha : raw39990step2 = (fun i j => raw39990step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39990step2 raw39990step1; decide +kernel
      have hl : raw39990step2Labels = raw39990step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39990step1 raw39990step1Labels permutation17 permutation6
    _ = mixedMoment B node262 node262Labels := by rfl

def raw39991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39991Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39991step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39991step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39991 raw39991Labels = mixedMoment B node180 node180Labels := by
  calc
    mixedMoment B raw39991 raw39991Labels = mixedMoment B raw39991step0 raw39991step0Labels := by
      have hz : ∀ j, raw39991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39991step0 = (fun i j => raw39991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39991step0 raw39991; decide +kernel
      have hl : raw39991step0Labels = raw39991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39991 raw39991Labels permutation346 hz
    mixedMoment B raw39991step0 raw39991step0Labels = mixedMoment B raw39991step1 raw39991step1Labels := by
      have ha : raw39991step1 = (fun i j => raw39991step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39991step1 raw39991step0; decide +kernel
      have hl : raw39991step1Labels = raw39991step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39991step0 raw39991step0Labels permutation77 permutation6
    _ = mixedMoment B node180 node180Labels := by rfl

def raw39992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39992Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39992step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39992step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39992 raw39992Labels = mixedMoment B node224 node224Labels := by
  calc
    mixedMoment B raw39992 raw39992Labels = mixedMoment B raw39992step0 raw39992step0Labels := by
      have hz : ∀ j, raw39992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39992step0 = (fun i j => raw39992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39992step0 raw39992; decide +kernel
      have hl : raw39992step0Labels = raw39992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39992 raw39992Labels permutation346 hz
    mixedMoment B raw39992step0 raw39992step0Labels = mixedMoment B raw39992step1 raw39992step1Labels := by
      have ha : raw39992step1 = (fun i j => raw39992step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39992step1 raw39992step0; decide +kernel
      have hl : raw39992step1Labels = raw39992step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39992step0 raw39992step0Labels permutation73 permutation6
    _ = mixedMoment B node224 node224Labels := by rfl

def raw39993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39993Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39993step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw39993step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39993 raw39993Labels = mixedMoment B node211 node211Labels := by
  calc
    mixedMoment B raw39993 raw39993Labels = mixedMoment B raw39993step0 raw39993step0Labels := by
      have hz : ∀ j, raw39993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39993step0 = (fun i j => raw39993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39993step0 raw39993; decide +kernel
      have hl : raw39993step0Labels = raw39993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39993 raw39993Labels permutation346 hz
    mixedMoment B raw39993step0 raw39993step0Labels = mixedMoment B raw39993step1 raw39993step1Labels := by
      have ha : raw39993step1 = (fun i j => raw39993step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39993step1 raw39993step0; decide +kernel
      have hl : raw39993step1Labels = raw39993step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39993step0 raw39993step0Labels permutation73 permutation6
    _ = mixedMoment B node211 node211Labels := by rfl

def raw39994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39994Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39994step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39994 raw39994Labels = mixedMoment B node207 node207Labels := by
  calc
    mixedMoment B raw39994 raw39994Labels = mixedMoment B raw39994step0 raw39994step0Labels := by
      have ha : raw39994step0 = (fun i j => raw39994 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39994step0 raw39994; decide +kernel
      have hl : raw39994step0Labels = raw39994Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39994 raw39994Labels permutation332 permutation6
    _ = mixedMoment B node207 node207Labels := by rfl

def raw39995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39995Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw39995step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw39995step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw39995step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39995step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39995 raw39995Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39995 raw39995Labels = mixedMoment B raw39995step0 raw39995step0Labels := by
      have hz : ∀ j, raw39995 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39995step0 = (fun i j => raw39995 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39995step0 raw39995; decide +kernel
      have hl : raw39995step0Labels = raw39995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39995 raw39995Labels permutation520 hz
    mixedMoment B raw39995step0 raw39995step0Labels = mixedMoment B raw39995step1 raw39995step1Labels := by
      have hz : ∀ j, raw39995step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39995step1 = (fun i j => raw39995step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39995step1 raw39995step0; decide +kernel
      have hl : raw39995step1Labels = raw39995step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39995step0 raw39995step0Labels permutation104 hz
    mixedMoment B raw39995step1 raw39995step1Labels = mixedMoment B raw39995step2 raw39995step2Labels := by
      have ha : raw39995step2 = (fun i j => raw39995step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39995step2 raw39995step1; decide +kernel
      have hl : raw39995step2Labels = raw39995step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39995step1 raw39995step1Labels permutation13 permutation7
    mixedMoment B raw39995step2 raw39995step2Labels = mixedMoment B raw39995step3 raw39995step3Labels := by
      have ha : raw39995step3 = -raw39995step2 := by apply Matrix.ext; change ∀ i j, raw39995step3 i j = -(raw39995step2 i j); unfold raw39995step3 raw39995step2; decide +kernel
      have hl : raw39995step3Labels = raw39995step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node412 node412Labels := by rfl

def raw39996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39996Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw39996step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39996step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39996step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39996 raw39996Labels = mixedMoment B node286 node286Labels := by
  calc
    mixedMoment B raw39996 raw39996Labels = mixedMoment B raw39996step0 raw39996step0Labels := by
      have hz : ∀ j, raw39996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39996step0 = (fun i j => raw39996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39996step0 raw39996; decide +kernel
      have hl : raw39996step0Labels = raw39996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39996 raw39996Labels permutation434 hz
    mixedMoment B raw39996step0 raw39996step0Labels = mixedMoment B raw39996step1 raw39996step1Labels := by
      have ha : raw39996step1 = (fun i j => raw39996step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39996step1 raw39996step0; decide +kernel
      have hl : raw39996step1Labels = raw39996step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39996step0 raw39996step0Labels permutation46 permutation7
    mixedMoment B raw39996step1 raw39996step1Labels = mixedMoment B raw39996step2 raw39996step2Labels := by
      have ha : raw39996step2 = -raw39996step1 := by apply Matrix.ext; change ∀ i j, raw39996step2 i j = -(raw39996step1 i j); unfold raw39996step2 raw39996step1; decide +kernel
      have hl : raw39996step2Labels = raw39996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node286 node286Labels := by rfl

def raw39997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39997Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39997step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw39997step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39997step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39997 raw39997Labels = mixedMoment B node353 node353Labels := by
  calc
    mixedMoment B raw39997 raw39997Labels = mixedMoment B raw39997step0 raw39997step0Labels := by
      have hz : ∀ j, raw39997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39997step0 = (fun i j => raw39997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39997step0 raw39997; decide +kernel
      have hl : raw39997step0Labels = raw39997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39997 raw39997Labels permutation434 hz
    mixedMoment B raw39997step0 raw39997step0Labels = mixedMoment B raw39997step1 raw39997step1Labels := by
      have ha : raw39997step1 = (fun i j => raw39997step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39997step1 raw39997step0; decide +kernel
      have hl : raw39997step1Labels = raw39997step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39997step0 raw39997step0Labels permutation53 permutation7
    mixedMoment B raw39997step1 raw39997step1Labels = mixedMoment B raw39997step2 raw39997step2Labels := by
      have ha : raw39997step2 = -raw39997step1 := by apply Matrix.ext; change ∀ i j, raw39997step2 i j = -(raw39997step1 i j); unfold raw39997step2 raw39997step1; decide +kernel
      have hl : raw39997step2Labels = raw39997step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node353 node353Labels := by rfl

def raw39998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39998Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39998step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -2, 2], ![2, 1, -3]]
def raw39998step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw39998step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39998 raw39998Labels = mixedMoment B node290 node290Labels := by
  calc
    mixedMoment B raw39998 raw39998Labels = mixedMoment B raw39998step0 raw39998step0Labels := by
      have hz : ∀ j, raw39998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39998step0 = (fun i j => raw39998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39998step0 raw39998; decide +kernel
      have hl : raw39998step0Labels = raw39998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39998 raw39998Labels permutation434 hz
    mixedMoment B raw39998step0 raw39998step0Labels = mixedMoment B raw39998step1 raw39998step1Labels := by
      have hz : ∀ j, raw39998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39998step1 = (fun i j => raw39998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39998step1 raw39998step0; decide +kernel
      have hl : raw39998step1Labels = raw39998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39998step0 raw39998step0Labels permutation80 hz
    mixedMoment B raw39998step1 raw39998step1Labels = mixedMoment B raw39998step2 raw39998step2Labels := by
      have ha : raw39998step2 = (fun i j => raw39998step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39998step2 raw39998step1; decide +kernel
      have hl : raw39998step2Labels = raw39998step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39998step1 raw39998step1Labels permutation29 permutation7
    _ = mixedMoment B node290 node290Labels := by rfl

def raw39999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw39999Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw39999step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]
def raw39999step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39999step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39999step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39999 raw39999Labels = mixedMoment B node355 node355Labels := by
  calc
    mixedMoment B raw39999 raw39999Labels = mixedMoment B raw39999step0 raw39999step0Labels := by
      have hz : ∀ j, raw39999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39999step0 = (fun i j => raw39999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39999step0 raw39999; decide +kernel
      have hl : raw39999step0Labels = raw39999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39999 raw39999Labels permutation434 hz
    mixedMoment B raw39999step0 raw39999step0Labels = mixedMoment B raw39999step1 raw39999step1Labels := by
      have hz : ∀ j, raw39999step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39999step1 = (fun i j => raw39999step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39999step1 raw39999step0; decide +kernel
      have hl : raw39999step1Labels = raw39999step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39999step0 raw39999step0Labels permutation80 hz
    mixedMoment B raw39999step1 raw39999step1Labels = mixedMoment B raw39999step2 raw39999step2Labels := by
      have ha : raw39999step2 = (fun i j => raw39999step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39999step2 raw39999step1; decide +kernel
      have hl : raw39999step2Labels = raw39999step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39999step1 raw39999step1Labels permutation12 permutation7
    mixedMoment B raw39999step2 raw39999step2Labels = mixedMoment B raw39999step3 raw39999step3Labels := by
      have ha : raw39999step3 = -raw39999step2 := by apply Matrix.ext; change ∀ i j, raw39999step3 i j = -(raw39999step2 i j); unfold raw39999step3 raw39999step2; decide +kernel
      have hl : raw39999step3Labels = raw39999step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node355 node355Labels := by rfl

def raw40000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40000Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40000step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40000step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40000step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40000step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40000 raw40000Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw40000 raw40000Labels = mixedMoment B raw40000step0 raw40000step0Labels := by
      have hz : ∀ j, raw40000 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40000step0 = (fun i j => raw40000 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40000step0 raw40000; decide +kernel
      have hl : raw40000step0Labels = raw40000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40000 raw40000Labels permutation434 hz
    mixedMoment B raw40000step0 raw40000step0Labels = mixedMoment B raw40000step1 raw40000step1Labels := by
      have hz : ∀ j, raw40000step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40000step1 = (fun i j => raw40000step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40000step1 raw40000step0; decide +kernel
      have hl : raw40000step1Labels = raw40000step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40000step0 raw40000step0Labels permutation80 hz
    mixedMoment B raw40000step1 raw40000step1Labels = mixedMoment B raw40000step2 raw40000step2Labels := by
      have ha : raw40000step2 = (fun i j => raw40000step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40000step2 raw40000step1; decide +kernel
      have hl : raw40000step2Labels = raw40000step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40000step1 raw40000step1Labels permutation13 permutation7
    mixedMoment B raw40000step2 raw40000step2Labels = mixedMoment B raw40000step3 raw40000step3Labels := by
      have ha : raw40000step3 = -raw40000step2 := by apply Matrix.ext; change ∀ i j, raw40000step3 i j = -(raw40000step2 i j); unfold raw40000step3 raw40000step2; decide +kernel
      have hl : raw40000step3Labels = raw40000step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node405 node405Labels := by rfl

def raw40001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40001Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40001step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40001step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40001step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40001 raw40001Labels = mixedMoment B node339 node339Labels := by
  calc
    mixedMoment B raw40001 raw40001Labels = mixedMoment B raw40001step0 raw40001step0Labels := by
      have hz : ∀ j, raw40001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40001step0 = (fun i j => raw40001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40001step0 raw40001; decide +kernel
      have hl : raw40001step0Labels = raw40001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40001 raw40001Labels permutation346 hz
    mixedMoment B raw40001step0 raw40001step0Labels = mixedMoment B raw40001step1 raw40001step1Labels := by
      have ha : raw40001step1 = (fun i j => raw40001step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40001step1 raw40001step0; decide +kernel
      have hl : raw40001step1Labels = raw40001step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40001step0 raw40001step0Labels permutation41 permutation7
    mixedMoment B raw40001step1 raw40001step1Labels = mixedMoment B raw40001step2 raw40001step2Labels := by
      have ha : raw40001step2 = -raw40001step1 := by apply Matrix.ext; change ∀ i j, raw40001step2 i j = -(raw40001step1 i j); unfold raw40001step2 raw40001step1; decide +kernel
      have hl : raw40001step2Labels = raw40001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node339 node339Labels := by rfl

def raw40002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40002Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40002step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40002step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40002 raw40002Labels = mixedMoment B node351 node351Labels := by
  calc
    mixedMoment B raw40002 raw40002Labels = mixedMoment B raw40002step0 raw40002step0Labels := by
      have ha : raw40002step0 = (fun i j => raw40002 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40002step0 raw40002; decide +kernel
      have hl : raw40002step0Labels = raw40002Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40002 raw40002Labels permutation246 permutation7
    mixedMoment B raw40002step0 raw40002step0Labels = mixedMoment B raw40002step1 raw40002step1Labels := by
      have ha : raw40002step1 = -raw40002step0 := by apply Matrix.ext; change ∀ i j, raw40002step1 i j = -(raw40002step0 i j); unfold raw40002step1 raw40002step0; decide +kernel
      have hl : raw40002step1Labels = raw40002step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node351 node351Labels := by rfl

def raw40003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw40003Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw40003step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw40003step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40003step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40003 raw40003Labels = mixedMoment B node352 node352Labels := by
  calc
    mixedMoment B raw40003 raw40003Labels = mixedMoment B raw40003step0 raw40003step0Labels := by
      have hz : ∀ j, raw40003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40003step0 = (fun i j => raw40003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40003step0 raw40003; decide +kernel
      have hl : raw40003step0Labels = raw40003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40003 raw40003Labels permutation434 hz
    mixedMoment B raw40003step0 raw40003step0Labels = mixedMoment B raw40003step1 raw40003step1Labels := by
      have ha : raw40003step1 = (fun i j => raw40003step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40003step1 raw40003step0; decide +kernel
      have hl : raw40003step1Labels = raw40003step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40003step0 raw40003step0Labels permutation50 permutation7
    mixedMoment B raw40003step1 raw40003step1Labels = mixedMoment B raw40003step2 raw40003step2Labels := by
      have ha : raw40003step2 = -raw40003step1 := by apply Matrix.ext; change ∀ i j, raw40003step2 i j = -(raw40003step1 i j); unfold raw40003step2 raw40003step1; decide +kernel
      have hl : raw40003step2Labels = raw40003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node352 node352Labels := by rfl

def raw40004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40004Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40004step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40004step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40004 raw40004Labels = mixedMoment B node334 node334Labels := by
  calc
    mixedMoment B raw40004 raw40004Labels = mixedMoment B raw40004step0 raw40004step0Labels := by
      have ha : raw40004step0 = (fun i j => raw40004 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40004step0 raw40004; decide +kernel
      have hl : raw40004step0Labels = raw40004Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40004 raw40004Labels permutation200 permutation7
    mixedMoment B raw40004step0 raw40004step0Labels = mixedMoment B raw40004step1 raw40004step1Labels := by
      have ha : raw40004step1 = -raw40004step0 := by apply Matrix.ext; change ∀ i j, raw40004step1 i j = -(raw40004step0 i j); unfold raw40004step1 raw40004step0; decide +kernel
      have hl : raw40004step1Labels = raw40004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node334 node334Labels := by rfl

def raw40005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40005Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw40005step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40005step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40005 raw40005Labels = mixedMoment B node283 node283Labels := by
  calc
    mixedMoment B raw40005 raw40005Labels = mixedMoment B raw40005step0 raw40005step0Labels := by
      have ha : raw40005step0 = (fun i j => raw40005 (permutation201 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40005step0 raw40005; decide +kernel
      have hl : raw40005step0Labels = raw40005Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40005 raw40005Labels permutation201 permutation7
    mixedMoment B raw40005step0 raw40005step0Labels = mixedMoment B raw40005step1 raw40005step1Labels := by
      have ha : raw40005step1 = -raw40005step0 := by apply Matrix.ext; change ∀ i j, raw40005step1 i j = -(raw40005step0 i j); unfold raw40005step1 raw40005step0; decide +kernel
      have hl : raw40005step1Labels = raw40005step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node283 node283Labels := by rfl

def raw40006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw40006Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw40006step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -2, 2], ![2, 2, -4]]
def raw40006step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40006step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40006step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40006 raw40006Labels = mixedMoment B node133 node133Labels := by
  calc
    mixedMoment B raw40006 raw40006Labels = mixedMoment B raw40006step0 raw40006step0Labels := by
      have hz : ∀ j, raw40006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40006step0 = (fun i j => raw40006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40006step0 raw40006; decide +kernel
      have hl : raw40006step0Labels = raw40006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40006 raw40006Labels permutation434 hz
    mixedMoment B raw40006step0 raw40006step0Labels = mixedMoment B raw40006step1 raw40006step1Labels := by
      have hz : ∀ j, raw40006step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40006step1 = (fun i j => raw40006step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40006step1 raw40006step0; decide +kernel
      have hl : raw40006step1Labels = raw40006step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40006step0 raw40006step0Labels permutation80 hz
    mixedMoment B raw40006step1 raw40006step1Labels = mixedMoment B raw40006step2 raw40006step2Labels := by
      have ha : raw40006step2 = (fun i j => raw40006step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40006step2 raw40006step1; decide +kernel
      have hl : raw40006step2Labels = raw40006step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40006step1 raw40006step1Labels permutation29 permutation6
    _ = mixedMoment B node133 node133Labels := by rfl

def raw40007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40007Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40007step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw40007step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40007step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40007 raw40007Labels = mixedMoment B node336 node336Labels := by
  calc
    mixedMoment B raw40007 raw40007Labels = mixedMoment B raw40007step0 raw40007step0Labels := by
      have hz : ∀ j, raw40007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40007step0 = (fun i j => raw40007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40007step0 raw40007; decide +kernel
      have hl : raw40007step0Labels = raw40007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40007 raw40007Labels permutation346 hz
    mixedMoment B raw40007step0 raw40007step0Labels = mixedMoment B raw40007step1 raw40007step1Labels := by
      have ha : raw40007step1 = (fun i j => raw40007step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40007step1 raw40007step0; decide +kernel
      have hl : raw40007step1Labels = raw40007step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40007step0 raw40007step0Labels permutation39 permutation7
    mixedMoment B raw40007step1 raw40007step1Labels = mixedMoment B raw40007step2 raw40007step2Labels := by
      have ha : raw40007step2 = -raw40007step1 := by apply Matrix.ext; change ∀ i j, raw40007step2 i j = -(raw40007step1 i j); unfold raw40007step2 raw40007step1; decide +kernel
      have hl : raw40007step2Labels = raw40007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node336 node336Labels := by rfl

def raw40008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw40008Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw40008step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw40008step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40008step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw40008step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40008 raw40008Labels = mixedMoment B node287 node287Labels := by
  calc
    mixedMoment B raw40008 raw40008Labels = mixedMoment B raw40008step0 raw40008step0Labels := by
      have hz : ∀ j, raw40008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40008step0 = (fun i j => raw40008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40008step0 raw40008; decide +kernel
      have hl : raw40008step0Labels = raw40008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40008 raw40008Labels permutation346 hz
    mixedMoment B raw40008step0 raw40008step0Labels = mixedMoment B raw40008step1 raw40008step1Labels := by
      have ha : raw40008step1 = (fun i j => raw40008step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40008step1 raw40008step0; decide +kernel
      have hl : raw40008step1Labels = raw40008step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40008step0 raw40008step0Labels permutation38 permutation7
    mixedMoment B raw40008step1 raw40008step1Labels = mixedMoment B raw40008step2 raw40008step2Labels := by
      have ha : raw40008step2 = -raw40008step1 := by apply Matrix.ext; change ∀ i j, raw40008step2 i j = -(raw40008step1 i j); unfold raw40008step2 raw40008step1; decide +kernel
      have hl : raw40008step2Labels = raw40008step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node287 node287Labels := by rfl

def raw40009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw40009Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw40009step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw40009step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![2, 3, -5]]
def raw40009step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw40009step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40009 raw40009Labels = mixedMoment B node40 node40Labels := by
  calc
    mixedMoment B raw40009 raw40009Labels = mixedMoment B raw40009step0 raw40009step0Labels := by
      have hz : ∀ j, raw40009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40009step0 = (fun i j => raw40009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40009step0 raw40009; decide +kernel
      have hl : raw40009step0Labels = raw40009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40009 raw40009Labels permutation434 hz
    mixedMoment B raw40009step0 raw40009step0Labels = mixedMoment B raw40009step1 raw40009step1Labels := by
      have hz : ∀ j, raw40009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40009step1 = (fun i j => raw40009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40009step1 raw40009step0; decide +kernel
      have hl : raw40009step1Labels = raw40009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40009step0 raw40009step0Labels permutation80 hz
    mixedMoment B raw40009step1 raw40009step1Labels = mixedMoment B raw40009step2 raw40009step2Labels := by
      have hz : ∀ j, raw40009step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40009step2 = (fun i j => raw40009step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40009step2 raw40009step1; decide +kernel
      have hl : raw40009step2Labels = raw40009step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40009step1 raw40009step1Labels permutation14 hz
    mixedMoment B raw40009step2 raw40009step2Labels = mixedMoment B raw40009step3 raw40009step3Labels := by
      have ha : raw40009step3 = (fun i j => raw40009step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40009step3 raw40009step2; decide +kernel
      have hl : raw40009step3Labels = raw40009step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40009step2 raw40009step2Labels permutation7 permutation6
    _ = mixedMoment B node40 node40Labels := by rfl

def raw40010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw40010Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw40010step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw40010step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 3, -4], ![1, -2, 1]]
def raw40010step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw40010step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40010 raw40010Labels = mixedMoment B node112 node112Labels := by
  calc
    mixedMoment B raw40010 raw40010Labels = mixedMoment B raw40010step0 raw40010step0Labels := by
      have hz : ∀ j, raw40010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40010step0 = (fun i j => raw40010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40010step0 raw40010; decide +kernel
      have hl : raw40010step0Labels = raw40010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40010 raw40010Labels permutation434 hz
    mixedMoment B raw40010step0 raw40010step0Labels = mixedMoment B raw40010step1 raw40010step1Labels := by
      have hz : ∀ j, raw40010step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40010step1 = (fun i j => raw40010step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40010step1 raw40010step0; decide +kernel
      have hl : raw40010step1Labels = raw40010step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40010step0 raw40010step0Labels permutation80 hz
    mixedMoment B raw40010step1 raw40010step1Labels = mixedMoment B raw40010step2 raw40010step2Labels := by
      have hz : ∀ j, raw40010step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40010step2 = (fun i j => raw40010step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40010step2 raw40010step1; decide +kernel
      have hl : raw40010step2Labels = raw40010step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40010step1 raw40010step1Labels permutation14 hz
    mixedMoment B raw40010step2 raw40010step2Labels = mixedMoment B raw40010step3 raw40010step3Labels := by
      have ha : raw40010step3 = (fun i j => raw40010step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40010step3 raw40010step2; decide +kernel
      have hl : raw40010step3Labels = raw40010step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40010step2 raw40010step2Labels permutation5 permutation6
    _ = mixedMoment B node112 node112Labels := by rfl

def raw40011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40011Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40011step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40011step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 2, -3], ![1, -1, 0]]
def raw40011step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw40011step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40011 raw40011Labels = mixedMoment B node407 node407Labels := by
  calc
    mixedMoment B raw40011 raw40011Labels = mixedMoment B raw40011step0 raw40011step0Labels := by
      have hz : ∀ j, raw40011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40011step0 = (fun i j => raw40011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40011step0 raw40011; decide +kernel
      have hl : raw40011step0Labels = raw40011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40011 raw40011Labels permutation434 hz
    mixedMoment B raw40011step0 raw40011step0Labels = mixedMoment B raw40011step1 raw40011step1Labels := by
      have hz : ∀ j, raw40011step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40011step1 = (fun i j => raw40011step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40011step1 raw40011step0; decide +kernel
      have hl : raw40011step1Labels = raw40011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40011step0 raw40011step0Labels permutation80 hz
    mixedMoment B raw40011step1 raw40011step1Labels = mixedMoment B raw40011step2 raw40011step2Labels := by
      have hz : ∀ j, raw40011step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40011step2 = (fun i j => raw40011step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40011step2 raw40011step1; decide +kernel
      have hl : raw40011step2Labels = raw40011step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40011step1 raw40011step1Labels permutation14 hz
    mixedMoment B raw40011step2 raw40011step2Labels = mixedMoment B raw40011step3 raw40011step3Labels := by
      have ha : raw40011step3 = (fun i j => raw40011step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40011step3 raw40011step2; decide +kernel
      have hl : raw40011step3Labels = raw40011step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40011step2 raw40011step2Labels permutation5 permutation6
    _ = mixedMoment B node407 node407Labels := by rfl

def raw40012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40012Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40012step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40012step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40012step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40012 raw40012Labels = mixedMoment B node96 node96Labels := by
  calc
    mixedMoment B raw40012 raw40012Labels = mixedMoment B raw40012step0 raw40012step0Labels := by
      have hz : ∀ j, raw40012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40012step0 = (fun i j => raw40012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40012step0 raw40012; decide +kernel
      have hl : raw40012step0Labels = raw40012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40012 raw40012Labels permutation346 hz
    mixedMoment B raw40012step0 raw40012step0Labels = mixedMoment B raw40012step1 raw40012step1Labels := by
      have hz : ∀ j, raw40012step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40012step1 = (fun i j => raw40012step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40012step1 raw40012step0; decide +kernel
      have hl : raw40012step1Labels = raw40012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40012step0 raw40012step0Labels permutation56 hz
    mixedMoment B raw40012step1 raw40012step1Labels = mixedMoment B raw40012step2 raw40012step2Labels := by
      have ha : raw40012step2 = (fun i j => raw40012step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40012step2 raw40012step1; decide +kernel
      have hl : raw40012step2Labels = raw40012step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40012step1 raw40012step1Labels permutation25 permutation6
    _ = mixedMoment B node96 node96Labels := by rfl

def raw40013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40013Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40013step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40013step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw40013step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40013 raw40013Labels = mixedMoment B node341 node341Labels := by
  calc
    mixedMoment B raw40013 raw40013Labels = mixedMoment B raw40013step0 raw40013step0Labels := by
      have hz : ∀ j, raw40013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40013step0 = (fun i j => raw40013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40013step0 raw40013; decide +kernel
      have hl : raw40013step0Labels = raw40013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40013 raw40013Labels permutation346 hz
    mixedMoment B raw40013step0 raw40013step0Labels = mixedMoment B raw40013step1 raw40013step1Labels := by
      have hz : ∀ j, raw40013step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40013step1 = (fun i j => raw40013step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40013step1 raw40013step0; decide +kernel
      have hl : raw40013step1Labels = raw40013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40013step0 raw40013step0Labels permutation56 hz
    mixedMoment B raw40013step1 raw40013step1Labels = mixedMoment B raw40013step2 raw40013step2Labels := by
      have ha : raw40013step2 = (fun i j => raw40013step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40013step2 raw40013step1; decide +kernel
      have hl : raw40013step2Labels = raw40013step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40013step1 raw40013step1Labels permutation25 permutation6
    _ = mixedMoment B node341 node341Labels := by rfl

def raw40014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw40014Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw40014step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw40014step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw40014step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw40014step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40014 raw40014Labels = mixedMoment B node344 node344Labels := by
  calc
    mixedMoment B raw40014 raw40014Labels = mixedMoment B raw40014step0 raw40014step0Labels := by
      have hz : ∀ j, raw40014 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40014step0 = (fun i j => raw40014 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40014step0 raw40014; decide +kernel
      have hl : raw40014step0Labels = raw40014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40014 raw40014Labels permutation346 hz
    mixedMoment B raw40014step0 raw40014step0Labels = mixedMoment B raw40014step1 raw40014step1Labels := by
      have hz : ∀ j, raw40014step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40014step1 = (fun i j => raw40014step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40014step1 raw40014step0; decide +kernel
      have hl : raw40014step1Labels = raw40014step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40014step0 raw40014step0Labels permutation56 hz
    mixedMoment B raw40014step1 raw40014step1Labels = mixedMoment B raw40014step2 raw40014step2Labels := by
      have ha : raw40014step2 = (fun i j => raw40014step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40014step2 raw40014step1; decide +kernel
      have hl : raw40014step2Labels = raw40014step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40014step1 raw40014step1Labels permutation8 permutation7
    mixedMoment B raw40014step2 raw40014step2Labels = mixedMoment B raw40014step3 raw40014step3Labels := by
      have ha : raw40014step3 = -raw40014step2 := by apply Matrix.ext; change ∀ i j, raw40014step3 i j = -(raw40014step2 i j); unfold raw40014step3 raw40014step2; decide +kernel
      have hl : raw40014step3Labels = raw40014step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node344 node344Labels := by rfl

def raw40015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw40015Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw40015step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw40015step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw40015step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40015 raw40015Labels = mixedMoment B node72 node72Labels := by
  calc
    mixedMoment B raw40015 raw40015Labels = mixedMoment B raw40015step0 raw40015step0Labels := by
      have hz : ∀ j, raw40015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40015step0 = (fun i j => raw40015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40015step0 raw40015; decide +kernel
      have hl : raw40015step0Labels = raw40015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40015 raw40015Labels permutation346 hz
    mixedMoment B raw40015step0 raw40015step0Labels = mixedMoment B raw40015step1 raw40015step1Labels := by
      have hz : ∀ j, raw40015step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40015step1 = (fun i j => raw40015step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40015step1 raw40015step0; decide +kernel
      have hl : raw40015step1Labels = raw40015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40015step0 raw40015step0Labels permutation56 hz
    mixedMoment B raw40015step1 raw40015step1Labels = mixedMoment B raw40015step2 raw40015step2Labels := by
      have ha : raw40015step2 = (fun i j => raw40015step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40015step2 raw40015step1; decide +kernel
      have hl : raw40015step2Labels = raw40015step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40015step1 raw40015step1Labels permutation25 permutation6
    _ = mixedMoment B node72 node72Labels := by rfl

def raw40016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40016Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40016step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40016step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40016 raw40016Labels = mixedMoment B node66 node66Labels := by
  calc
    mixedMoment B raw40016 raw40016Labels = mixedMoment B raw40016step0 raw40016step0Labels := by
      have hz : ∀ j, raw40016 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40016step0 = (fun i j => raw40016 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40016step0 raw40016; decide +kernel
      have hl : raw40016step0Labels = raw40016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40016 raw40016Labels permutation265 hz
    mixedMoment B raw40016step0 raw40016step0Labels = mixedMoment B raw40016step1 raw40016step1Labels := by
      have ha : raw40016step1 = (fun i j => raw40016step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40016step1 raw40016step0; decide +kernel
      have hl : raw40016step1Labels = raw40016step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40016step0 raw40016step0Labels permutation125 permutation6
    _ = mixedMoment B node66 node66Labels := by rfl

def raw40017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40017Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40017step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]
def raw40017step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw40017step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw40017step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40017 raw40017Labels = mixedMoment B node148 node148Labels := by
  calc
    mixedMoment B raw40017 raw40017Labels = mixedMoment B raw40017step0 raw40017step0Labels := by
      have hz : ∀ j, raw40017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40017step0 = (fun i j => raw40017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40017step0 raw40017; decide +kernel
      have hl : raw40017step0Labels = raw40017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40017 raw40017Labels permutation434 hz
    mixedMoment B raw40017step0 raw40017step0Labels = mixedMoment B raw40017step1 raw40017step1Labels := by
      have hz : ∀ j, raw40017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40017step1 = (fun i j => raw40017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40017step1 raw40017step0; decide +kernel
      have hl : raw40017step1Labels = raw40017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40017step0 raw40017step0Labels permutation80 hz
    mixedMoment B raw40017step1 raw40017step1Labels = mixedMoment B raw40017step2 raw40017step2Labels := by
      have ha : raw40017step2 = (fun i j => raw40017step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40017step2 raw40017step1; decide +kernel
      have hl : raw40017step2Labels = raw40017step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40017step1 raw40017step1Labels permutation11 permutation6
    mixedMoment B raw40017step2 raw40017step2Labels = mixedMoment B raw40017step3 raw40017step3Labels := by
      have ha : raw40017step3 = -raw40017step2 := by apply Matrix.ext; change ∀ i j, raw40017step3 i j = -(raw40017step2 i j); unfold raw40017step3 raw40017step2; decide +kernel
      have hl : raw40017step3Labels = raw40017step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node148 node148Labels := by rfl

def raw40018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40018Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40018step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40018step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40018step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40018 raw40018Labels = mixedMoment B node145 node145Labels := by
  calc
    mixedMoment B raw40018 raw40018Labels = mixedMoment B raw40018step0 raw40018step0Labels := by
      have hz : ∀ j, raw40018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40018step0 = (fun i j => raw40018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40018step0 raw40018; decide +kernel
      have hl : raw40018step0Labels = raw40018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40018 raw40018Labels permutation434 hz
    mixedMoment B raw40018step0 raw40018step0Labels = mixedMoment B raw40018step1 raw40018step1Labels := by
      have ha : raw40018step1 = (fun i j => raw40018step0 (permutation46 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40018step1 raw40018step0; decide +kernel
      have hl : raw40018step1Labels = raw40018step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40018step0 raw40018step0Labels permutation46 permutation6
    mixedMoment B raw40018step1 raw40018step1Labels = mixedMoment B raw40018step2 raw40018step2Labels := by
      have ha : raw40018step2 = -raw40018step1 := by apply Matrix.ext; change ∀ i j, raw40018step2 i j = -(raw40018step1 i j); unfold raw40018step2 raw40018step1; decide +kernel
      have hl : raw40018step2Labels = raw40018step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node145 node145Labels := by rfl

def raw40019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40019Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40019step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 1, -3]]
def raw40019step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw40019step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw40019step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40019 raw40019Labels = mixedMoment B node147 node147Labels := by
  calc
    mixedMoment B raw40019 raw40019Labels = mixedMoment B raw40019step0 raw40019step0Labels := by
      have hz : ∀ j, raw40019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40019step0 = (fun i j => raw40019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40019step0 raw40019; decide +kernel
      have hl : raw40019step0Labels = raw40019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40019 raw40019Labels permutation434 hz
    mixedMoment B raw40019step0 raw40019step0Labels = mixedMoment B raw40019step1 raw40019step1Labels := by
      have hz : ∀ j, raw40019step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40019step1 = (fun i j => raw40019step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40019step1 raw40019step0; decide +kernel
      have hl : raw40019step1Labels = raw40019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40019step0 raw40019step0Labels permutation80 hz
    mixedMoment B raw40019step1 raw40019step1Labels = mixedMoment B raw40019step2 raw40019step2Labels := by
      have ha : raw40019step2 = (fun i j => raw40019step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40019step2 raw40019step1; decide +kernel
      have hl : raw40019step2Labels = raw40019step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40019step1 raw40019step1Labels permutation10 permutation6
    mixedMoment B raw40019step2 raw40019step2Labels = mixedMoment B raw40019step3 raw40019step3Labels := by
      have ha : raw40019step3 = -raw40019step2 := by apply Matrix.ext; change ∀ i j, raw40019step3 i j = -(raw40019step2 i j); unfold raw40019step3 raw40019step2; decide +kernel
      have hl : raw40019step3Labels = raw40019step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node147 node147Labels := by rfl

def raw40020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40020Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw40020step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40020step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40020step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40020 raw40020Labels = mixedMoment B node139 node139Labels := by
  calc
    mixedMoment B raw40020 raw40020Labels = mixedMoment B raw40020step0 raw40020step0Labels := by
      have hz : ∀ j, raw40020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40020step0 = (fun i j => raw40020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40020step0 raw40020; decide +kernel
      have hl : raw40020step0Labels = raw40020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40020 raw40020Labels permutation434 hz
    mixedMoment B raw40020step0 raw40020step0Labels = mixedMoment B raw40020step1 raw40020step1Labels := by
      have ha : raw40020step1 = (fun i j => raw40020step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40020step1 raw40020step0; decide +kernel
      have hl : raw40020step1Labels = raw40020step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40020step0 raw40020step0Labels permutation45 permutation6
    mixedMoment B raw40020step1 raw40020step1Labels = mixedMoment B raw40020step2 raw40020step2Labels := by
      have ha : raw40020step2 = -raw40020step1 := by apply Matrix.ext; change ∀ i j, raw40020step2 i j = -(raw40020step1 i j); unfold raw40020step2 raw40020step1; decide +kernel
      have hl : raw40020step2Labels = raw40020step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node139 node139Labels := by rfl

def raw40021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40021Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40021step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40021step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw40021step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40021 raw40021Labels = mixedMoment B node140 node140Labels := by
  calc
    mixedMoment B raw40021 raw40021Labels = mixedMoment B raw40021step0 raw40021step0Labels := by
      have hz : ∀ j, raw40021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40021step0 = (fun i j => raw40021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40021step0 raw40021; decide +kernel
      have hl : raw40021step0Labels = raw40021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40021 raw40021Labels permutation434 hz
    mixedMoment B raw40021step0 raw40021step0Labels = mixedMoment B raw40021step1 raw40021step1Labels := by
      have hz : ∀ j, raw40021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40021step1 = (fun i j => raw40021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40021step1 raw40021step0; decide +kernel
      have hl : raw40021step1Labels = raw40021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40021step0 raw40021step0Labels permutation80 hz
    mixedMoment B raw40021step1 raw40021step1Labels = mixedMoment B raw40021step2 raw40021step2Labels := by
      have ha : raw40021step2 = (fun i j => raw40021step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40021step2 raw40021step1; decide +kernel
      have hl : raw40021step2Labels = raw40021step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40021step1 raw40021step1Labels permutation29 permutation6
    _ = mixedMoment B node140 node140Labels := by rfl

def raw40022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40022Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw40022step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw40022step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40022step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40022 raw40022Labels = mixedMoment B node117 node117Labels := by
  calc
    mixedMoment B raw40022 raw40022Labels = mixedMoment B raw40022step0 raw40022step0Labels := by
      have hz : ∀ j, raw40022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40022step0 = (fun i j => raw40022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40022step0 raw40022; decide +kernel
      have hl : raw40022step0Labels = raw40022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40022 raw40022Labels permutation434 hz
    mixedMoment B raw40022step0 raw40022step0Labels = mixedMoment B raw40022step1 raw40022step1Labels := by
      have ha : raw40022step1 = (fun i j => raw40022step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40022step1 raw40022step0; decide +kernel
      have hl : raw40022step1Labels = raw40022step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40022step0 raw40022step0Labels permutation35 permutation7
    mixedMoment B raw40022step1 raw40022step1Labels = mixedMoment B raw40022step2 raw40022step2Labels := by
      have ha : raw40022step2 = -raw40022step1 := by apply Matrix.ext; change ∀ i j, raw40022step2 i j = -(raw40022step1 i j); unfold raw40022step2 raw40022step1; decide +kernel
      have hl : raw40022step2Labels = raw40022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node117 node117Labels := by rfl

def raw40023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40023Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw40023step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40023step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40023 raw40023Labels = mixedMoment B node114 node114Labels := by
  calc
    mixedMoment B raw40023 raw40023Labels = mixedMoment B raw40023step0 raw40023step0Labels := by
      have ha : raw40023step0 = (fun i j => raw40023 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40023step0 raw40023; decide +kernel
      have hl : raw40023step0Labels = raw40023Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40023 raw40023Labels permutation166 permutation7
    mixedMoment B raw40023step0 raw40023step0Labels = mixedMoment B raw40023step1 raw40023step1Labels := by
      have ha : raw40023step1 = -raw40023step0 := by apply Matrix.ext; change ∀ i j, raw40023step1 i j = -(raw40023step0 i j); unfold raw40023step1 raw40023step0; decide +kernel
      have hl : raw40023step1Labels = raw40023step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node114 node114Labels := by rfl

def raw40024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40024Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw40024step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw40024step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40024step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40024 raw40024Labels = mixedMoment B node116 node116Labels := by
  calc
    mixedMoment B raw40024 raw40024Labels = mixedMoment B raw40024step0 raw40024step0Labels := by
      have hz : ∀ j, raw40024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40024step0 = (fun i j => raw40024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40024step0 raw40024; decide +kernel
      have hl : raw40024step0Labels = raw40024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40024 raw40024Labels permutation434 hz
    mixedMoment B raw40024step0 raw40024step0Labels = mixedMoment B raw40024step1 raw40024step1Labels := by
      have ha : raw40024step1 = (fun i j => raw40024step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40024step1 raw40024step0; decide +kernel
      have hl : raw40024step1Labels = raw40024step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40024step0 raw40024step0Labels permutation34 permutation7
    mixedMoment B raw40024step1 raw40024step1Labels = mixedMoment B raw40024step2 raw40024step2Labels := by
      have ha : raw40024step2 = -raw40024step1 := by apply Matrix.ext; change ∀ i j, raw40024step2 i j = -(raw40024step1 i j); unfold raw40024step2 raw40024step1; decide +kernel
      have hl : raw40024step2Labels = raw40024step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node116 node116Labels := by rfl

def raw40025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40025Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw40025step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw40025step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40025 raw40025Labels = mixedMoment B node115 node115Labels := by
  calc
    mixedMoment B raw40025 raw40025Labels = mixedMoment B raw40025step0 raw40025step0Labels := by
      have hz : ∀ j, raw40025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40025step0 = (fun i j => raw40025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40025step0 raw40025; decide +kernel
      have hl : raw40025step0Labels = raw40025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40025 raw40025Labels permutation434 hz
    mixedMoment B raw40025step0 raw40025step0Labels = mixedMoment B raw40025step1 raw40025step1Labels := by
      have ha : raw40025step1 = (fun i j => raw40025step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40025step1 raw40025step0; decide +kernel
      have hl : raw40025step1Labels = raw40025step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40025step0 raw40025step0Labels permutation145 permutation6
    _ = mixedMoment B node115 node115Labels := by rfl

def raw40026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40026Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40026step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40026step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw40026step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40026 raw40026Labels = mixedMoment B node13 node13Labels := by
  calc
    mixedMoment B raw40026 raw40026Labels = mixedMoment B raw40026step0 raw40026step0Labels := by
      have hz : ∀ j, raw40026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40026step0 = (fun i j => raw40026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40026step0 raw40026; decide +kernel
      have hl : raw40026step0Labels = raw40026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40026 raw40026Labels permutation434 hz
    mixedMoment B raw40026step0 raw40026step0Labels = mixedMoment B raw40026step1 raw40026step1Labels := by
      have hz : ∀ j, raw40026step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40026step1 = (fun i j => raw40026step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40026step1 raw40026step0; decide +kernel
      have hl : raw40026step1Labels = raw40026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40026step0 raw40026step0Labels permutation80 hz
    mixedMoment B raw40026step1 raw40026step1Labels = mixedMoment B raw40026step2 raw40026step2Labels := by
      have ha : raw40026step2 = (fun i j => raw40026step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40026step2 raw40026step1; decide +kernel
      have hl : raw40026step2Labels = raw40026step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40026step1 raw40026step1Labels permutation31 permutation6
    _ = mixedMoment B node13 node13Labels := by rfl

def raw40027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40027Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40027step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, -1, 1], ![2, 0, -2]]
def raw40027step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 2, 0], ![-3, 0, 3]]
def raw40027step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw40027step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40027 raw40027Labels = mixedMoment B node131 node131Labels := by
  calc
    mixedMoment B raw40027 raw40027Labels = mixedMoment B raw40027step0 raw40027step0Labels := by
      have hz : ∀ j, raw40027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40027step0 = (fun i j => raw40027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40027step0 raw40027; decide +kernel
      have hl : raw40027step0Labels = raw40027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40027 raw40027Labels permutation434 hz
    mixedMoment B raw40027step0 raw40027step0Labels = mixedMoment B raw40027step1 raw40027step1Labels := by
      have hz : ∀ j, raw40027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40027step1 = (fun i j => raw40027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40027step1 raw40027step0; decide +kernel
      have hl : raw40027step1Labels = raw40027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40027step0 raw40027step0Labels permutation80 hz
    mixedMoment B raw40027step1 raw40027step1Labels = mixedMoment B raw40027step2 raw40027step2Labels := by
      have ha : raw40027step2 = (fun i j => raw40027step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40027step2 raw40027step1; decide +kernel
      have hl : raw40027step2Labels = raw40027step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40027step1 raw40027step1Labels permutation11 permutation6
    mixedMoment B raw40027step2 raw40027step2Labels = mixedMoment B raw40027step3 raw40027step3Labels := by
      have ha : raw40027step3 = -raw40027step2 := by apply Matrix.ext; change ∀ i j, raw40027step3 i j = -(raw40027step2 i j); unfold raw40027step3 raw40027step2; decide +kernel
      have hl : raw40027step3Labels = raw40027step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node131 node131Labels := by rfl

def raw40028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40028Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40028step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40028step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-3, 0, 3]]
def raw40028step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw40028step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40028 raw40028Labels = mixedMoment B node143 node143Labels := by
  calc
    mixedMoment B raw40028 raw40028Labels = mixedMoment B raw40028step0 raw40028step0Labels := by
      have hz : ∀ j, raw40028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40028step0 = (fun i j => raw40028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40028step0 raw40028; decide +kernel
      have hl : raw40028step0Labels = raw40028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40028 raw40028Labels permutation434 hz
    mixedMoment B raw40028step0 raw40028step0Labels = mixedMoment B raw40028step1 raw40028step1Labels := by
      have hz : ∀ j, raw40028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40028step1 = (fun i j => raw40028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40028step1 raw40028step0; decide +kernel
      have hl : raw40028step1Labels = raw40028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40028step0 raw40028step0Labels permutation80 hz
    mixedMoment B raw40028step1 raw40028step1Labels = mixedMoment B raw40028step2 raw40028step2Labels := by
      have ha : raw40028step2 = (fun i j => raw40028step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40028step2 raw40028step1; decide +kernel
      have hl : raw40028step2Labels = raw40028step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40028step1 raw40028step1Labels permutation13 permutation6
    mixedMoment B raw40028step2 raw40028step2Labels = mixedMoment B raw40028step3 raw40028step3Labels := by
      have ha : raw40028step3 = -raw40028step2 := by apply Matrix.ext; change ∀ i j, raw40028step3 i j = -(raw40028step2 i j); unfold raw40028step3 raw40028step2; decide +kernel
      have hl : raw40028step3Labels = raw40028step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node143 node143Labels := by rfl

def raw40029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40029Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40029step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw40029step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw40029step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40029 raw40029Labels = mixedMoment B node119 node119Labels := by
  calc
    mixedMoment B raw40029 raw40029Labels = mixedMoment B raw40029step0 raw40029step0Labels := by
      have hz : ∀ j, raw40029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40029step0 = (fun i j => raw40029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40029step0 raw40029; decide +kernel
      have hl : raw40029step0Labels = raw40029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40029 raw40029Labels permutation346 hz
    mixedMoment B raw40029step0 raw40029step0Labels = mixedMoment B raw40029step1 raw40029step1Labels := by
      have ha : raw40029step1 = (fun i j => raw40029step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40029step1 raw40029step0; decide +kernel
      have hl : raw40029step1Labels = raw40029step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40029step0 raw40029step0Labels permutation41 permutation6
    mixedMoment B raw40029step1 raw40029step1Labels = mixedMoment B raw40029step2 raw40029step2Labels := by
      have ha : raw40029step2 = -raw40029step1 := by apply Matrix.ext; change ∀ i j, raw40029step2 i j = -(raw40029step1 i j); unfold raw40029step2 raw40029step1; decide +kernel
      have hl : raw40029step2Labels = raw40029step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node119 node119Labels := by rfl

def raw40030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40030Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw40030step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40030step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40030step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40030 raw40030Labels = mixedMoment B node127 node127Labels := by
  calc
    mixedMoment B raw40030 raw40030Labels = mixedMoment B raw40030step0 raw40030step0Labels := by
      have hz : ∀ j, raw40030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40030step0 = (fun i j => raw40030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40030step0 raw40030; decide +kernel
      have hl : raw40030step0Labels = raw40030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40030 raw40030Labels permutation434 hz
    mixedMoment B raw40030step0 raw40030step0Labels = mixedMoment B raw40030step1 raw40030step1Labels := by
      have ha : raw40030step1 = (fun i j => raw40030step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40030step1 raw40030step0; decide +kernel
      have hl : raw40030step1Labels = raw40030step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40030step0 raw40030step0Labels permutation47 permutation6
    mixedMoment B raw40030step1 raw40030step1Labels = mixedMoment B raw40030step2 raw40030step2Labels := by
      have ha : raw40030step2 = -raw40030step1 := by apply Matrix.ext; change ∀ i j, raw40030step2 i j = -(raw40030step1 i j); unfold raw40030step2 raw40030step1; decide +kernel
      have hl : raw40030step2Labels = raw40030step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node127 node127Labels := by rfl

def raw40031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40031Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40031step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40031step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40031step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40031 raw40031Labels = mixedMoment B node142 node142Labels := by
  calc
    mixedMoment B raw40031 raw40031Labels = mixedMoment B raw40031step0 raw40031step0Labels := by
      have hz : ∀ j, raw40031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40031step0 = (fun i j => raw40031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40031step0 raw40031; decide +kernel
      have hl : raw40031step0Labels = raw40031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40031 raw40031Labels permutation434 hz
    mixedMoment B raw40031step0 raw40031step0Labels = mixedMoment B raw40031step1 raw40031step1Labels := by
      have ha : raw40031step1 = (fun i j => raw40031step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40031step1 raw40031step0; decide +kernel
      have hl : raw40031step1Labels = raw40031step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40031step0 raw40031step0Labels permutation55 permutation6
    mixedMoment B raw40031step1 raw40031step1Labels = mixedMoment B raw40031step2 raw40031step2Labels := by
      have ha : raw40031step2 = -raw40031step1 := by apply Matrix.ext; change ∀ i j, raw40031step2 i j = -(raw40031step1 i j); unfold raw40031step2 raw40031step1; decide +kernel
      have hl : raw40031step2Labels = raw40031step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node142 node142Labels := by rfl

def raw40032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40032Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40032step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40032step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40032 raw40032Labels = mixedMoment B node118 node118Labels := by
  calc
    mixedMoment B raw40032 raw40032Labels = mixedMoment B raw40032step0 raw40032step0Labels := by
      have ha : raw40032step0 = (fun i j => raw40032 (permutation217 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40032step0 raw40032; decide +kernel
      have hl : raw40032step0Labels = raw40032Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40032 raw40032Labels permutation217 permutation6
    mixedMoment B raw40032step0 raw40032step0Labels = mixedMoment B raw40032step1 raw40032step1Labels := by
      have ha : raw40032step1 = -raw40032step0 := by apply Matrix.ext; change ∀ i j, raw40032step1 i j = -(raw40032step0 i j); unfold raw40032step1 raw40032step0; decide +kernel
      have hl : raw40032step1Labels = raw40032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node118 node118Labels := by rfl

def raw40033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40033Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40033step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]
def raw40033step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]
def raw40033step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-2, 2, 0], ![-2, 0, 2]]
def raw40033step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw40033step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40033 raw40033Labels = mixedMoment B node160 node160Labels := by
  calc
    mixedMoment B raw40033 raw40033Labels = mixedMoment B raw40033step0 raw40033step0Labels := by
      have hz : ∀ j, raw40033 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40033step0 = (fun i j => raw40033 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40033step0 raw40033; decide +kernel
      have hl : raw40033step0Labels = raw40033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40033 raw40033Labels permutation520 hz
    mixedMoment B raw40033step0 raw40033step0Labels = mixedMoment B raw40033step1 raw40033step1Labels := by
      have hz : ∀ j, raw40033step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40033step1 = (fun i j => raw40033step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40033step1 raw40033step0; decide +kernel
      have hl : raw40033step1Labels = raw40033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40033step0 raw40033step0Labels permutation104 hz
    mixedMoment B raw40033step1 raw40033step1Labels = mixedMoment B raw40033step2 raw40033step2Labels := by
      have hz : ∀ j, raw40033step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40033step2 = (fun i j => raw40033step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40033step2 raw40033step1; decide +kernel
      have hl : raw40033step2Labels = raw40033step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40033step1 raw40033step1Labels permutation20 hz
    mixedMoment B raw40033step2 raw40033step2Labels = mixedMoment B raw40033step3 raw40033step3Labels := by
      have ha : raw40033step3 = (fun i j => raw40033step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40033step3 raw40033step2; decide +kernel
      have hl : raw40033step3Labels = raw40033step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40033step2 raw40033step2Labels permutation3 permutation6
    mixedMoment B raw40033step3 raw40033step3Labels = mixedMoment B raw40033step4 raw40033step4Labels := by
      have ha : raw40033step4 = -raw40033step3 := by apply Matrix.ext; change ∀ i j, raw40033step4 i j = -(raw40033step3 i j); unfold raw40033step4 raw40033step3; decide +kernel
      have hl : raw40033step4Labels = raw40033step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node160 node160Labels := by rfl

def raw40034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40034Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40034step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![2, 1, -3]]
def raw40034step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw40034step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40034step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40034 raw40034Labels = mixedMoment B node133 node133Labels := by
  calc
    mixedMoment B raw40034 raw40034Labels = mixedMoment B raw40034step0 raw40034step0Labels := by
      have hz : ∀ j, raw40034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40034step0 = (fun i j => raw40034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40034step0 raw40034; decide +kernel
      have hl : raw40034step0Labels = raw40034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40034 raw40034Labels permutation434 hz
    mixedMoment B raw40034step0 raw40034step0Labels = mixedMoment B raw40034step1 raw40034step1Labels := by
      have hz : ∀ j, raw40034step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40034step1 = (fun i j => raw40034step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40034step1 raw40034step0; decide +kernel
      have hl : raw40034step1Labels = raw40034step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40034step0 raw40034step0Labels permutation80 hz
    mixedMoment B raw40034step1 raw40034step1Labels = mixedMoment B raw40034step2 raw40034step2Labels := by
      have ha : raw40034step2 = (fun i j => raw40034step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40034step2 raw40034step1; decide +kernel
      have hl : raw40034step2Labels = raw40034step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40034step1 raw40034step1Labels permutation10 permutation6
    mixedMoment B raw40034step2 raw40034step2Labels = mixedMoment B raw40034step3 raw40034step3Labels := by
      have ha : raw40034step3 = -raw40034step2 := by apply Matrix.ext; change ∀ i j, raw40034step3 i j = -(raw40034step2 i j); unfold raw40034step3 raw40034step2; decide +kernel
      have hl : raw40034step3Labels = raw40034step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node133 node133Labels := by rfl

def raw40035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40035Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40035step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]
def raw40035step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40035step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40035step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40035 raw40035Labels = mixedMoment B node149 node149Labels := by
  calc
    mixedMoment B raw40035 raw40035Labels = mixedMoment B raw40035step0 raw40035step0Labels := by
      have hz : ∀ j, raw40035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40035step0 = (fun i j => raw40035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40035step0 raw40035; decide +kernel
      have hl : raw40035step0Labels = raw40035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40035 raw40035Labels permutation434 hz
    mixedMoment B raw40035step0 raw40035step0Labels = mixedMoment B raw40035step1 raw40035step1Labels := by
      have hz : ∀ j, raw40035step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40035step1 = (fun i j => raw40035step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40035step1 raw40035step0; decide +kernel
      have hl : raw40035step1Labels = raw40035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40035step0 raw40035step0Labels permutation80 hz
    mixedMoment B raw40035step1 raw40035step1Labels = mixedMoment B raw40035step2 raw40035step2Labels := by
      have ha : raw40035step2 = (fun i j => raw40035step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40035step2 raw40035step1; decide +kernel
      have hl : raw40035step2Labels = raw40035step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40035step1 raw40035step1Labels permutation13 permutation6
    mixedMoment B raw40035step2 raw40035step2Labels = mixedMoment B raw40035step3 raw40035step3Labels := by
      have ha : raw40035step3 = -raw40035step2 := by apply Matrix.ext; change ∀ i j, raw40035step3 i j = -(raw40035step2 i j); unfold raw40035step3 raw40035step2; decide +kernel
      have hl : raw40035step3Labels = raw40035step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node149 node149Labels := by rfl

def raw40036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40036Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40036step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40036step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40036step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40036 raw40036Labels = mixedMoment B node124 node124Labels := by
  calc
    mixedMoment B raw40036 raw40036Labels = mixedMoment B raw40036step0 raw40036step0Labels := by
      have hz : ∀ j, raw40036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40036step0 = (fun i j => raw40036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40036step0 raw40036; decide +kernel
      have hl : raw40036step0Labels = raw40036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40036 raw40036Labels permutation346 hz
    mixedMoment B raw40036step0 raw40036step0Labels = mixedMoment B raw40036step1 raw40036step1Labels := by
      have ha : raw40036step1 = (fun i j => raw40036step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40036step1 raw40036step0; decide +kernel
      have hl : raw40036step1Labels = raw40036step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40036step0 raw40036step0Labels permutation43 permutation6
    mixedMoment B raw40036step1 raw40036step1Labels = mixedMoment B raw40036step2 raw40036step2Labels := by
      have ha : raw40036step2 = -raw40036step1 := by apply Matrix.ext; change ∀ i j, raw40036step2 i j = -(raw40036step1 i j); unfold raw40036step2 raw40036step1; decide +kernel
      have hl : raw40036step2Labels = raw40036step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node124 node124Labels := by rfl

def raw40037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw40037Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40037step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40037step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40037 raw40037Labels = mixedMoment B node125 node125Labels := by
  calc
    mixedMoment B raw40037 raw40037Labels = mixedMoment B raw40037step0 raw40037step0Labels := by
      have ha : raw40037step0 = (fun i j => raw40037 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40037step0 raw40037; decide +kernel
      have hl : raw40037step0Labels = raw40037Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40037 raw40037Labels permutation224 permutation6
    mixedMoment B raw40037step0 raw40037step0Labels = mixedMoment B raw40037step1 raw40037step1Labels := by
      have ha : raw40037step1 = -raw40037step0 := by apply Matrix.ext; change ∀ i j, raw40037step1 i j = -(raw40037step0 i j); unfold raw40037step1 raw40037step0; decide +kernel
      have hl : raw40037step1Labels = raw40037step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node125 node125Labels := by rfl

def raw40038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40038Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3]]
def raw40038step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40038step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40038step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40038 raw40038Labels = mixedMoment B node126 node126Labels := by
  calc
    mixedMoment B raw40038 raw40038Labels = mixedMoment B raw40038step0 raw40038step0Labels := by
      have hz : ∀ j, raw40038 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40038step0 = (fun i j => raw40038 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40038step0 raw40038; decide +kernel
      have hl : raw40038step0Labels = raw40038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40038 raw40038Labels permutation434 hz
    mixedMoment B raw40038step0 raw40038step0Labels = mixedMoment B raw40038step1 raw40038step1Labels := by
      have ha : raw40038step1 = (fun i j => raw40038step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40038step1 raw40038step0; decide +kernel
      have hl : raw40038step1Labels = raw40038step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40038step0 raw40038step0Labels permutation44 permutation6
    mixedMoment B raw40038step1 raw40038step1Labels = mixedMoment B raw40038step2 raw40038step2Labels := by
      have ha : raw40038step2 = -raw40038step1 := by apply Matrix.ext; change ∀ i j, raw40038step2 i j = -(raw40038step1 i j); unfold raw40038step2 raw40038step1; decide +kernel
      have hl : raw40038step2Labels = raw40038step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node126 node126Labels := by rfl

def raw40039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40039Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40039step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]
def raw40039step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def raw40039step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-3, 1, 2]]
def raw40039step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw40039step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40039 raw40039Labels = mixedMoment B node158 node158Labels := by
  calc
    mixedMoment B raw40039 raw40039Labels = mixedMoment B raw40039step0 raw40039step0Labels := by
      have hz : ∀ j, raw40039 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40039step0 = (fun i j => raw40039 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40039step0 raw40039; decide +kernel
      have hl : raw40039step0Labels = raw40039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40039 raw40039Labels permutation520 hz
    mixedMoment B raw40039step0 raw40039step0Labels = mixedMoment B raw40039step1 raw40039step1Labels := by
      have hz : ∀ j, raw40039step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40039step1 = (fun i j => raw40039step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40039step1 raw40039step0; decide +kernel
      have hl : raw40039step1Labels = raw40039step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40039step0 raw40039step0Labels permutation104 hz
    mixedMoment B raw40039step1 raw40039step1Labels = mixedMoment B raw40039step2 raw40039step2Labels := by
      have hz : ∀ j, raw40039step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40039step2 = (fun i j => raw40039step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40039step2 raw40039step1; decide +kernel
      have hl : raw40039step2Labels = raw40039step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40039step1 raw40039step1Labels permutation20 hz
    mixedMoment B raw40039step2 raw40039step2Labels = mixedMoment B raw40039step3 raw40039step3Labels := by
      have ha : raw40039step3 = (fun i j => raw40039step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40039step3 raw40039step2; decide +kernel
      have hl : raw40039step3Labels = raw40039step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40039step2 raw40039step2Labels permutation2 permutation7
    mixedMoment B raw40039step3 raw40039step3Labels = mixedMoment B raw40039step4 raw40039step4Labels := by
      have ha : raw40039step4 = -raw40039step3 := by apply Matrix.ext; change ∀ i j, raw40039step4 i j = -(raw40039step3 i j); unfold raw40039step4 raw40039step3; decide +kernel
      have hl : raw40039step4Labels = raw40039step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node158 node158Labels := by rfl

def raw40040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw40040Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw40040step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, -1, 1], ![2, 2, -4]]
def raw40040step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40040step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw40040step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40040 raw40040Labels = mixedMoment B node129 node129Labels := by
  calc
    mixedMoment B raw40040 raw40040Labels = mixedMoment B raw40040step0 raw40040step0Labels := by
      have hz : ∀ j, raw40040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40040step0 = (fun i j => raw40040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40040step0 raw40040; decide +kernel
      have hl : raw40040step0Labels = raw40040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40040 raw40040Labels permutation434 hz
    mixedMoment B raw40040step0 raw40040step0Labels = mixedMoment B raw40040step1 raw40040step1Labels := by
      have hz : ∀ j, raw40040step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40040step1 = (fun i j => raw40040step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40040step1 raw40040step0; decide +kernel
      have hl : raw40040step1Labels = raw40040step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40040step0 raw40040step0Labels permutation80 hz
    mixedMoment B raw40040step1 raw40040step1Labels = mixedMoment B raw40040step2 raw40040step2Labels := by
      have ha : raw40040step2 = (fun i j => raw40040step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40040step2 raw40040step1; decide +kernel
      have hl : raw40040step2Labels = raw40040step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40040step1 raw40040step1Labels permutation29 permutation6
    _ = mixedMoment B node129 node129Labels := by rfl

def raw40041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40041Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40041step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]
def raw40041step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw40041step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40041step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw40041step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40041 raw40041Labels = mixedMoment B node146 node146Labels := by
  calc
    mixedMoment B raw40041 raw40041Labels = mixedMoment B raw40041step0 raw40041step0Labels := by
      have hz : ∀ j, raw40041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40041step0 = (fun i j => raw40041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40041step0 raw40041; decide +kernel
      have hl : raw40041step0Labels = raw40041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40041 raw40041Labels permutation434 hz
    mixedMoment B raw40041step0 raw40041step0Labels = mixedMoment B raw40041step1 raw40041step1Labels := by
      have hz : ∀ j, raw40041step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40041step1 = (fun i j => raw40041step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40041step1 raw40041step0; decide +kernel
      have hl : raw40041step1Labels = raw40041step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40041step0 raw40041step0Labels permutation80 hz
    mixedMoment B raw40041step1 raw40041step1Labels = mixedMoment B raw40041step2 raw40041step2Labels := by
      have ha : raw40041step2 = (fun i j => raw40041step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40041step2 raw40041step1; decide +kernel
      have hl : raw40041step2Labels = raw40041step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40041step1 raw40041step1Labels permutation12 permutation6
    mixedMoment B raw40041step2 raw40041step2Labels = mixedMoment B raw40041step3 raw40041step3Labels := by
      have ha : raw40041step3 = -raw40041step2 := by apply Matrix.ext; change ∀ i j, raw40041step3 i j = -(raw40041step2 i j); unfold raw40041step3 raw40041step2; decide +kernel
      have hl : raw40041step3Labels = raw40041step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node146 node146Labels := by rfl

def raw40042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40042Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40042step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw40042step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40042step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40042 raw40042Labels = mixedMoment B node121 node121Labels := by
  calc
    mixedMoment B raw40042 raw40042Labels = mixedMoment B raw40042step0 raw40042step0Labels := by
      have hz : ∀ j, raw40042 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40042step0 = (fun i j => raw40042 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40042step0 raw40042; decide +kernel
      have hl : raw40042step0Labels = raw40042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40042 raw40042Labels permutation346 hz
    mixedMoment B raw40042step0 raw40042step0Labels = mixedMoment B raw40042step1 raw40042step1Labels := by
      have ha : raw40042step1 = (fun i j => raw40042step0 (permutation42 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40042step1 raw40042step0; decide +kernel
      have hl : raw40042step1Labels = raw40042step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40042step0 raw40042step0Labels permutation42 permutation6
    mixedMoment B raw40042step1 raw40042step1Labels = mixedMoment B raw40042step2 raw40042step2Labels := by
      have ha : raw40042step2 = -raw40042step1 := by apply Matrix.ext; change ∀ i j, raw40042step2 i j = -(raw40042step1 i j); unfold raw40042step2 raw40042step1; decide +kernel
      have hl : raw40042step2Labels = raw40042step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node121 node121Labels := by rfl

def raw40043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40043Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40043step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40043step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40043step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![2, 2, -4]]
def raw40043step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40043step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -2, 4], ![2, 2, -4]]
def raw40043step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40043step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw40043step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40043 raw40043Labels = mixedMoment B node162 node162Labels := by
  calc
    mixedMoment B raw40043 raw40043Labels = mixedMoment B raw40043step0 raw40043step0Labels := by
      have hz : ∀ j, raw40043 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40043step0 = (fun i j => raw40043 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40043step0 raw40043; decide +kernel
      have hl : raw40043step0Labels = raw40043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40043 raw40043Labels permutation520 hz
    mixedMoment B raw40043step0 raw40043step0Labels = mixedMoment B raw40043step1 raw40043step1Labels := by
      have hz : ∀ j, raw40043step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40043step1 = (fun i j => raw40043step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40043step1 raw40043step0; decide +kernel
      have hl : raw40043step1Labels = raw40043step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40043step0 raw40043step0Labels permutation104 hz
    mixedMoment B raw40043step1 raw40043step1Labels = mixedMoment B raw40043step2 raw40043step2Labels := by
      have hz : ∀ j, raw40043step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40043step2 = (fun i j => raw40043step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40043step2 raw40043step1; decide +kernel
      have hl : raw40043step2Labels = raw40043step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40043step1 raw40043step1Labels permutation20 hz
    mixedMoment B raw40043step2 raw40043step2Labels = mixedMoment B raw40043step3 raw40043step3Labels := by
      have hz : ∀ j, raw40043step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw40043step3 = (fun i j => raw40043step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw40043step3 raw40043step2; decide +kernel
      have hl : raw40043step3Labels = raw40043step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40043step2 raw40043step2Labels permutation4 hz
    mixedMoment B raw40043step3 raw40043step3Labels = mixedMoment B raw40043step4 raw40043step4Labels := by
      have ha : raw40043step4 = (fun i j => raw40043step3 (permutation1 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40043step4 raw40043step3; decide +kernel
      have hl : raw40043step4Labels = raw40043step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40043step3 raw40043step3Labels permutation1 permutation6
    _ = mixedMoment B node162 node162Labels := by rfl

def raw40044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40044Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40044step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw40044step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40044step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![2, 3, -5]]
def raw40044step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40044step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw40044step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40044 raw40044Labels = mixedMoment B node35 node35Labels := by
  calc
    mixedMoment B raw40044 raw40044Labels = mixedMoment B raw40044step0 raw40044step0Labels := by
      have hz : ∀ j, raw40044 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40044step0 = (fun i j => raw40044 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40044step0 raw40044; decide +kernel
      have hl : raw40044step0Labels = raw40044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40044 raw40044Labels permutation434 hz
    mixedMoment B raw40044step0 raw40044step0Labels = mixedMoment B raw40044step1 raw40044step1Labels := by
      have hz : ∀ j, raw40044step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40044step1 = (fun i j => raw40044step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40044step1 raw40044step0; decide +kernel
      have hl : raw40044step1Labels = raw40044step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40044step0 raw40044step0Labels permutation80 hz
    mixedMoment B raw40044step1 raw40044step1Labels = mixedMoment B raw40044step2 raw40044step2Labels := by
      have hz : ∀ j, raw40044step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40044step2 = (fun i j => raw40044step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40044step2 raw40044step1; decide +kernel
      have hl : raw40044step2Labels = raw40044step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40044step1 raw40044step1Labels permutation14 hz
    mixedMoment B raw40044step2 raw40044step2Labels = mixedMoment B raw40044step3 raw40044step3Labels := by
      have ha : raw40044step3 = (fun i j => raw40044step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40044step3 raw40044step2; decide +kernel
      have hl : raw40044step3Labels = raw40044step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40044step2 raw40044step2Labels permutation7 permutation6
    _ = mixedMoment B node35 node35Labels := by rfl

def raw40045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40045Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40045step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw40045step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40045step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 3, -4], ![1, -1, 0]]
def raw40045step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40045step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw40045step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40045 raw40045Labels = mixedMoment B node100 node100Labels := by
  calc
    mixedMoment B raw40045 raw40045Labels = mixedMoment B raw40045step0 raw40045step0Labels := by
      have hz : ∀ j, raw40045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40045step0 = (fun i j => raw40045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40045step0 raw40045; decide +kernel
      have hl : raw40045step0Labels = raw40045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40045 raw40045Labels permutation434 hz
    mixedMoment B raw40045step0 raw40045step0Labels = mixedMoment B raw40045step1 raw40045step1Labels := by
      have hz : ∀ j, raw40045step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40045step1 = (fun i j => raw40045step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40045step1 raw40045step0; decide +kernel
      have hl : raw40045step1Labels = raw40045step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40045step0 raw40045step0Labels permutation80 hz
    mixedMoment B raw40045step1 raw40045step1Labels = mixedMoment B raw40045step2 raw40045step2Labels := by
      have hz : ∀ j, raw40045step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40045step2 = (fun i j => raw40045step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40045step2 raw40045step1; decide +kernel
      have hl : raw40045step2Labels = raw40045step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40045step1 raw40045step1Labels permutation14 hz
    mixedMoment B raw40045step2 raw40045step2Labels = mixedMoment B raw40045step3 raw40045step3Labels := by
      have ha : raw40045step3 = (fun i j => raw40045step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40045step3 raw40045step2; decide +kernel
      have hl : raw40045step3Labels = raw40045step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40045step2 raw40045step2Labels permutation5 permutation6
    _ = mixedMoment B node100 node100Labels := by rfl

def raw40046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40046Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40046step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40046step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw40046step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40046 raw40046Labels = mixedMoment B node70 node70Labels := by
  calc
    mixedMoment B raw40046 raw40046Labels = mixedMoment B raw40046step0 raw40046step0Labels := by
      have hz : ∀ j, raw40046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40046step0 = (fun i j => raw40046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40046step0 raw40046; decide +kernel
      have hl : raw40046step0Labels = raw40046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40046 raw40046Labels permutation346 hz
    mixedMoment B raw40046step0 raw40046step0Labels = mixedMoment B raw40046step1 raw40046step1Labels := by
      have hz : ∀ j, raw40046step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40046step1 = (fun i j => raw40046step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40046step1 raw40046step0; decide +kernel
      have hl : raw40046step1Labels = raw40046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40046step0 raw40046step0Labels permutation56 hz
    mixedMoment B raw40046step1 raw40046step1Labels = mixedMoment B raw40046step2 raw40046step2Labels := by
      have ha : raw40046step2 = (fun i j => raw40046step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40046step2 raw40046step1; decide +kernel
      have hl : raw40046step2Labels = raw40046step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40046step1 raw40046step1Labels permutation25 permutation6
    _ = mixedMoment B node70 node70Labels := by rfl

def raw40047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw40047Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw40047step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw40047step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 1, 1], ![-3, 1, 2]]
def raw40047step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40047step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw40047step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40047 raw40047Labels = mixedMoment B node132 node132Labels := by
  calc
    mixedMoment B raw40047 raw40047Labels = mixedMoment B raw40047step0 raw40047step0Labels := by
      have hz : ∀ j, raw40047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40047step0 = (fun i j => raw40047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40047step0 raw40047; decide +kernel
      have hl : raw40047step0Labels = raw40047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40047 raw40047Labels permutation346 hz
    mixedMoment B raw40047step0 raw40047step0Labels = mixedMoment B raw40047step1 raw40047step1Labels := by
      have hz : ∀ j, raw40047step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40047step1 = (fun i j => raw40047step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40047step1 raw40047step0; decide +kernel
      have hl : raw40047step1Labels = raw40047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40047step0 raw40047step0Labels permutation56 hz
    mixedMoment B raw40047step1 raw40047step1Labels = mixedMoment B raw40047step2 raw40047step2Labels := by
      have ha : raw40047step2 = (fun i j => raw40047step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40047step2 raw40047step1; decide +kernel
      have hl : raw40047step2Labels = raw40047step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40047step1 raw40047step1Labels permutation9 permutation6
    mixedMoment B raw40047step2 raw40047step2Labels = mixedMoment B raw40047step3 raw40047step3Labels := by
      have ha : raw40047step3 = -raw40047step2 := by apply Matrix.ext; change ∀ i j, raw40047step3 i j = -(raw40047step2 i j); unfold raw40047step3 raw40047step2; decide +kernel
      have hl : raw40047step3Labels = raw40047step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node132 node132Labels := by rfl

def raw40048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40048Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40048step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![0, 0, 0], ![2, 0, -2]]
def raw40048step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40048step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]
def raw40048step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40048step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 2, 0], ![-3, 0, 3]]
def raw40048step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40048step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw40048step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40048 raw40048Labels = mixedMoment B node38 node38Labels := by
  calc
    mixedMoment B raw40048 raw40048Labels = mixedMoment B raw40048step0 raw40048step0Labels := by
      have hz : ∀ j, raw40048 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40048step0 = (fun i j => raw40048 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40048step0 raw40048; decide +kernel
      have hl : raw40048step0Labels = raw40048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40048 raw40048Labels permutation520 hz
    mixedMoment B raw40048step0 raw40048step0Labels = mixedMoment B raw40048step1 raw40048step1Labels := by
      have hz : ∀ j, raw40048step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40048step1 = (fun i j => raw40048step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40048step1 raw40048step0; decide +kernel
      have hl : raw40048step1Labels = raw40048step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40048step0 raw40048step0Labels permutation104 hz
    mixedMoment B raw40048step1 raw40048step1Labels = mixedMoment B raw40048step2 raw40048step2Labels := by
      have hz : ∀ j, raw40048step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40048step2 = (fun i j => raw40048step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40048step2 raw40048step1; decide +kernel
      have hl : raw40048step2Labels = raw40048step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40048step1 raw40048step1Labels permutation20 hz
    mixedMoment B raw40048step2 raw40048step2Labels = mixedMoment B raw40048step3 raw40048step3Labels := by
      have ha : raw40048step3 = (fun i j => raw40048step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40048step3 raw40048step2; decide +kernel
      have hl : raw40048step3Labels = raw40048step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40048step2 raw40048step2Labels permutation3 permutation6
    mixedMoment B raw40048step3 raw40048step3Labels = mixedMoment B raw40048step4 raw40048step4Labels := by
      have ha : raw40048step4 = -raw40048step3 := by apply Matrix.ext; change ∀ i j, raw40048step4 i j = -(raw40048step3 i j); unfold raw40048step4 raw40048step3; decide +kernel
      have hl : raw40048step4Labels = raw40048step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node38 node38Labels := by rfl

def raw40049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40049Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw40049step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]
def raw40049step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40049step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40049step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40049step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40049 raw40049Labels = mixedMoment B node33 node33Labels := by
  calc
    mixedMoment B raw40049 raw40049Labels = mixedMoment B raw40049step0 raw40049step0Labels := by
      have hz : ∀ j, raw40049 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40049step0 = (fun i j => raw40049 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40049step0 raw40049; decide +kernel
      have hl : raw40049step0Labels = raw40049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40049 raw40049Labels permutation520 hz
    mixedMoment B raw40049step0 raw40049step0Labels = mixedMoment B raw40049step1 raw40049step1Labels := by
      have hz : ∀ j, raw40049step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40049step1 = (fun i j => raw40049step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40049step1 raw40049step0; decide +kernel
      have hl : raw40049step1Labels = raw40049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40049step0 raw40049step0Labels permutation104 hz
    mixedMoment B raw40049step1 raw40049step1Labels = mixedMoment B raw40049step2 raw40049step2Labels := by
      have ha : raw40049step2 = (fun i j => raw40049step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40049step2 raw40049step1; decide +kernel
      have hl : raw40049step2Labels = raw40049step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40049step1 raw40049step1Labels permutation11 permutation6
    mixedMoment B raw40049step2 raw40049step2Labels = mixedMoment B raw40049step3 raw40049step3Labels := by
      have ha : raw40049step3 = -raw40049step2 := by apply Matrix.ext; change ∀ i j, raw40049step3 i j = -(raw40049step2 i j); unfold raw40049step3 raw40049step2; decide +kernel
      have hl : raw40049step3Labels = raw40049step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node33 node33Labels := by rfl

def raw40050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40050Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40050step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![2, 1, -3]]
def raw40050step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40050step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]
def raw40050step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40050step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 0, 2], ![-3, 2, 1]]
def raw40050step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40050step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw40050step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40050 raw40050Labels = mixedMoment B node40 node40Labels := by
  calc
    mixedMoment B raw40050 raw40050Labels = mixedMoment B raw40050step0 raw40050step0Labels := by
      have hz : ∀ j, raw40050 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40050step0 = (fun i j => raw40050 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40050step0 raw40050; decide +kernel
      have hl : raw40050step0Labels = raw40050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40050 raw40050Labels permutation520 hz
    mixedMoment B raw40050step0 raw40050step0Labels = mixedMoment B raw40050step1 raw40050step1Labels := by
      have hz : ∀ j, raw40050step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40050step1 = (fun i j => raw40050step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40050step1 raw40050step0; decide +kernel
      have hl : raw40050step1Labels = raw40050step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40050step0 raw40050step0Labels permutation104 hz
    mixedMoment B raw40050step1 raw40050step1Labels = mixedMoment B raw40050step2 raw40050step2Labels := by
      have hz : ∀ j, raw40050step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40050step2 = (fun i j => raw40050step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40050step2 raw40050step1; decide +kernel
      have hl : raw40050step2Labels = raw40050step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40050step1 raw40050step1Labels permutation20 hz
    mixedMoment B raw40050step2 raw40050step2Labels = mixedMoment B raw40050step3 raw40050step3Labels := by
      have ha : raw40050step3 = (fun i j => raw40050step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40050step3 raw40050step2; decide +kernel
      have hl : raw40050step3Labels = raw40050step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40050step2 raw40050step2Labels permutation2 permutation6
    mixedMoment B raw40050step3 raw40050step3Labels = mixedMoment B raw40050step4 raw40050step4Labels := by
      have ha : raw40050step4 = -raw40050step3 := by apply Matrix.ext; change ∀ i j, raw40050step4 i j = -(raw40050step3 i j); unfold raw40050step4 raw40050step3; decide +kernel
      have hl : raw40050step4Labels = raw40050step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node40 node40Labels := by rfl

def raw40051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40051Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40051step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40051step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40051 raw40051Labels = mixedMoment B node22 node22Labels := by
  calc
    mixedMoment B raw40051 raw40051Labels = mixedMoment B raw40051step0 raw40051step0Labels := by
      have ha : raw40051step0 = (fun i j => raw40051 (permutation240 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40051step0 raw40051; decide +kernel
      have hl : raw40051step0Labels = raw40051Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40051 raw40051Labels permutation240 permutation6
    mixedMoment B raw40051step0 raw40051step0Labels = mixedMoment B raw40051step1 raw40051step1Labels := by
      have ha : raw40051step1 = -raw40051step0 := by apply Matrix.ext; change ∀ i j, raw40051step1 i j = -(raw40051step0 i j); unfold raw40051step1 raw40051step0; decide +kernel
      have hl : raw40051step1Labels = raw40051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node22 node22Labels := by rfl

def raw40052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw40052Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]
def raw40052step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40052step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40052step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40052 raw40052Labels = mixedMoment B node26 node26Labels := by
  calc
    mixedMoment B raw40052 raw40052Labels = mixedMoment B raw40052step0 raw40052step0Labels := by
      have hz : ∀ j, raw40052 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40052step0 = (fun i j => raw40052 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40052step0 raw40052; decide +kernel
      have hl : raw40052step0Labels = raw40052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40052 raw40052Labels permutation434 hz
    mixedMoment B raw40052step0 raw40052step0Labels = mixedMoment B raw40052step1 raw40052step1Labels := by
      have ha : raw40052step1 = (fun i j => raw40052step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40052step1 raw40052step0; decide +kernel
      have hl : raw40052step1Labels = raw40052step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40052step0 raw40052step0Labels permutation50 permutation6
    mixedMoment B raw40052step1 raw40052step1Labels = mixedMoment B raw40052step2 raw40052step2Labels := by
      have ha : raw40052step2 = -raw40052step1 := by apply Matrix.ext; change ∀ i j, raw40052step2 i j = -(raw40052step1 i j); unfold raw40052step2 raw40052step1; decide +kernel
      have hl : raw40052step2Labels = raw40052step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node26 node26Labels := by rfl

def raw40053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]
def raw40053Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]
def raw40053step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw40053step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40053step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40053step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40053 raw40053Labels = mixedMoment B node34 node34Labels := by
  calc
    mixedMoment B raw40053 raw40053Labels = mixedMoment B raw40053step0 raw40053step0Labels := by
      have hz : ∀ j, raw40053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40053step0 = (fun i j => raw40053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40053step0 raw40053; decide +kernel
      have hl : raw40053step0Labels = raw40053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40053 raw40053Labels permutation434 hz
    mixedMoment B raw40053step0 raw40053step0Labels = mixedMoment B raw40053step1 raw40053step1Labels := by
      have hz : ∀ j, raw40053step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40053step1 = (fun i j => raw40053step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40053step1 raw40053step0; decide +kernel
      have hl : raw40053step1Labels = raw40053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40053step0 raw40053step0Labels permutation80 hz
    mixedMoment B raw40053step1 raw40053step1Labels = mixedMoment B raw40053step2 raw40053step2Labels := by
      have ha : raw40053step2 = (fun i j => raw40053step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40053step2 raw40053step1; decide +kernel
      have hl : raw40053step2Labels = raw40053step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40053step1 raw40053step1Labels permutation8 permutation6
    mixedMoment B raw40053step2 raw40053step2Labels = mixedMoment B raw40053step3 raw40053step3Labels := by
      have ha : raw40053step3 = -raw40053step2 := by apply Matrix.ext; change ∀ i j, raw40053step3 i j = -(raw40053step2 i j); unfold raw40053step3 raw40053step2; decide +kernel
      have hl : raw40053step3Labels = raw40053step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node34 node34Labels := by rfl

def raw40054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw40054Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw40054step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw40054step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40054step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![2, 3, -5]]
def raw40054step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40054step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -3, 5], ![2, 3, -5]]
def raw40054step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40054step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw40054step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40054 raw40054Labels = mixedMoment B node42 node42Labels := by
  calc
    mixedMoment B raw40054 raw40054Labels = mixedMoment B raw40054step0 raw40054step0Labels := by
      have hz : ∀ j, raw40054 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40054step0 = (fun i j => raw40054 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40054step0 raw40054; decide +kernel
      have hl : raw40054step0Labels = raw40054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40054 raw40054Labels permutation520 hz
    mixedMoment B raw40054step0 raw40054step0Labels = mixedMoment B raw40054step1 raw40054step1Labels := by
      have hz : ∀ j, raw40054step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40054step1 = (fun i j => raw40054step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40054step1 raw40054step0; decide +kernel
      have hl : raw40054step1Labels = raw40054step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40054step0 raw40054step0Labels permutation104 hz
    mixedMoment B raw40054step1 raw40054step1Labels = mixedMoment B raw40054step2 raw40054step2Labels := by
      have hz : ∀ j, raw40054step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40054step2 = (fun i j => raw40054step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40054step2 raw40054step1; decide +kernel
      have hl : raw40054step2Labels = raw40054step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40054step1 raw40054step1Labels permutation20 hz
    mixedMoment B raw40054step2 raw40054step2Labels = mixedMoment B raw40054step3 raw40054step3Labels := by
      have hz : ∀ j, raw40054step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw40054step3 = (fun i j => raw40054step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw40054step3 raw40054step2; decide +kernel
      have hl : raw40054step3Labels = raw40054step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40054step2 raw40054step2Labels permutation4 hz
    mixedMoment B raw40054step3 raw40054step3Labels = mixedMoment B raw40054step4 raw40054step4Labels := by
      have ha : raw40054step4 = (fun i j => raw40054step3 (permutation1 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40054step4 raw40054step3; decide +kernel
      have hl : raw40054step4Labels = raw40054step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40054step3 raw40054step3Labels permutation1 permutation6
    _ = mixedMoment B node42 node42Labels := by rfl

def raw40055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40055Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw40055step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw40055step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40055step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40055 raw40055Labels = mixedMoment B node397 node397Labels := by
  calc
    mixedMoment B raw40055 raw40055Labels = mixedMoment B raw40055step0 raw40055step0Labels := by
      have hz : ∀ j, raw40055 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40055step0 = (fun i j => raw40055 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40055step0 raw40055; decide +kernel
      have hl : raw40055step0Labels = raw40055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40055 raw40055Labels permutation434 hz
    mixedMoment B raw40055step0 raw40055step0Labels = mixedMoment B raw40055step1 raw40055step1Labels := by
      have ha : raw40055step1 = (fun i j => raw40055step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40055step1 raw40055step0; decide +kernel
      have hl : raw40055step1Labels = raw40055step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40055step0 raw40055step0Labels permutation32 permutation4
    mixedMoment B raw40055step1 raw40055step1Labels = mixedMoment B raw40055step2 raw40055step2Labels := by
      have ha : raw40055step2 = -raw40055step1 := by apply Matrix.ext; change ∀ i j, raw40055step2 i j = -(raw40055step1 i j); unfold raw40055step2 raw40055step1; decide +kernel
      have hl : raw40055step2Labels = raw40055step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node397 node397Labels := by rfl

def raw40056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40056Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw40056step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw40056step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40056step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40056 raw40056Labels = mixedMoment B node395 node395Labels := by
  calc
    mixedMoment B raw40056 raw40056Labels = mixedMoment B raw40056step0 raw40056step0Labels := by
      have hz : ∀ j, raw40056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40056step0 = (fun i j => raw40056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40056step0 raw40056; decide +kernel
      have hl : raw40056step0Labels = raw40056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40056 raw40056Labels permutation434 hz
    mixedMoment B raw40056step0 raw40056step0Labels = mixedMoment B raw40056step1 raw40056step1Labels := by
      have ha : raw40056step1 = (fun i j => raw40056step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40056step1 raw40056step0; decide +kernel
      have hl : raw40056step1Labels = raw40056step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40056step0 raw40056step0Labels permutation33 permutation4
    mixedMoment B raw40056step1 raw40056step1Labels = mixedMoment B raw40056step2 raw40056step2Labels := by
      have ha : raw40056step2 = -raw40056step1 := by apply Matrix.ext; change ∀ i j, raw40056step2 i j = -(raw40056step1 i j); unfold raw40056step2 raw40056step1; decide +kernel
      have hl : raw40056step2Labels = raw40056step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node395 node395Labels := by rfl

def raw40057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40057Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40057step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40057step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40057 raw40057Labels = mixedMoment B node394 node394Labels := by
  calc
    mixedMoment B raw40057 raw40057Labels = mixedMoment B raw40057step0 raw40057step0Labels := by
      have ha : raw40057step0 = (fun i j => raw40057 (permutation157 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40057step0 raw40057; decide +kernel
      have hl : raw40057step0Labels = raw40057Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40057 raw40057Labels permutation157 permutation4
    mixedMoment B raw40057step0 raw40057step0Labels = mixedMoment B raw40057step1 raw40057step1Labels := by
      have ha : raw40057step1 = -raw40057step0 := by apply Matrix.ext; change ∀ i j, raw40057step1 i j = -(raw40057step0 i j); unfold raw40057step1 raw40057step0; decide +kernel
      have hl : raw40057step1Labels = raw40057step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node394 node394Labels := by rfl

def raw40058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40058Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40058step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40058step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40058 raw40058Labels = mixedMoment B node358 node358Labels := by
  calc
    mixedMoment B raw40058 raw40058Labels = mixedMoment B raw40058step0 raw40058step0Labels := by
      have ha : raw40058step0 = (fun i j => raw40058 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40058step0 raw40058; decide +kernel
      have hl : raw40058step0Labels = raw40058Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40058 raw40058Labels permutation246 permutation4
    mixedMoment B raw40058step0 raw40058step0Labels = mixedMoment B raw40058step1 raw40058step1Labels := by
      have ha : raw40058step1 = -raw40058step0 := by apply Matrix.ext; change ∀ i j, raw40058step1 i j = -(raw40058step0 i j); unfold raw40058step1 raw40058step0; decide +kernel
      have hl : raw40058step1Labels = raw40058step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node358 node358Labels := by rfl

def raw40059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40059Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40059step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40059step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40059 raw40059Labels = mixedMoment B node357 node357Labels := by
  calc
    mixedMoment B raw40059 raw40059Labels = mixedMoment B raw40059step0 raw40059step0Labels := by
      have ha : raw40059step0 = (fun i j => raw40059 (permutation247 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40059step0 raw40059; decide +kernel
      have hl : raw40059step0Labels = raw40059Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40059 raw40059Labels permutation247 permutation4
    mixedMoment B raw40059step0 raw40059step0Labels = mixedMoment B raw40059step1 raw40059step1Labels := by
      have ha : raw40059step1 = -raw40059step0 := by apply Matrix.ext; change ∀ i j, raw40059step1 i j = -(raw40059step0 i j); unfold raw40059step1 raw40059step0; decide +kernel
      have hl : raw40059step1Labels = raw40059step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node357 node357Labels := by rfl

def raw40060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40060Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw40060step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw40060step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40060step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40060 raw40060Labels = mixedMoment B node400 node400Labels := by
  calc
    mixedMoment B raw40060 raw40060Labels = mixedMoment B raw40060step0 raw40060step0Labels := by
      have hz : ∀ j, raw40060 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40060step0 = (fun i j => raw40060 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40060step0 raw40060; decide +kernel
      have hl : raw40060step0Labels = raw40060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40060 raw40060Labels permutation434 hz
    mixedMoment B raw40060step0 raw40060step0Labels = mixedMoment B raw40060step1 raw40060step1Labels := by
      have ha : raw40060step1 = (fun i j => raw40060step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40060step1 raw40060step0; decide +kernel
      have hl : raw40060step1Labels = raw40060step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40060step0 raw40060step0Labels permutation37 permutation4
    mixedMoment B raw40060step1 raw40060step1Labels = mixedMoment B raw40060step2 raw40060step2Labels := by
      have ha : raw40060step2 = -raw40060step1 := by apply Matrix.ext; change ∀ i j, raw40060step2 i j = -(raw40060step1 i j); unfold raw40060step2 raw40060step1; decide +kernel
      have hl : raw40060step2Labels = raw40060step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node400 node400Labels := by rfl

def raw40061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40061Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw40061step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40061step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw40061step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40061 raw40061Labels = mixedMoment B node362 node362Labels := by
  calc
    mixedMoment B raw40061 raw40061Labels = mixedMoment B raw40061step0 raw40061step0Labels := by
      have hz : ∀ j, raw40061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40061step0 = (fun i j => raw40061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40061step0 raw40061; decide +kernel
      have hl : raw40061step0Labels = raw40061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40061 raw40061Labels permutation434 hz
    mixedMoment B raw40061step0 raw40061step0Labels = mixedMoment B raw40061step1 raw40061step1Labels := by
      have ha : raw40061step1 = (fun i j => raw40061step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40061step1 raw40061step0; decide +kernel
      have hl : raw40061step1Labels = raw40061step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40061step0 raw40061step0Labels permutation50 permutation4
    mixedMoment B raw40061step1 raw40061step1Labels = mixedMoment B raw40061step2 raw40061step2Labels := by
      have ha : raw40061step2 = -raw40061step1 := by apply Matrix.ext; change ∀ i j, raw40061step2 i j = -(raw40061step1 i j); unfold raw40061step2 raw40061step1; decide +kernel
      have hl : raw40061step2Labels = raw40061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node362 node362Labels := by rfl

def raw40062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40062Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw40062step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40062step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40062 raw40062Labels = mixedMoment B node359 node359Labels := by
  calc
    mixedMoment B raw40062 raw40062Labels = mixedMoment B raw40062step0 raw40062step0Labels := by
      have ha : raw40062step0 = (fun i j => raw40062 (permutation251 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40062step0 raw40062; decide +kernel
      have hl : raw40062step0Labels = raw40062Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40062 raw40062Labels permutation251 permutation4
    mixedMoment B raw40062step0 raw40062step0Labels = mixedMoment B raw40062step1 raw40062step1Labels := by
      have ha : raw40062step1 = -raw40062step0 := by apply Matrix.ext; change ∀ i j, raw40062step1 i j = -(raw40062step0 i j); unfold raw40062step1 raw40062step0; decide +kernel
      have hl : raw40062step1Labels = raw40062step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node359 node359Labels := by rfl

def raw40063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40063Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40063step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1]]
def raw40063step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40063step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40063step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40063step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40063 raw40063Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw40063 raw40063Labels = mixedMoment B raw40063step0 raw40063step0Labels := by
      have hz : ∀ j, raw40063 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40063step0 = (fun i j => raw40063 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40063step0 raw40063; decide +kernel
      have hl : raw40063step0Labels = raw40063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40063 raw40063Labels permutation434 hz
    mixedMoment B raw40063step0 raw40063step0Labels = mixedMoment B raw40063step1 raw40063step1Labels := by
      have hz : ∀ j, raw40063step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40063step1 = (fun i j => raw40063step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40063step1 raw40063step0; decide +kernel
      have hl : raw40063step1Labels = raw40063step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40063step0 raw40063step0Labels permutation80 hz
    mixedMoment B raw40063step1 raw40063step1Labels = mixedMoment B raw40063step2 raw40063step2Labels := by
      have ha : raw40063step2 = (fun i j => raw40063step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40063step2 raw40063step1; decide +kernel
      have hl : raw40063step2Labels = raw40063step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40063step1 raw40063step1Labels permutation8 permutation4
    mixedMoment B raw40063step2 raw40063step2Labels = mixedMoment B raw40063step3 raw40063step3Labels := by
      have ha : raw40063step3 = -raw40063step2 := by apply Matrix.ext; change ∀ i j, raw40063step3 i j = -(raw40063step2 i j); unfold raw40063step3 raw40063step2; decide +kernel
      have hl : raw40063step3Labels = raw40063step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node404 node404Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
