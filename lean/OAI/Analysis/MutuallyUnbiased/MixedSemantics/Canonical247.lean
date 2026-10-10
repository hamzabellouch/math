import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31616 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![-1, 1], ![2, -2], ![1, -1]]
def raw31616Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31616step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![2, -2], ![1, -1]]
def raw31616step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31616step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw31616step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31616 raw31616Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw31616 raw31616Labels = mixedMoment B raw31616step0 raw31616step0Labels := by
      have hz : ∀ j, raw31616 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw31616step0 = (fun i j => raw31616 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw31616step0 raw31616; decide +kernel
      have hl : raw31616step0Labels = raw31616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31616 raw31616Labels permutation265 hz
    mixedMoment B raw31616step0 raw31616step0Labels = mixedMoment B raw31616step1 raw31616step1Labels := by
      have ha : raw31616step1 = (fun i j => raw31616step0 (permutation39 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31616step1 raw31616step0; decide +kernel
      have hl : raw31616step1Labels = raw31616step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31616step0 raw31616step0Labels permutation39 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw31617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31617step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31617 raw31617Labels = mixedMoment B node901 node901Labels := by
  calc
    mixedMoment B raw31617 raw31617Labels = mixedMoment B raw31617step0 raw31617step0Labels := by
      have ha : raw31617step0 = (fun i j => raw31617 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31617step0 raw31617; decide +kernel
      have hl : raw31617step0Labels = raw31617Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31617 raw31617Labels permutation159 permutation2
    _ = mixedMoment B node901 node901Labels := by rfl

def raw31618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31618 raw31618Labels = mixedMoment B node1787 node1787Labels := by
  calc
    mixedMoment B raw31618 raw31618Labels = mixedMoment B raw31618step0 raw31618step0Labels := by
      have ha : raw31618step0 = (fun i j => raw31618 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31618step0 raw31618; decide +kernel
      have hl : raw31618step0Labels = raw31618Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31618 raw31618Labels permutation159 permutation2
    _ = mixedMoment B node1787 node1787Labels := by rfl

def raw31619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31619Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31619step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31619 raw31619Labels = mixedMoment B node1869 node1869Labels := by
  calc
    mixedMoment B raw31619 raw31619Labels = mixedMoment B raw31619step0 raw31619step0Labels := by
      have ha : raw31619step0 = (fun i j => raw31619 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31619step0 raw31619; decide +kernel
      have hl : raw31619step0Labels = raw31619Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31619 raw31619Labels permutation201 permutation2
    _ = mixedMoment B node1869 node1869Labels := by rfl

def raw31620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw31620Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31620step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31620 raw31620Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw31620 raw31620Labels = mixedMoment B raw31620step0 raw31620step0Labels := by
      have ha : raw31620step0 = (fun i j => raw31620 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31620step0 raw31620; decide +kernel
      have hl : raw31620step0Labels = raw31620Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31620 raw31620Labels permutation158 permutation2
    _ = mixedMoment B node2000 node2000Labels := by rfl

def raw31621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw31621Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31621 raw31621Labels = mixedMoment B node1999 node1999Labels := by
  calc
    mixedMoment B raw31621 raw31621Labels = mixedMoment B raw31621step0 raw31621step0Labels := by
      have ha : raw31621step0 = (fun i j => raw31621 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31621step0 raw31621; decide +kernel
      have hl : raw31621step0Labels = raw31621Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31621 raw31621Labels permutation159 permutation2
    _ = mixedMoment B node1999 node1999Labels := by rfl

def raw31622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31622Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31622step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31622 raw31622Labels = mixedMoment B node1918 node1918Labels := by
  calc
    mixedMoment B raw31622 raw31622Labels = mixedMoment B raw31622step0 raw31622step0Labels := by
      have hz : ∀ j, raw31622 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw31622step0 = (fun i j => raw31622 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw31622step0 raw31622; decide +kernel
      have hl : raw31622step0Labels = raw31622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31622 raw31622Labels permutation265 hz
    mixedMoment B raw31622step0 raw31622step0Labels = mixedMoment B raw31622step1 raw31622step1Labels := by
      have ha : raw31622step1 = (fun i j => raw31622step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31622step1 raw31622step0; decide +kernel
      have hl : raw31622step1Labels = raw31622step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31622step0 raw31622step0Labels permutation39 permutation2
    _ = mixedMoment B node1918 node1918Labels := by rfl

def raw31623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw31623Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31623step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31623 raw31623Labels = mixedMoment B node1860 node1860Labels := by
  calc
    mixedMoment B raw31623 raw31623Labels = mixedMoment B raw31623step0 raw31623step0Labels := by
      have ha : raw31623step0 = (fun i j => raw31623 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31623step0 raw31623; decide +kernel
      have hl : raw31623step0Labels = raw31623Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31623 raw31623Labels permutation201 permutation2
    _ = mixedMoment B node1860 node1860Labels := by rfl

def raw31624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw31624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31624step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31624 raw31624Labels = mixedMoment B node1861 node1861Labels := by
  calc
    mixedMoment B raw31624 raw31624Labels = mixedMoment B raw31624step0 raw31624step0Labels := by
      have ha : raw31624step0 = (fun i j => raw31624 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31624step0 raw31624; decide +kernel
      have hl : raw31624step0Labels = raw31624Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31624 raw31624Labels permutation200 permutation2
    _ = mixedMoment B node1861 node1861Labels := by rfl

def raw31625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw31625step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31625step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw31625step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31625 raw31625Labels = mixedMoment B node5235 node5235Labels := by
  calc
    mixedMoment B raw31625 raw31625Labels = mixedMoment B raw31625step0 raw31625step0Labels := by
      have hz : ∀ j, raw31625 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31625step0 = (fun i j => raw31625 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31625step0 raw31625; decide +kernel
      have hl : raw31625step0Labels = raw31625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31625 raw31625Labels permutation434 hz
    mixedMoment B raw31625step0 raw31625step0Labels = mixedMoment B raw31625step1 raw31625step1Labels := by
      have hz : ∀ j, raw31625step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31625step1 = (fun i j => raw31625step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31625step1 raw31625step0; decide +kernel
      have hl : raw31625step1Labels = raw31625step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31625step0 raw31625step0Labels permutation80 hz
    mixedMoment B raw31625step1 raw31625step1Labels = mixedMoment B raw31625step2 raw31625step2Labels := by
      have ha : raw31625step2 = (fun i j => raw31625step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31625step2 raw31625step1; decide +kernel
      have hl : raw31625step2Labels = raw31625step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31625step1 raw31625step1Labels permutation25 permutation7
    mixedMoment B raw31625step2 raw31625step2Labels = mixedMoment B raw31625step3 raw31625step3Labels := by
      have ha : raw31625step3 = raw31625step2 := by apply Matrix.ext; unfold raw31625step3 raw31625step2; decide +kernel
      have hl : raw31625step2Labels = labelEmbedding10 ∘ raw31625step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31625step2 raw31625step2Labels raw31625step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5235 node5235Labels := by rfl

def raw31626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31626step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31626 raw31626Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw31626 raw31626Labels = mixedMoment B raw31626step0 raw31626step0Labels := by
      have hz : ∀ j, raw31626 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31626step0 = (fun i j => raw31626 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31626step0 raw31626; decide +kernel
      have hl : raw31626step0Labels = raw31626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31626 raw31626Labels permutation434 hz
    mixedMoment B raw31626step0 raw31626step0Labels = mixedMoment B raw31626step1 raw31626step1Labels := by
      have ha : raw31626step1 = (fun i j => raw31626step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31626step1 raw31626step0; decide +kernel
      have hl : raw31626step1Labels = raw31626step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31626step0 raw31626step0Labels permutation125 permutation7
    mixedMoment B raw31626step1 raw31626step1Labels = mixedMoment B raw31626step2 raw31626step2Labels := by
      have ha : raw31626step2 = raw31626step1 := by apply Matrix.ext; unfold raw31626step2 raw31626step1; decide +kernel
      have hl : raw31626step1Labels = labelEmbedding10 ∘ raw31626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31626step1 raw31626step1Labels raw31626step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw31627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31627step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31627step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31627 raw31627Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw31627 raw31627Labels = mixedMoment B raw31627step0 raw31627step0Labels := by
      have hz : ∀ j, raw31627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31627step0 = (fun i j => raw31627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31627step0 raw31627; decide +kernel
      have hl : raw31627step0Labels = raw31627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31627 raw31627Labels permutation346 hz
    mixedMoment B raw31627step0 raw31627step0Labels = mixedMoment B raw31627step1 raw31627step1Labels := by
      have ha : raw31627step1 = (fun i j => raw31627step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31627step1 raw31627step0; decide +kernel
      have hl : raw31627step1Labels = raw31627step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31627step0 raw31627step0Labels permutation125 permutation7
    mixedMoment B raw31627step1 raw31627step1Labels = mixedMoment B raw31627step2 raw31627step2Labels := by
      have ha : raw31627step2 = raw31627step1 := by apply Matrix.ext; unfold raw31627step2 raw31627step1; decide +kernel
      have hl : raw31627step1Labels = labelEmbedding10 ∘ raw31627step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31627step1 raw31627step1Labels raw31627step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw31628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw31628step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31628step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw31628step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31628 raw31628Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw31628 raw31628Labels = mixedMoment B raw31628step0 raw31628step0Labels := by
      have hz : ∀ j, raw31628 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31628step0 = (fun i j => raw31628 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31628step0 raw31628; decide +kernel
      have hl : raw31628step0Labels = raw31628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31628 raw31628Labels permutation434 hz
    mixedMoment B raw31628step0 raw31628step0Labels = mixedMoment B raw31628step1 raw31628step1Labels := by
      have hz : ∀ j, raw31628step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31628step1 = (fun i j => raw31628step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31628step1 raw31628step0; decide +kernel
      have hl : raw31628step1Labels = raw31628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31628step0 raw31628step0Labels permutation80 hz
    mixedMoment B raw31628step1 raw31628step1Labels = mixedMoment B raw31628step2 raw31628step2Labels := by
      have ha : raw31628step2 = (fun i j => raw31628step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31628step2 raw31628step1; decide +kernel
      have hl : raw31628step2Labels = raw31628step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31628step1 raw31628step1Labels permutation23 permutation6
    mixedMoment B raw31628step2 raw31628step2Labels = mixedMoment B raw31628step3 raw31628step3Labels := by
      have ha : raw31628step3 = raw31628step2 := by apply Matrix.ext; unfold raw31628step3 raw31628step2; decide +kernel
      have hl : raw31628step2Labels = labelEmbedding9 ∘ raw31628step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31628step2 raw31628step2Labels raw31628step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw31629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31629step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw31629step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31629step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw31629step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31629 raw31629Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw31629 raw31629Labels = mixedMoment B raw31629step0 raw31629step0Labels := by
      have hz : ∀ j, raw31629 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31629step0 = (fun i j => raw31629 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31629step0 raw31629; decide +kernel
      have hl : raw31629step0Labels = raw31629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31629 raw31629Labels permutation434 hz
    mixedMoment B raw31629step0 raw31629step0Labels = mixedMoment B raw31629step1 raw31629step1Labels := by
      have hz : ∀ j, raw31629step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31629step1 = (fun i j => raw31629step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31629step1 raw31629step0; decide +kernel
      have hl : raw31629step1Labels = raw31629step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31629step0 raw31629step0Labels permutation80 hz
    mixedMoment B raw31629step1 raw31629step1Labels = mixedMoment B raw31629step2 raw31629step2Labels := by
      have ha : raw31629step2 = (fun i j => raw31629step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31629step2 raw31629step1; decide +kernel
      have hl : raw31629step2Labels = raw31629step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31629step1 raw31629step1Labels permutation25 permutation7
    mixedMoment B raw31629step2 raw31629step2Labels = mixedMoment B raw31629step3 raw31629step3Labels := by
      have ha : raw31629step3 = raw31629step2 := by apply Matrix.ext; unfold raw31629step3 raw31629step2; decide +kernel
      have hl : raw31629step2Labels = labelEmbedding10 ∘ raw31629step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31629step2 raw31629step2Labels raw31629step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw31630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31630step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31630step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 1, -3], ![2, -2, 0]]
def raw31630step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31630step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw31630step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31630 raw31630Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw31630 raw31630Labels = mixedMoment B raw31630step0 raw31630step0Labels := by
      have hz : ∀ j, raw31630 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31630step0 = (fun i j => raw31630 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31630step0 raw31630; decide +kernel
      have hl : raw31630step0Labels = raw31630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31630 raw31630Labels permutation434 hz
    mixedMoment B raw31630step0 raw31630step0Labels = mixedMoment B raw31630step1 raw31630step1Labels := by
      have hz : ∀ j, raw31630step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31630step1 = (fun i j => raw31630step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31630step1 raw31630step0; decide +kernel
      have hl : raw31630step1Labels = raw31630step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31630step0 raw31630step0Labels permutation80 hz
    mixedMoment B raw31630step1 raw31630step1Labels = mixedMoment B raw31630step2 raw31630step2Labels := by
      have hz : ∀ j, raw31630step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw31630step2 = (fun i j => raw31630step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw31630step2 raw31630step1; decide +kernel
      have hl : raw31630step2Labels = raw31630step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31630step1 raw31630step1Labels permutation14 hz
    mixedMoment B raw31630step2 raw31630step2Labels = mixedMoment B raw31630step3 raw31630step3Labels := by
      have ha : raw31630step3 = (fun i j => raw31630step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31630step3 raw31630step2; decide +kernel
      have hl : raw31630step3Labels = raw31630step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31630step2 raw31630step2Labels permutation3 permutation2
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw31631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31631 raw31631Labels = mixedMoment B node4683 node4683Labels := by
  calc
    mixedMoment B raw31631 raw31631Labels = mixedMoment B raw31631step0 raw31631step0Labels := by
      have hz : ∀ j, raw31631 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31631step0 = (fun i j => raw31631 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31631step0 raw31631; decide +kernel
      have hl : raw31631step0Labels = raw31631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31631 raw31631Labels permutation434 hz
    mixedMoment B raw31631step0 raw31631step0Labels = mixedMoment B raw31631step1 raw31631step1Labels := by
      have ha : raw31631step1 = (fun i j => raw31631step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31631step1 raw31631step0; decide +kernel
      have hl : raw31631step1Labels = raw31631step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31631step0 raw31631step0Labels permutation33 permutation2
    _ = mixedMoment B node4683 node4683Labels := by rfl

def raw31632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31632 raw31632Labels = mixedMoment B node4762 node4762Labels := by
  calc
    mixedMoment B raw31632 raw31632Labels = mixedMoment B raw31632step0 raw31632step0Labels := by
      have ha : raw31632step0 = (fun i j => raw31632 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31632step0 raw31632; decide +kernel
      have hl : raw31632step0Labels = raw31632Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31632 raw31632Labels permutation159 permutation2
    _ = mixedMoment B node4762 node4762Labels := by rfl

def raw31633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31633 raw31633Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw31633 raw31633Labels = mixedMoment B raw31633step0 raw31633step0Labels := by
      have hz : ∀ j, raw31633 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31633step0 = (fun i j => raw31633 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31633step0 raw31633; decide +kernel
      have hl : raw31633step0Labels = raw31633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31633 raw31633Labels permutation434 hz
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw31634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw31634step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31634 raw31634Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw31634 raw31634Labels = mixedMoment B raw31634step0 raw31634step0Labels := by
      have hz : ∀ j, raw31634 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31634step0 = (fun i j => raw31634 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31634step0 raw31634; decide +kernel
      have hl : raw31634step0Labels = raw31634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31634 raw31634Labels permutation434 hz
    mixedMoment B raw31634step0 raw31634step0Labels = mixedMoment B raw31634step1 raw31634step1Labels := by
      have ha : raw31634step1 = (fun i j => raw31634step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31634step1 raw31634step0; decide +kernel
      have hl : raw31634step1Labels = raw31634step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31634step0 raw31634step0Labels permutation33 permutation2
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw31635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31635 raw31635Labels = mixedMoment B node4683 node4683Labels := by
  calc
    mixedMoment B raw31635 raw31635Labels = mixedMoment B raw31635step0 raw31635step0Labels := by
      have hz : ∀ j, raw31635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31635step0 = (fun i j => raw31635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31635step0 raw31635; decide +kernel
      have hl : raw31635step0Labels = raw31635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31635 raw31635Labels permutation346 hz
    mixedMoment B raw31635step0 raw31635step0Labels = mixedMoment B raw31635step1 raw31635step1Labels := by
      have ha : raw31635step1 = (fun i j => raw31635step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31635step1 raw31635step0; decide +kernel
      have hl : raw31635step1Labels = raw31635step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31635step0 raw31635step0Labels permutation33 permutation2
    _ = mixedMoment B node4683 node4683Labels := by rfl

def raw31636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31636 raw31636Labels = mixedMoment B node4762 node4762Labels := by
  calc
    mixedMoment B raw31636 raw31636Labels = mixedMoment B raw31636step0 raw31636step0Labels := by
      have ha : raw31636step0 = (fun i j => raw31636 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31636step0 raw31636; decide +kernel
      have hl : raw31636step0Labels = raw31636Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31636 raw31636Labels permutation153 permutation2
    _ = mixedMoment B node4762 node4762Labels := by rfl

def raw31637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31637 raw31637Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw31637 raw31637Labels = mixedMoment B raw31637step0 raw31637step0Labels := by
      have hz : ∀ j, raw31637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31637step0 = (fun i j => raw31637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31637step0 raw31637; decide +kernel
      have hl : raw31637step0Labels = raw31637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31637 raw31637Labels permutation346 hz
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw31638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw31638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31638 raw31638Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw31638 raw31638Labels = mixedMoment B raw31638step0 raw31638step0Labels := by
      have hz : ∀ j, raw31638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31638step0 = (fun i j => raw31638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31638step0 raw31638; decide +kernel
      have hl : raw31638step0Labels = raw31638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31638 raw31638Labels permutation346 hz
    mixedMoment B raw31638step0 raw31638step0Labels = mixedMoment B raw31638step1 raw31638step1Labels := by
      have ha : raw31638step1 = (fun i j => raw31638step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31638step1 raw31638step0; decide +kernel
      have hl : raw31638step1Labels = raw31638step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31638step0 raw31638step0Labels permutation33 permutation2
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw31639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31639step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw31639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31639 raw31639Labels = mixedMoment B node4691 node4691Labels := by
  calc
    mixedMoment B raw31639 raw31639Labels = mixedMoment B raw31639step0 raw31639step0Labels := by
      have hz : ∀ j, raw31639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31639step0 = (fun i j => raw31639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31639step0 raw31639; decide +kernel
      have hl : raw31639step0Labels = raw31639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31639 raw31639Labels permutation434 hz
    mixedMoment B raw31639step0 raw31639step0Labels = mixedMoment B raw31639step1 raw31639step1Labels := by
      have hz : ∀ j, raw31639step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31639step1 = (fun i j => raw31639step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31639step1 raw31639step0; decide +kernel
      have hl : raw31639step1Labels = raw31639step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31639step0 raw31639step0Labels permutation80 hz
    mixedMoment B raw31639step1 raw31639step1Labels = mixedMoment B raw31639step2 raw31639step2Labels := by
      have ha : raw31639step2 = (fun i j => raw31639step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31639step2 raw31639step1; decide +kernel
      have hl : raw31639step2Labels = raw31639step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31639step1 raw31639step1Labels permutation9 permutation2
    _ = mixedMoment B node4691 node4691Labels := by rfl

def raw31640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw31640step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw31640step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31640 raw31640Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw31640 raw31640Labels = mixedMoment B raw31640step0 raw31640step0Labels := by
      have hz : ∀ j, raw31640 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31640step0 = (fun i j => raw31640 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31640step0 raw31640; decide +kernel
      have hl : raw31640step0Labels = raw31640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31640 raw31640Labels permutation434 hz
    mixedMoment B raw31640step0 raw31640step0Labels = mixedMoment B raw31640step1 raw31640step1Labels := by
      have ha : raw31640step1 = (fun i j => raw31640step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31640step1 raw31640step0; decide +kernel
      have hl : raw31640step1Labels = raw31640step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31640step0 raw31640step0Labels permutation125 permutation2
    mixedMoment B raw31640step1 raw31640step1Labels = mixedMoment B raw31640step2 raw31640step2Labels := by
      have ha : raw31640step2 = -raw31640step1 := by apply Matrix.ext; change ∀ i j, raw31640step2 i j = -(raw31640step1 i j); unfold raw31640step2 raw31640step1; decide +kernel
      have hl : raw31640step2Labels = raw31640step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4678 node4678Labels := by rfl

def raw31641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw31641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31641step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw31641step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31641 raw31641Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw31641 raw31641Labels = mixedMoment B raw31641step0 raw31641step0Labels := by
      have hz : ∀ j, raw31641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31641step0 = (fun i j => raw31641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31641step0 raw31641; decide +kernel
      have hl : raw31641step0Labels = raw31641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31641 raw31641Labels permutation346 hz
    mixedMoment B raw31641step0 raw31641step0Labels = mixedMoment B raw31641step1 raw31641step1Labels := by
      have ha : raw31641step1 = (fun i j => raw31641step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31641step1 raw31641step0; decide +kernel
      have hl : raw31641step1Labels = raw31641step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31641step0 raw31641step0Labels permutation125 permutation2
    mixedMoment B raw31641step1 raw31641step1Labels = mixedMoment B raw31641step2 raw31641step2Labels := by
      have ha : raw31641step2 = -raw31641step1 := by apply Matrix.ext; change ∀ i j, raw31641step2 i j = -(raw31641step1 i j); unfold raw31641step2 raw31641step1; decide +kernel
      have hl : raw31641step2Labels = raw31641step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4678 node4678Labels := by rfl

def raw31642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw31642step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31642 raw31642Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw31642 raw31642Labels = mixedMoment B raw31642step0 raw31642step0Labels := by
      have hz : ∀ j, raw31642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31642step0 = (fun i j => raw31642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31642step0 raw31642; decide +kernel
      have hl : raw31642step0Labels = raw31642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31642 raw31642Labels permutation434 hz
    mixedMoment B raw31642step0 raw31642step0Labels = mixedMoment B raw31642step1 raw31642step1Labels := by
      have hz : ∀ j, raw31642step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31642step1 = (fun i j => raw31642step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31642step1 raw31642step0; decide +kernel
      have hl : raw31642step1Labels = raw31642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31642step0 raw31642step0Labels permutation80 hz
    mixedMoment B raw31642step1 raw31642step1Labels = mixedMoment B raw31642step2 raw31642step2Labels := by
      have ha : raw31642step2 = (fun i j => raw31642step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31642step2 raw31642step1; decide +kernel
      have hl : raw31642step2Labels = raw31642step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31642step1 raw31642step1Labels permutation9 permutation2
    _ = mixedMoment B node4837 node4837Labels := by rfl

def raw31643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31643step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31643 raw31643Labels = mixedMoment B node4694 node4694Labels := by
  calc
    mixedMoment B raw31643 raw31643Labels = mixedMoment B raw31643step0 raw31643step0Labels := by
      have hz : ∀ j, raw31643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31643step0 = (fun i j => raw31643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31643step0 raw31643; decide +kernel
      have hl : raw31643step0Labels = raw31643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31643 raw31643Labels permutation434 hz
    mixedMoment B raw31643step0 raw31643step0Labels = mixedMoment B raw31643step1 raw31643step1Labels := by
      have hz : ∀ j, raw31643step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31643step1 = (fun i j => raw31643step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31643step1 raw31643step0; decide +kernel
      have hl : raw31643step1Labels = raw31643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31643step0 raw31643step0Labels permutation80 hz
    _ = mixedMoment B node4694 node4694Labels := by rfl

def raw31644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31644step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31644step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31644step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31644step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31644 raw31644Labels = mixedMoment B node4702 node4702Labels := by
  calc
    mixedMoment B raw31644 raw31644Labels = mixedMoment B raw31644step0 raw31644step0Labels := by
      have hz : ∀ j, raw31644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31644step0 = (fun i j => raw31644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31644step0 raw31644; decide +kernel
      have hl : raw31644step0Labels = raw31644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31644 raw31644Labels permutation434 hz
    mixedMoment B raw31644step0 raw31644step0Labels = mixedMoment B raw31644step1 raw31644step1Labels := by
      have ha : raw31644step1 = (fun i j => raw31644step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31644step1 raw31644step0; decide +kernel
      have hl : raw31644step1Labels = raw31644step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31644step0 raw31644step0Labels permutation149 permutation3
    mixedMoment B raw31644step1 raw31644step1Labels = mixedMoment B raw31644step2 raw31644step2Labels := by
      have ha : raw31644step2 = -raw31644step1 := by apply Matrix.ext; change ∀ i j, raw31644step2 i j = -(raw31644step1 i j); unfold raw31644step2 raw31644step1; decide +kernel
      have hl : raw31644step2Labels = raw31644step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31644step2 raw31644step2Labels = mixedMoment B raw31644step3 raw31644step3Labels := by
      have ha : raw31644step3 = raw31644step2 := by apply Matrix.ext; unfold raw31644step3 raw31644step2; decide +kernel
      have hl : raw31644step2Labels = labelEmbedding6 ∘ raw31644step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31644step2 raw31644step2Labels raw31644step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4702 node4702Labels := by rfl

def raw31645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31645step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31645step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31645step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31645step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31645 raw31645Labels = mixedMoment B node4702 node4702Labels := by
  calc
    mixedMoment B raw31645 raw31645Labels = mixedMoment B raw31645step0 raw31645step0Labels := by
      have hz : ∀ j, raw31645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31645step0 = (fun i j => raw31645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31645step0 raw31645; decide +kernel
      have hl : raw31645step0Labels = raw31645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31645 raw31645Labels permutation346 hz
    mixedMoment B raw31645step0 raw31645step0Labels = mixedMoment B raw31645step1 raw31645step1Labels := by
      have ha : raw31645step1 = (fun i j => raw31645step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31645step1 raw31645step0; decide +kernel
      have hl : raw31645step1Labels = raw31645step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31645step0 raw31645step0Labels permutation149 permutation3
    mixedMoment B raw31645step1 raw31645step1Labels = mixedMoment B raw31645step2 raw31645step2Labels := by
      have ha : raw31645step2 = -raw31645step1 := by apply Matrix.ext; change ∀ i j, raw31645step2 i j = -(raw31645step1 i j); unfold raw31645step2 raw31645step1; decide +kernel
      have hl : raw31645step2Labels = raw31645step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31645step2 raw31645step2Labels = mixedMoment B raw31645step3 raw31645step3Labels := by
      have ha : raw31645step3 = raw31645step2 := by apply Matrix.ext; unfold raw31645step3 raw31645step2; decide +kernel
      have hl : raw31645step2Labels = labelEmbedding6 ∘ raw31645step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31645step2 raw31645step2Labels raw31645step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4702 node4702Labels := by rfl

def raw31646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31646step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw31646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31646 raw31646Labels = mixedMoment B node3046 node3046Labels := by
  calc
    mixedMoment B raw31646 raw31646Labels = mixedMoment B raw31646step0 raw31646step0Labels := by
      have hz : ∀ j, raw31646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31646step0 = (fun i j => raw31646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31646step0 raw31646; decide +kernel
      have hl : raw31646step0Labels = raw31646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31646 raw31646Labels permutation434 hz
    mixedMoment B raw31646step0 raw31646step0Labels = mixedMoment B raw31646step1 raw31646step1Labels := by
      have hz : ∀ j, raw31646step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31646step1 = (fun i j => raw31646step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31646step1 raw31646step0; decide +kernel
      have hl : raw31646step1Labels = raw31646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31646step0 raw31646step0Labels permutation80 hz
    mixedMoment B raw31646step1 raw31646step1Labels = mixedMoment B raw31646step2 raw31646step2Labels := by
      have ha : raw31646step2 = (fun i j => raw31646step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31646step2 raw31646step1; decide +kernel
      have hl : raw31646step2Labels = raw31646step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31646step1 raw31646step1Labels permutation23 permutation6
    _ = mixedMoment B node3046 node3046Labels := by rfl

def raw31647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw31647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw31647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31647 raw31647Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw31647 raw31647Labels = mixedMoment B raw31647step0 raw31647step0Labels := by
      have hz : ∀ j, raw31647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31647step0 = (fun i j => raw31647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31647step0 raw31647; decide +kernel
      have hl : raw31647step0Labels = raw31647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31647 raw31647Labels permutation434 hz
    mixedMoment B raw31647step0 raw31647step0Labels = mixedMoment B raw31647step1 raw31647step1Labels := by
      have ha : raw31647step1 = (fun i j => raw31647step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31647step1 raw31647step0; decide +kernel
      have hl : raw31647step1Labels = raw31647step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31647step0 raw31647step0Labels permutation50 permutation6
    mixedMoment B raw31647step1 raw31647step1Labels = mixedMoment B raw31647step2 raw31647step2Labels := by
      have ha : raw31647step2 = -raw31647step1 := by apply Matrix.ext; change ∀ i j, raw31647step2 i j = -(raw31647step1 i j); unfold raw31647step2 raw31647step1; decide +kernel
      have hl : raw31647step2Labels = raw31647step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3031 node3031Labels := by rfl

def raw31648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw31648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw31648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31648 raw31648Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw31648 raw31648Labels = mixedMoment B raw31648step0 raw31648step0Labels := by
      have hz : ∀ j, raw31648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31648step0 = (fun i j => raw31648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31648step0 raw31648; decide +kernel
      have hl : raw31648step0Labels = raw31648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31648 raw31648Labels permutation346 hz
    mixedMoment B raw31648step0 raw31648step0Labels = mixedMoment B raw31648step1 raw31648step1Labels := by
      have ha : raw31648step1 = (fun i j => raw31648step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31648step1 raw31648step0; decide +kernel
      have hl : raw31648step1Labels = raw31648step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31648step0 raw31648step0Labels permutation50 permutation6
    mixedMoment B raw31648step1 raw31648step1Labels = mixedMoment B raw31648step2 raw31648step2Labels := by
      have ha : raw31648step2 = -raw31648step1 := by apply Matrix.ext; change ∀ i j, raw31648step2 i j = -(raw31648step1 i j); unfold raw31648step2 raw31648step1; decide +kernel
      have hl : raw31648step2Labels = raw31648step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3031 node3031Labels := by rfl

def raw31649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31649step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw31649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31649 raw31649Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw31649 raw31649Labels = mixedMoment B raw31649step0 raw31649step0Labels := by
      have hz : ∀ j, raw31649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31649step0 = (fun i j => raw31649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31649step0 raw31649; decide +kernel
      have hl : raw31649step0Labels = raw31649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31649 raw31649Labels permutation434 hz
    mixedMoment B raw31649step0 raw31649step0Labels = mixedMoment B raw31649step1 raw31649step1Labels := by
      have hz : ∀ j, raw31649step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31649step1 = (fun i j => raw31649step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31649step1 raw31649step0; decide +kernel
      have hl : raw31649step1Labels = raw31649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31649step0 raw31649step0Labels permutation80 hz
    mixedMoment B raw31649step1 raw31649step1Labels = mixedMoment B raw31649step2 raw31649step2Labels := by
      have ha : raw31649step2 = (fun i j => raw31649step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31649step2 raw31649step1; decide +kernel
      have hl : raw31649step2Labels = raw31649step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31649step1 raw31649step1Labels permutation23 permutation6
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw31650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31650step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw31650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31650 raw31650Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw31650 raw31650Labels = mixedMoment B raw31650step0 raw31650step0Labels := by
      have hz : ∀ j, raw31650 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31650step0 = (fun i j => raw31650 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31650step0 raw31650; decide +kernel
      have hl : raw31650step0Labels = raw31650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31650 raw31650Labels permutation434 hz
    mixedMoment B raw31650step0 raw31650step0Labels = mixedMoment B raw31650step1 raw31650step1Labels := by
      have hz : ∀ j, raw31650step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31650step1 = (fun i j => raw31650step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31650step1 raw31650step0; decide +kernel
      have hl : raw31650step1Labels = raw31650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31650step0 raw31650step0Labels permutation80 hz
    mixedMoment B raw31650step1 raw31650step1Labels = mixedMoment B raw31650step2 raw31650step2Labels := by
      have ha : raw31650step2 = (fun i j => raw31650step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31650step2 raw31650step1; decide +kernel
      have hl : raw31650step2Labels = raw31650step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31650step1 raw31650step1Labels permutation23 permutation6
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw31651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31651step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31651step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 1, -3], ![2, -2, 0]]
def raw31651step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31651step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw31651step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31651 raw31651Labels = mixedMoment B node1454 node1454Labels := by
  calc
    mixedMoment B raw31651 raw31651Labels = mixedMoment B raw31651step0 raw31651step0Labels := by
      have hz : ∀ j, raw31651 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31651step0 = (fun i j => raw31651 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31651step0 raw31651; decide +kernel
      have hl : raw31651step0Labels = raw31651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31651 raw31651Labels permutation434 hz
    mixedMoment B raw31651step0 raw31651step0Labels = mixedMoment B raw31651step1 raw31651step1Labels := by
      have hz : ∀ j, raw31651step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31651step1 = (fun i j => raw31651step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31651step1 raw31651step0; decide +kernel
      have hl : raw31651step1Labels = raw31651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31651step0 raw31651step0Labels permutation80 hz
    mixedMoment B raw31651step1 raw31651step1Labels = mixedMoment B raw31651step2 raw31651step2Labels := by
      have hz : ∀ j, raw31651step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw31651step2 = (fun i j => raw31651step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw31651step2 raw31651step1; decide +kernel
      have hl : raw31651step2Labels = raw31651step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31651step1 raw31651step1Labels permutation14 hz
    mixedMoment B raw31651step2 raw31651step2Labels = mixedMoment B raw31651step3 raw31651step3Labels := by
      have ha : raw31651step3 = (fun i j => raw31651step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31651step3 raw31651step2; decide +kernel
      have hl : raw31651step3Labels = raw31651step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31651step2 raw31651step2Labels permutation2 permutation3
    _ = mixedMoment B node1454 node1454Labels := by rfl

def raw31652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31652 raw31652Labels = mixedMoment B node3033 node3033Labels := by
  calc
    mixedMoment B raw31652 raw31652Labels = mixedMoment B raw31652step0 raw31652step0Labels := by
      have hz : ∀ j, raw31652 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31652step0 = (fun i j => raw31652 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31652step0 raw31652; decide +kernel
      have hl : raw31652step0Labels = raw31652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31652 raw31652Labels permutation434 hz
    mixedMoment B raw31652step0 raw31652step0Labels = mixedMoment B raw31652step1 raw31652step1Labels := by
      have ha : raw31652step1 = (fun i j => raw31652step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31652step1 raw31652step0; decide +kernel
      have hl : raw31652step1Labels = raw31652step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31652step0 raw31652step0Labels permutation113 permutation6
    _ = mixedMoment B node3033 node3033Labels := by rfl

def raw31653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31653 raw31653Labels = mixedMoment B node3062 node3062Labels := by
  calc
    mixedMoment B raw31653 raw31653Labels = mixedMoment B raw31653step0 raw31653step0Labels := by
      have ha : raw31653step0 = (fun i j => raw31653 (permutation536 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31653step0 raw31653; decide +kernel
      have hl : raw31653step0Labels = raw31653Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31653 raw31653Labels permutation536 permutation6
    _ = mixedMoment B node3062 node3062Labels := by rfl

def raw31654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31654step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31654 raw31654Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw31654 raw31654Labels = mixedMoment B raw31654step0 raw31654step0Labels := by
      have hz : ∀ j, raw31654 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31654step0 = (fun i j => raw31654 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31654step0 raw31654; decide +kernel
      have hl : raw31654step0Labels = raw31654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31654 raw31654Labels permutation434 hz
    mixedMoment B raw31654step0 raw31654step0Labels = mixedMoment B raw31654step1 raw31654step1Labels := by
      have ha : raw31654step1 = (fun i j => raw31654step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31654step1 raw31654step0; decide +kernel
      have hl : raw31654step1Labels = raw31654step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31654step0 raw31654step0Labels permutation113 permutation6
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw31655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31655step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw31655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31655 raw31655Labels = mixedMoment B node3082 node3082Labels := by
  calc
    mixedMoment B raw31655 raw31655Labels = mixedMoment B raw31655step0 raw31655step0Labels := by
      have hz : ∀ j, raw31655 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31655step0 = (fun i j => raw31655 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31655step0 raw31655; decide +kernel
      have hl : raw31655step0Labels = raw31655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31655 raw31655Labels permutation434 hz
    mixedMoment B raw31655step0 raw31655step0Labels = mixedMoment B raw31655step1 raw31655step1Labels := by
      have ha : raw31655step1 = (fun i j => raw31655step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31655step1 raw31655step0; decide +kernel
      have hl : raw31655step1Labels = raw31655step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31655step0 raw31655step0Labels permutation113 permutation6
    _ = mixedMoment B node3082 node3082Labels := by rfl

def raw31656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31656step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31656 raw31656Labels = mixedMoment B node3033 node3033Labels := by
  calc
    mixedMoment B raw31656 raw31656Labels = mixedMoment B raw31656step0 raw31656step0Labels := by
      have hz : ∀ j, raw31656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31656step0 = (fun i j => raw31656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31656step0 raw31656; decide +kernel
      have hl : raw31656step0Labels = raw31656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31656 raw31656Labels permutation346 hz
    mixedMoment B raw31656step0 raw31656step0Labels = mixedMoment B raw31656step1 raw31656step1Labels := by
      have ha : raw31656step1 = (fun i j => raw31656step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31656step1 raw31656step0; decide +kernel
      have hl : raw31656step1Labels = raw31656step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31656step0 raw31656step0Labels permutation113 permutation6
    _ = mixedMoment B node3033 node3033Labels := by rfl

def raw31657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31657 raw31657Labels = mixedMoment B node3062 node3062Labels := by
  calc
    mixedMoment B raw31657 raw31657Labels = mixedMoment B raw31657step0 raw31657step0Labels := by
      have ha : raw31657step0 = (fun i j => raw31657 (permutation533 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31657step0 raw31657; decide +kernel
      have hl : raw31657step0Labels = raw31657Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31657 raw31657Labels permutation533 permutation6
    _ = mixedMoment B node3062 node3062Labels := by rfl

def raw31658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw31658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31658 raw31658Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw31658 raw31658Labels = mixedMoment B raw31658step0 raw31658step0Labels := by
      have hz : ∀ j, raw31658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31658step0 = (fun i j => raw31658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31658step0 raw31658; decide +kernel
      have hl : raw31658step0Labels = raw31658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31658 raw31658Labels permutation346 hz
    mixedMoment B raw31658step0 raw31658step0Labels = mixedMoment B raw31658step1 raw31658step1Labels := by
      have ha : raw31658step1 = (fun i j => raw31658step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31658step1 raw31658step0; decide +kernel
      have hl : raw31658step1Labels = raw31658step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31658step0 raw31658step0Labels permutation113 permutation6
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw31659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31659step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw31659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31659 raw31659Labels = mixedMoment B node3082 node3082Labels := by
  calc
    mixedMoment B raw31659 raw31659Labels = mixedMoment B raw31659step0 raw31659step0Labels := by
      have hz : ∀ j, raw31659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31659step0 = (fun i j => raw31659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31659step0 raw31659; decide +kernel
      have hl : raw31659step0Labels = raw31659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31659 raw31659Labels permutation346 hz
    mixedMoment B raw31659step0 raw31659step0Labels = mixedMoment B raw31659step1 raw31659step1Labels := by
      have ha : raw31659step1 = (fun i j => raw31659step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31659step1 raw31659step0; decide +kernel
      have hl : raw31659step1Labels = raw31659step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31659step0 raw31659step0Labels permutation113 permutation6
    _ = mixedMoment B node3082 node3082Labels := by rfl

def raw31660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31660step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, 0, -2], ![3, -3, 0]]
def raw31660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31660 raw31660Labels = mixedMoment B node3145 node3145Labels := by
  calc
    mixedMoment B raw31660 raw31660Labels = mixedMoment B raw31660step0 raw31660step0Labels := by
      have hz : ∀ j, raw31660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31660step0 = (fun i j => raw31660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31660step0 raw31660; decide +kernel
      have hl : raw31660step0Labels = raw31660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31660 raw31660Labels permutation434 hz
    mixedMoment B raw31660step0 raw31660step0Labels = mixedMoment B raw31660step1 raw31660step1Labels := by
      have hz : ∀ j, raw31660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31660step1 = (fun i j => raw31660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31660step1 raw31660step0; decide +kernel
      have hl : raw31660step1Labels = raw31660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31660step0 raw31660step0Labels permutation80 hz
    mixedMoment B raw31660step1 raw31660step1Labels = mixedMoment B raw31660step2 raw31660step2Labels := by
      have ha : raw31660step2 = (fun i j => raw31660step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31660step2 raw31660step1; decide +kernel
      have hl : raw31660step2Labels = raw31660step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31660step1 raw31660step1Labels permutation9 permutation3
    _ = mixedMoment B node3145 node3145Labels := by rfl

def raw31661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31661 raw31661Labels = mixedMoment B node3143 node3143Labels := by
  calc
    mixedMoment B raw31661 raw31661Labels = mixedMoment B raw31661step0 raw31661step0Labels := by
      have hz : ∀ j, raw31661 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31661step0 = (fun i j => raw31661 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31661step0 raw31661; decide +kernel
      have hl : raw31661step0Labels = raw31661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31661 raw31661Labels permutation434 hz
    mixedMoment B raw31661step0 raw31661step0Labels = mixedMoment B raw31661step1 raw31661step1Labels := by
      have ha : raw31661step1 = (fun i j => raw31661step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31661step1 raw31661step0; decide +kernel
      have hl : raw31661step1Labels = raw31661step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31661step0 raw31661step0Labels permutation125 permutation3
    mixedMoment B raw31661step1 raw31661step1Labels = mixedMoment B raw31661step2 raw31661step2Labels := by
      have ha : raw31661step2 = -raw31661step1 := by apply Matrix.ext; change ∀ i j, raw31661step2 i j = -(raw31661step1 i j); unfold raw31661step2 raw31661step1; decide +kernel
      have hl : raw31661step2Labels = raw31661step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3143 node3143Labels := by rfl

def raw31662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31662 raw31662Labels = mixedMoment B node3143 node3143Labels := by
  calc
    mixedMoment B raw31662 raw31662Labels = mixedMoment B raw31662step0 raw31662step0Labels := by
      have hz : ∀ j, raw31662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31662step0 = (fun i j => raw31662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31662step0 raw31662; decide +kernel
      have hl : raw31662step0Labels = raw31662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31662 raw31662Labels permutation346 hz
    mixedMoment B raw31662step0 raw31662step0Labels = mixedMoment B raw31662step1 raw31662step1Labels := by
      have ha : raw31662step1 = (fun i j => raw31662step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31662step1 raw31662step0; decide +kernel
      have hl : raw31662step1Labels = raw31662step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31662step0 raw31662step0Labels permutation125 permutation3
    mixedMoment B raw31662step1 raw31662step1Labels = mixedMoment B raw31662step2 raw31662step2Labels := by
      have ha : raw31662step2 = -raw31662step1 := by apply Matrix.ext; change ∀ i j, raw31662step2 i j = -(raw31662step1 i j); unfold raw31662step2 raw31662step1; decide +kernel
      have hl : raw31662step2Labels = raw31662step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3143 node3143Labels := by rfl

def raw31663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31663step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def raw31663step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31663 raw31663Labels = mixedMoment B node3215 node3215Labels := by
  calc
    mixedMoment B raw31663 raw31663Labels = mixedMoment B raw31663step0 raw31663step0Labels := by
      have hz : ∀ j, raw31663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31663step0 = (fun i j => raw31663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31663step0 raw31663; decide +kernel
      have hl : raw31663step0Labels = raw31663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31663 raw31663Labels permutation434 hz
    mixedMoment B raw31663step0 raw31663step0Labels = mixedMoment B raw31663step1 raw31663step1Labels := by
      have hz : ∀ j, raw31663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31663step1 = (fun i j => raw31663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31663step1 raw31663step0; decide +kernel
      have hl : raw31663step1Labels = raw31663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31663step0 raw31663step0Labels permutation80 hz
    mixedMoment B raw31663step1 raw31663step1Labels = mixedMoment B raw31663step2 raw31663step2Labels := by
      have ha : raw31663step2 = (fun i j => raw31663step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31663step2 raw31663step1; decide +kernel
      have hl : raw31663step2Labels = raw31663step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31663step1 raw31663step1Labels permutation9 permutation3
    _ = mixedMoment B node3215 node3215Labels := by rfl

def raw31664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31664step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31664step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31664 raw31664Labels = mixedMoment B node1832 node1832Labels := by
  calc
    mixedMoment B raw31664 raw31664Labels = mixedMoment B raw31664step0 raw31664step0Labels := by
      have hz : ∀ j, raw31664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31664step0 = (fun i j => raw31664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31664step0 raw31664; decide +kernel
      have hl : raw31664step0Labels = raw31664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31664 raw31664Labels permutation434 hz
    mixedMoment B raw31664step0 raw31664step0Labels = mixedMoment B raw31664step1 raw31664step1Labels := by
      have hz : ∀ j, raw31664step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31664step1 = (fun i j => raw31664step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31664step1 raw31664step0; decide +kernel
      have hl : raw31664step1Labels = raw31664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31664step0 raw31664step0Labels permutation80 hz
    mixedMoment B raw31664step1 raw31664step1Labels = mixedMoment B raw31664step2 raw31664step2Labels := by
      have ha : raw31664step2 = (fun i j => raw31664step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31664step2 raw31664step1; decide +kernel
      have hl : raw31664step2Labels = raw31664step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31664step1 raw31664step1Labels permutation31 permutation3
    mixedMoment B raw31664step2 raw31664step2Labels = mixedMoment B raw31664step3 raw31664step3Labels := by
      have ha : raw31664step3 = -raw31664step2 := by apply Matrix.ext; change ∀ i j, raw31664step3 i j = -(raw31664step2 i j); unfold raw31664step3 raw31664step2; decide +kernel
      have hl : raw31664step3Labels = raw31664step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1832 node1832Labels := by rfl

def raw31665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31665step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31665 raw31665Labels = mixedMoment B node1828 node1828Labels := by
  calc
    mixedMoment B raw31665 raw31665Labels = mixedMoment B raw31665step0 raw31665step0Labels := by
      have hz : ∀ j, raw31665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31665step0 = (fun i j => raw31665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31665step0 raw31665; decide +kernel
      have hl : raw31665step0Labels = raw31665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31665 raw31665Labels permutation434 hz
    mixedMoment B raw31665step0 raw31665step0Labels = mixedMoment B raw31665step1 raw31665step1Labels := by
      have ha : raw31665step1 = (fun i j => raw31665step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31665step1 raw31665step0; decide +kernel
      have hl : raw31665step1Labels = raw31665step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31665step0 raw31665step0Labels permutation149 permutation3
    mixedMoment B raw31665step1 raw31665step1Labels = mixedMoment B raw31665step2 raw31665step2Labels := by
      have ha : raw31665step2 = -raw31665step1 := by apply Matrix.ext; change ∀ i j, raw31665step2 i j = -(raw31665step1 i j); unfold raw31665step2 raw31665step1; decide +kernel
      have hl : raw31665step2Labels = raw31665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1828 node1828Labels := by rfl

def raw31666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31666step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31666 raw31666Labels = mixedMoment B node1828 node1828Labels := by
  calc
    mixedMoment B raw31666 raw31666Labels = mixedMoment B raw31666step0 raw31666step0Labels := by
      have hz : ∀ j, raw31666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31666step0 = (fun i j => raw31666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31666step0 raw31666; decide +kernel
      have hl : raw31666step0Labels = raw31666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31666 raw31666Labels permutation346 hz
    mixedMoment B raw31666step0 raw31666step0Labels = mixedMoment B raw31666step1 raw31666step1Labels := by
      have ha : raw31666step1 = (fun i j => raw31666step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31666step1 raw31666step0; decide +kernel
      have hl : raw31666step1Labels = raw31666step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31666step0 raw31666step0Labels permutation149 permutation3
    mixedMoment B raw31666step1 raw31666step1Labels = mixedMoment B raw31666step2 raw31666step2Labels := by
      have ha : raw31666step2 = -raw31666step1 := by apply Matrix.ext; change ∀ i j, raw31666step2 i j = -(raw31666step1 i j); unfold raw31666step2 raw31666step1; decide +kernel
      have hl : raw31666step2Labels = raw31666step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1828 node1828Labels := by rfl

def raw31667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31667Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31667step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31667step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw31667step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw31667step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31667 raw31667Labels = mixedMoment B node2680 node2680Labels := by
  calc
    mixedMoment B raw31667 raw31667Labels = mixedMoment B raw31667step0 raw31667step0Labels := by
      have hz : ∀ j, raw31667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31667step0 = (fun i j => raw31667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31667step0 raw31667; decide +kernel
      have hl : raw31667step0Labels = raw31667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31667 raw31667Labels permutation434 hz
    mixedMoment B raw31667step0 raw31667step0Labels = mixedMoment B raw31667step1 raw31667step1Labels := by
      have hz : ∀ j, raw31667step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31667step1 = (fun i j => raw31667step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31667step1 raw31667step0; decide +kernel
      have hl : raw31667step1Labels = raw31667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31667step0 raw31667step0Labels permutation80 hz
    mixedMoment B raw31667step1 raw31667step1Labels = mixedMoment B raw31667step2 raw31667step2Labels := by
      have ha : raw31667step2 = (fun i j => raw31667step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31667step2 raw31667step1; decide +kernel
      have hl : raw31667step2Labels = raw31667step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31667step1 raw31667step1Labels permutation25 permutation7
    mixedMoment B raw31667step2 raw31667step2Labels = mixedMoment B raw31667step3 raw31667step3Labels := by
      have ha : raw31667step3 = raw31667step2 := by apply Matrix.ext; unfold raw31667step3 raw31667step2; decide +kernel
      have hl : raw31667step2Labels = labelEmbedding1 ∘ raw31667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31667step2 raw31667step2Labels raw31667step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2680 node2680Labels := by rfl

def raw31668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31668Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31668step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31668step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31668 raw31668Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw31668 raw31668Labels = mixedMoment B raw31668step0 raw31668step0Labels := by
      have hz : ∀ j, raw31668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31668step0 = (fun i j => raw31668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31668step0 raw31668; decide +kernel
      have hl : raw31668step0Labels = raw31668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31668 raw31668Labels permutation434 hz
    mixedMoment B raw31668step0 raw31668step0Labels = mixedMoment B raw31668step1 raw31668step1Labels := by
      have ha : raw31668step1 = (fun i j => raw31668step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31668step1 raw31668step0; decide +kernel
      have hl : raw31668step1Labels = raw31668step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31668step0 raw31668step0Labels permutation125 permutation7
    mixedMoment B raw31668step1 raw31668step1Labels = mixedMoment B raw31668step2 raw31668step2Labels := by
      have ha : raw31668step2 = raw31668step1 := by apply Matrix.ext; unfold raw31668step2 raw31668step1; decide +kernel
      have hl : raw31668step1Labels = labelEmbedding1 ∘ raw31668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31668step1 raw31668step1Labels raw31668step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw31669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31669Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31669step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31669step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31669 raw31669Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw31669 raw31669Labels = mixedMoment B raw31669step0 raw31669step0Labels := by
      have hz : ∀ j, raw31669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31669step0 = (fun i j => raw31669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31669step0 raw31669; decide +kernel
      have hl : raw31669step0Labels = raw31669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31669 raw31669Labels permutation346 hz
    mixedMoment B raw31669step0 raw31669step0Labels = mixedMoment B raw31669step1 raw31669step1Labels := by
      have ha : raw31669step1 = (fun i j => raw31669step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31669step1 raw31669step0; decide +kernel
      have hl : raw31669step1Labels = raw31669step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31669step0 raw31669step0Labels permutation125 permutation7
    mixedMoment B raw31669step1 raw31669step1Labels = mixedMoment B raw31669step2 raw31669step2Labels := by
      have ha : raw31669step2 = raw31669step1 := by apply Matrix.ext; unfold raw31669step2 raw31669step1; decide +kernel
      have hl : raw31669step1Labels = labelEmbedding1 ∘ raw31669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31669step1 raw31669step1Labels raw31669step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw31670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31670Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31670step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31670step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31670step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw31670step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31670step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw31670step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31670step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw31670step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31670 raw31670Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw31670 raw31670Labels = mixedMoment B raw31670step0 raw31670step0Labels := by
      have hz : ∀ j, raw31670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31670step0 = (fun i j => raw31670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31670step0 raw31670; decide +kernel
      have hl : raw31670step0Labels = raw31670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31670 raw31670Labels permutation434 hz
    mixedMoment B raw31670step0 raw31670step0Labels = mixedMoment B raw31670step1 raw31670step1Labels := by
      have hz : ∀ j, raw31670step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31670step1 = (fun i j => raw31670step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31670step1 raw31670step0; decide +kernel
      have hl : raw31670step1Labels = raw31670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31670step0 raw31670step0Labels permutation80 hz
    mixedMoment B raw31670step1 raw31670step1Labels = mixedMoment B raw31670step2 raw31670step2Labels := by
      have ha : raw31670step2 = (fun i j => raw31670step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31670step2 raw31670step1; decide +kernel
      have hl : raw31670step2Labels = raw31670step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31670step1 raw31670step1Labels permutation9 permutation7
    mixedMoment B raw31670step2 raw31670step2Labels = mixedMoment B raw31670step3 raw31670step3Labels := by
      have ha : raw31670step3 = -raw31670step2 := by apply Matrix.ext; change ∀ i j, raw31670step3 i j = -(raw31670step2 i j); unfold raw31670step3 raw31670step2; decide +kernel
      have hl : raw31670step3Labels = raw31670step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31670step3 raw31670step3Labels = mixedMoment B raw31670step4 raw31670step4Labels := by
      have ha : raw31670step4 = raw31670step3 := by apply Matrix.ext; unfold raw31670step4 raw31670step3; decide +kernel
      have hl : raw31670step3Labels = labelEmbedding1 ∘ raw31670step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31670step3 raw31670step3Labels raw31670step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw31671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31671Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31671step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31671step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw31671step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31671step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw31671step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31671 raw31671Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw31671 raw31671Labels = mixedMoment B raw31671step0 raw31671step0Labels := by
      have hz : ∀ j, raw31671 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31671step0 = (fun i j => raw31671 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31671step0 raw31671; decide +kernel
      have hl : raw31671step0Labels = raw31671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31671 raw31671Labels permutation434 hz
    mixedMoment B raw31671step0 raw31671step0Labels = mixedMoment B raw31671step1 raw31671step1Labels := by
      have hz : ∀ j, raw31671step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31671step1 = (fun i j => raw31671step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31671step1 raw31671step0; decide +kernel
      have hl : raw31671step1Labels = raw31671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31671step0 raw31671step0Labels permutation80 hz
    mixedMoment B raw31671step1 raw31671step1Labels = mixedMoment B raw31671step2 raw31671step2Labels := by
      have ha : raw31671step2 = (fun i j => raw31671step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31671step2 raw31671step1; decide +kernel
      have hl : raw31671step2Labels = raw31671step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31671step1 raw31671step1Labels permutation25 permutation7
    mixedMoment B raw31671step2 raw31671step2Labels = mixedMoment B raw31671step3 raw31671step3Labels := by
      have ha : raw31671step3 = raw31671step2 := by apply Matrix.ext; unfold raw31671step3 raw31671step2; decide +kernel
      have hl : raw31671step2Labels = labelEmbedding1 ∘ raw31671step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31671step2 raw31671step2Labels raw31671step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw31672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31672Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31672step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31672step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31672step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 1, -3], ![2, -2, 0]]
def raw31672step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31672step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw31672step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31672step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw31672step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31672step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw31672step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31672 raw31672Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw31672 raw31672Labels = mixedMoment B raw31672step0 raw31672step0Labels := by
      have hz : ∀ j, raw31672 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31672step0 = (fun i j => raw31672 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31672step0 raw31672; decide +kernel
      have hl : raw31672step0Labels = raw31672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31672 raw31672Labels permutation434 hz
    mixedMoment B raw31672step0 raw31672step0Labels = mixedMoment B raw31672step1 raw31672step1Labels := by
      have hz : ∀ j, raw31672step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31672step1 = (fun i j => raw31672step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31672step1 raw31672step0; decide +kernel
      have hl : raw31672step1Labels = raw31672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31672step0 raw31672step0Labels permutation80 hz
    mixedMoment B raw31672step1 raw31672step1Labels = mixedMoment B raw31672step2 raw31672step2Labels := by
      have hz : ∀ j, raw31672step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw31672step2 = (fun i j => raw31672step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw31672step2 raw31672step1; decide +kernel
      have hl : raw31672step2Labels = raw31672step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31672step1 raw31672step1Labels permutation14 hz
    mixedMoment B raw31672step2 raw31672step2Labels = mixedMoment B raw31672step3 raw31672step3Labels := by
      have ha : raw31672step3 = (fun i j => raw31672step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31672step3 raw31672step2; decide +kernel
      have hl : raw31672step3Labels = raw31672step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31672step2 raw31672step2Labels permutation3 permutation7
    mixedMoment B raw31672step3 raw31672step3Labels = mixedMoment B raw31672step4 raw31672step4Labels := by
      have ha : raw31672step4 = -raw31672step3 := by apply Matrix.ext; change ∀ i j, raw31672step4 i j = -(raw31672step3 i j); unfold raw31672step4 raw31672step3; decide +kernel
      have hl : raw31672step4Labels = raw31672step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31672step4 raw31672step4Labels = mixedMoment B raw31672step5 raw31672step5Labels := by
      have ha : raw31672step5 = raw31672step4 := by apply Matrix.ext; unfold raw31672step5 raw31672step4; decide +kernel
      have hl : raw31672step4Labels = labelEmbedding1 ∘ raw31672step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31672step4 raw31672step4Labels raw31672step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1741 node1741Labels := by rfl

def raw31673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31673Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31673step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw31673step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31673step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31673step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31673step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31673 raw31673Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw31673 raw31673Labels = mixedMoment B raw31673step0 raw31673step0Labels := by
      have hz : ∀ j, raw31673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31673step0 = (fun i j => raw31673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31673step0 raw31673; decide +kernel
      have hl : raw31673step0Labels = raw31673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31673 raw31673Labels permutation434 hz
    mixedMoment B raw31673step0 raw31673step0Labels = mixedMoment B raw31673step1 raw31673step1Labels := by
      have ha : raw31673step1 = (fun i j => raw31673step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31673step1 raw31673step0; decide +kernel
      have hl : raw31673step1Labels = raw31673step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31673step0 raw31673step0Labels permutation33 permutation7
    mixedMoment B raw31673step1 raw31673step1Labels = mixedMoment B raw31673step2 raw31673step2Labels := by
      have ha : raw31673step2 = -raw31673step1 := by apply Matrix.ext; change ∀ i j, raw31673step2 i j = -(raw31673step1 i j); unfold raw31673step2 raw31673step1; decide +kernel
      have hl : raw31673step2Labels = raw31673step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31673step2 raw31673step2Labels = mixedMoment B raw31673step3 raw31673step3Labels := by
      have ha : raw31673step3 = raw31673step2 := by apply Matrix.ext; unfold raw31673step3 raw31673step2; decide +kernel
      have hl : raw31673step2Labels = labelEmbedding1 ∘ raw31673step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31673step2 raw31673step2Labels raw31673step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2146 node2146Labels := by rfl

def raw31674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31674Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw31674step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31674step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31674step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31674 raw31674Labels = mixedMoment B node2171 node2171Labels := by
  calc
    mixedMoment B raw31674 raw31674Labels = mixedMoment B raw31674step0 raw31674step0Labels := by
      have ha : raw31674step0 = (fun i j => raw31674 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31674step0 raw31674; decide +kernel
      have hl : raw31674step0Labels = raw31674Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31674 raw31674Labels permutation159 permutation7
    mixedMoment B raw31674step0 raw31674step0Labels = mixedMoment B raw31674step1 raw31674step1Labels := by
      have ha : raw31674step1 = -raw31674step0 := by apply Matrix.ext; change ∀ i j, raw31674step1 i j = -(raw31674step0 i j); unfold raw31674step1 raw31674step0; decide +kernel
      have hl : raw31674step1Labels = raw31674step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31674step1 raw31674step1Labels = mixedMoment B raw31674step2 raw31674step2Labels := by
      have ha : raw31674step2 = raw31674step1 := by apply Matrix.ext; unfold raw31674step2 raw31674step1; decide +kernel
      have hl : raw31674step1Labels = labelEmbedding1 ∘ raw31674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31674step1 raw31674step1Labels raw31674step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2171 node2171Labels := by rfl

def raw31675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31675Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31675step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw31675step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw31675step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31675step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw31675step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31675 raw31675Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw31675 raw31675Labels = mixedMoment B raw31675step0 raw31675step0Labels := by
      have hz : ∀ j, raw31675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31675step0 = (fun i j => raw31675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31675step0 raw31675; decide +kernel
      have hl : raw31675step0Labels = raw31675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31675 raw31675Labels permutation434 hz
    mixedMoment B raw31675step0 raw31675step0Labels = mixedMoment B raw31675step1 raw31675step1Labels := by
      have ha : raw31675step1 = (fun i j => raw31675step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31675step1 raw31675step0; decide +kernel
      have hl : raw31675step1Labels = raw31675step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31675step0 raw31675step0Labels permutation33 permutation7
    mixedMoment B raw31675step1 raw31675step1Labels = mixedMoment B raw31675step2 raw31675step2Labels := by
      have ha : raw31675step2 = -raw31675step1 := by apply Matrix.ext; change ∀ i j, raw31675step2 i j = -(raw31675step1 i j); unfold raw31675step2 raw31675step1; decide +kernel
      have hl : raw31675step2Labels = raw31675step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31675step2 raw31675step2Labels = mixedMoment B raw31675step3 raw31675step3Labels := by
      have ha : raw31675step3 = raw31675step2 := by apply Matrix.ext; unfold raw31675step3 raw31675step2; decide +kernel
      have hl : raw31675step2Labels = labelEmbedding1 ∘ raw31675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31675step2 raw31675step2Labels raw31675step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw31676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31676Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31676step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw31676step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31676step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31676step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31676step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31676 raw31676Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw31676 raw31676Labels = mixedMoment B raw31676step0 raw31676step0Labels := by
      have hz : ∀ j, raw31676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31676step0 = (fun i j => raw31676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31676step0 raw31676; decide +kernel
      have hl : raw31676step0Labels = raw31676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31676 raw31676Labels permutation434 hz
    mixedMoment B raw31676step0 raw31676step0Labels = mixedMoment B raw31676step1 raw31676step1Labels := by
      have ha : raw31676step1 = (fun i j => raw31676step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31676step1 raw31676step0; decide +kernel
      have hl : raw31676step1Labels = raw31676step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31676step0 raw31676step0Labels permutation33 permutation7
    mixedMoment B raw31676step1 raw31676step1Labels = mixedMoment B raw31676step2 raw31676step2Labels := by
      have ha : raw31676step2 = -raw31676step1 := by apply Matrix.ext; change ∀ i j, raw31676step2 i j = -(raw31676step1 i j); unfold raw31676step2 raw31676step1; decide +kernel
      have hl : raw31676step2Labels = raw31676step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31676step2 raw31676step2Labels = mixedMoment B raw31676step3 raw31676step3Labels := by
      have ha : raw31676step3 = raw31676step2 := by apply Matrix.ext; unfold raw31676step3 raw31676step2; decide +kernel
      have hl : raw31676step2Labels = labelEmbedding1 ∘ raw31676step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31676step2 raw31676step2Labels raw31676step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw31677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31677Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31677step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw31677step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31677step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31677step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31677step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31677 raw31677Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw31677 raw31677Labels = mixedMoment B raw31677step0 raw31677step0Labels := by
      have hz : ∀ j, raw31677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31677step0 = (fun i j => raw31677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31677step0 raw31677; decide +kernel
      have hl : raw31677step0Labels = raw31677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31677 raw31677Labels permutation346 hz
    mixedMoment B raw31677step0 raw31677step0Labels = mixedMoment B raw31677step1 raw31677step1Labels := by
      have ha : raw31677step1 = (fun i j => raw31677step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31677step1 raw31677step0; decide +kernel
      have hl : raw31677step1Labels = raw31677step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31677step0 raw31677step0Labels permutation33 permutation7
    mixedMoment B raw31677step1 raw31677step1Labels = mixedMoment B raw31677step2 raw31677step2Labels := by
      have ha : raw31677step2 = -raw31677step1 := by apply Matrix.ext; change ∀ i j, raw31677step2 i j = -(raw31677step1 i j); unfold raw31677step2 raw31677step1; decide +kernel
      have hl : raw31677step2Labels = raw31677step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31677step2 raw31677step2Labels = mixedMoment B raw31677step3 raw31677step3Labels := by
      have ha : raw31677step3 = raw31677step2 := by apply Matrix.ext; unfold raw31677step3 raw31677step2; decide +kernel
      have hl : raw31677step2Labels = labelEmbedding1 ∘ raw31677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31677step2 raw31677step2Labels raw31677step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2146 node2146Labels := by rfl

def raw31678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31678Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw31678step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31678step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31678step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw31678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31678 raw31678Labels = mixedMoment B node2171 node2171Labels := by
  calc
    mixedMoment B raw31678 raw31678Labels = mixedMoment B raw31678step0 raw31678step0Labels := by
      have ha : raw31678step0 = (fun i j => raw31678 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31678step0 raw31678; decide +kernel
      have hl : raw31678step0Labels = raw31678Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31678 raw31678Labels permutation153 permutation7
    mixedMoment B raw31678step0 raw31678step0Labels = mixedMoment B raw31678step1 raw31678step1Labels := by
      have ha : raw31678step1 = -raw31678step0 := by apply Matrix.ext; change ∀ i j, raw31678step1 i j = -(raw31678step0 i j); unfold raw31678step1 raw31678step0; decide +kernel
      have hl : raw31678step1Labels = raw31678step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31678step1 raw31678step1Labels = mixedMoment B raw31678step2 raw31678step2Labels := by
      have ha : raw31678step2 = raw31678step1 := by apply Matrix.ext; unfold raw31678step2 raw31678step1; decide +kernel
      have hl : raw31678step1Labels = labelEmbedding1 ∘ raw31678step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31678step1 raw31678step1Labels raw31678step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2171 node2171Labels := by rfl

def raw31679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31679Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31679step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw31679step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw31679step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31679step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw31679step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31679 raw31679Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw31679 raw31679Labels = mixedMoment B raw31679step0 raw31679step0Labels := by
      have hz : ∀ j, raw31679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31679step0 = (fun i j => raw31679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31679step0 raw31679; decide +kernel
      have hl : raw31679step0Labels = raw31679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31679 raw31679Labels permutation346 hz
    mixedMoment B raw31679step0 raw31679step0Labels = mixedMoment B raw31679step1 raw31679step1Labels := by
      have ha : raw31679step1 = (fun i j => raw31679step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31679step1 raw31679step0; decide +kernel
      have hl : raw31679step1Labels = raw31679step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31679step0 raw31679step0Labels permutation33 permutation7
    mixedMoment B raw31679step1 raw31679step1Labels = mixedMoment B raw31679step2 raw31679step2Labels := by
      have ha : raw31679step2 = -raw31679step1 := by apply Matrix.ext; change ∀ i j, raw31679step2 i j = -(raw31679step1 i j); unfold raw31679step2 raw31679step1; decide +kernel
      have hl : raw31679step2Labels = raw31679step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31679step2 raw31679step2Labels = mixedMoment B raw31679step3 raw31679step3Labels := by
      have ha : raw31679step3 = raw31679step2 := by apply Matrix.ext; unfold raw31679step3 raw31679step2; decide +kernel
      have hl : raw31679step2Labels = labelEmbedding1 ∘ raw31679step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31679step2 raw31679step2Labels raw31679step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw31680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31680Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31680step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw31680step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31680step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31680step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw31680step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31680 raw31680Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw31680 raw31680Labels = mixedMoment B raw31680step0 raw31680step0Labels := by
      have hz : ∀ j, raw31680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31680step0 = (fun i j => raw31680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31680step0 raw31680; decide +kernel
      have hl : raw31680step0Labels = raw31680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31680 raw31680Labels permutation346 hz
    mixedMoment B raw31680step0 raw31680step0Labels = mixedMoment B raw31680step1 raw31680step1Labels := by
      have ha : raw31680step1 = (fun i j => raw31680step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31680step1 raw31680step0; decide +kernel
      have hl : raw31680step1Labels = raw31680step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31680step0 raw31680step0Labels permutation33 permutation7
    mixedMoment B raw31680step1 raw31680step1Labels = mixedMoment B raw31680step2 raw31680step2Labels := by
      have ha : raw31680step2 = -raw31680step1 := by apply Matrix.ext; change ∀ i j, raw31680step2 i j = -(raw31680step1 i j); unfold raw31680step2 raw31680step1; decide +kernel
      have hl : raw31680step2Labels = raw31680step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31680step2 raw31680step2Labels = mixedMoment B raw31680step3 raw31680step3Labels := by
      have ha : raw31680step3 = raw31680step2 := by apply Matrix.ext; unfold raw31680step3 raw31680step2; decide +kernel
      have hl : raw31680step2Labels = labelEmbedding1 ∘ raw31680step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31680step2 raw31680step2Labels raw31680step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw31681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31681Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31681step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31681step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw31681step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31681step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw31681step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31681 raw31681Labels = mixedMoment B node2159 node2159Labels := by
  calc
    mixedMoment B raw31681 raw31681Labels = mixedMoment B raw31681step0 raw31681step0Labels := by
      have hz : ∀ j, raw31681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31681step0 = (fun i j => raw31681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31681step0 raw31681; decide +kernel
      have hl : raw31681step0Labels = raw31681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31681 raw31681Labels permutation434 hz
    mixedMoment B raw31681step0 raw31681step0Labels = mixedMoment B raw31681step1 raw31681step1Labels := by
      have hz : ∀ j, raw31681step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31681step1 = (fun i j => raw31681step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31681step1 raw31681step0; decide +kernel
      have hl : raw31681step1Labels = raw31681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31681step0 raw31681step0Labels permutation80 hz
    mixedMoment B raw31681step1 raw31681step1Labels = mixedMoment B raw31681step2 raw31681step2Labels := by
      have ha : raw31681step2 = (fun i j => raw31681step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31681step2 raw31681step1; decide +kernel
      have hl : raw31681step2Labels = raw31681step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31681step1 raw31681step1Labels permutation25 permutation7
    mixedMoment B raw31681step2 raw31681step2Labels = mixedMoment B raw31681step3 raw31681step3Labels := by
      have ha : raw31681step3 = raw31681step2 := by apply Matrix.ext; unfold raw31681step3 raw31681step2; decide +kernel
      have hl : raw31681step2Labels = labelEmbedding1 ∘ raw31681step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31681step2 raw31681step2Labels raw31681step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2159 node2159Labels := by rfl

def raw31682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31682Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31682step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw31682step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw31682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31682 raw31682Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw31682 raw31682Labels = mixedMoment B raw31682step0 raw31682step0Labels := by
      have hz : ∀ j, raw31682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31682step0 = (fun i j => raw31682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31682step0 raw31682; decide +kernel
      have hl : raw31682step0Labels = raw31682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31682 raw31682Labels permutation434 hz
    mixedMoment B raw31682step0 raw31682step0Labels = mixedMoment B raw31682step1 raw31682step1Labels := by
      have ha : raw31682step1 = (fun i j => raw31682step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31682step1 raw31682step0; decide +kernel
      have hl : raw31682step1Labels = raw31682step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31682step0 raw31682step0Labels permutation125 permutation7
    mixedMoment B raw31682step1 raw31682step1Labels = mixedMoment B raw31682step2 raw31682step2Labels := by
      have ha : raw31682step2 = raw31682step1 := by apply Matrix.ext; unfold raw31682step2 raw31682step1; decide +kernel
      have hl : raw31682step1Labels = labelEmbedding1 ∘ raw31682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31682step1 raw31682step1Labels raw31682step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

def raw31683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31683Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31683step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw31683step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw31683step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31683 raw31683Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw31683 raw31683Labels = mixedMoment B raw31683step0 raw31683step0Labels := by
      have hz : ∀ j, raw31683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31683step0 = (fun i j => raw31683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31683step0 raw31683; decide +kernel
      have hl : raw31683step0Labels = raw31683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31683 raw31683Labels permutation346 hz
    mixedMoment B raw31683step0 raw31683step0Labels = mixedMoment B raw31683step1 raw31683step1Labels := by
      have ha : raw31683step1 = (fun i j => raw31683step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31683step1 raw31683step0; decide +kernel
      have hl : raw31683step1Labels = raw31683step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31683step0 raw31683step0Labels permutation125 permutation7
    mixedMoment B raw31683step1 raw31683step1Labels = mixedMoment B raw31683step2 raw31683step2Labels := by
      have ha : raw31683step2 = raw31683step1 := by apply Matrix.ext; unfold raw31683step2 raw31683step1; decide +kernel
      have hl : raw31683step1Labels = labelEmbedding1 ∘ raw31683step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31683step1 raw31683step1Labels raw31683step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

def raw31684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31684Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31684step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![3, 0, -3], ![1, -1, 0]]
def raw31684step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw31684step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw31684step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31684 raw31684Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw31684 raw31684Labels = mixedMoment B raw31684step0 raw31684step0Labels := by
      have hz : ∀ j, raw31684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31684step0 = (fun i j => raw31684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31684step0 raw31684; decide +kernel
      have hl : raw31684step0Labels = raw31684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31684 raw31684Labels permutation434 hz
    mixedMoment B raw31684step0 raw31684step0Labels = mixedMoment B raw31684step1 raw31684step1Labels := by
      have hz : ∀ j, raw31684step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31684step1 = (fun i j => raw31684step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31684step1 raw31684step0; decide +kernel
      have hl : raw31684step1Labels = raw31684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31684step0 raw31684step0Labels permutation80 hz
    mixedMoment B raw31684step1 raw31684step1Labels = mixedMoment B raw31684step2 raw31684step2Labels := by
      have ha : raw31684step2 = (fun i j => raw31684step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31684step2 raw31684step1; decide +kernel
      have hl : raw31684step2Labels = raw31684step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31684step1 raw31684step1Labels permutation25 permutation7
    mixedMoment B raw31684step2 raw31684step2Labels = mixedMoment B raw31684step3 raw31684step3Labels := by
      have ha : raw31684step3 = raw31684step2 := by apply Matrix.ext; unfold raw31684step3 raw31684step2; decide +kernel
      have hl : raw31684step2Labels = labelEmbedding1 ∘ raw31684step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31684step2 raw31684step2Labels raw31684step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

def raw31685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31685Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31685step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31685step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-3, 1, 2]]
def raw31685step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31685step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw31685step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31685step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw31685step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31685 raw31685Labels = mixedMoment B node2163 node2163Labels := by
  calc
    mixedMoment B raw31685 raw31685Labels = mixedMoment B raw31685step0 raw31685step0Labels := by
      have hz : ∀ j, raw31685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31685step0 = (fun i j => raw31685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31685step0 raw31685; decide +kernel
      have hl : raw31685step0Labels = raw31685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31685 raw31685Labels permutation434 hz
    mixedMoment B raw31685step0 raw31685step0Labels = mixedMoment B raw31685step1 raw31685step1Labels := by
      have hz : ∀ j, raw31685step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31685step1 = (fun i j => raw31685step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31685step1 raw31685step0; decide +kernel
      have hl : raw31685step1Labels = raw31685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31685step0 raw31685step0Labels permutation80 hz
    mixedMoment B raw31685step1 raw31685step1Labels = mixedMoment B raw31685step2 raw31685step2Labels := by
      have ha : raw31685step2 = (fun i j => raw31685step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31685step2 raw31685step1; decide +kernel
      have hl : raw31685step2Labels = raw31685step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31685step1 raw31685step1Labels permutation9 permutation7
    mixedMoment B raw31685step2 raw31685step2Labels = mixedMoment B raw31685step3 raw31685step3Labels := by
      have ha : raw31685step3 = -raw31685step2 := by apply Matrix.ext; change ∀ i j, raw31685step3 i j = -(raw31685step2 i j); unfold raw31685step3 raw31685step2; decide +kernel
      have hl : raw31685step3Labels = raw31685step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31685step3 raw31685step3Labels = mixedMoment B raw31685step4 raw31685step4Labels := by
      have ha : raw31685step4 = raw31685step3 := by apply Matrix.ext; unfold raw31685step4 raw31685step3; decide +kernel
      have hl : raw31685step3Labels = labelEmbedding1 ∘ raw31685step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31685step3 raw31685step3Labels raw31685step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2163 node2163Labels := by rfl

def raw31686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31686Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31686step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw31686step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw31686step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31686step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw31686step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31686 raw31686Labels = mixedMoment B node2180 node2180Labels := by
  calc
    mixedMoment B raw31686 raw31686Labels = mixedMoment B raw31686step0 raw31686step0Labels := by
      have hz : ∀ j, raw31686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31686step0 = (fun i j => raw31686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31686step0 raw31686; decide +kernel
      have hl : raw31686step0Labels = raw31686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31686 raw31686Labels permutation434 hz
    mixedMoment B raw31686step0 raw31686step0Labels = mixedMoment B raw31686step1 raw31686step1Labels := by
      have ha : raw31686step1 = (fun i j => raw31686step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31686step1 raw31686step0; decide +kernel
      have hl : raw31686step1Labels = raw31686step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31686step0 raw31686step0Labels permutation33 permutation7
    mixedMoment B raw31686step1 raw31686step1Labels = mixedMoment B raw31686step2 raw31686step2Labels := by
      have ha : raw31686step2 = -raw31686step1 := by apply Matrix.ext; change ∀ i j, raw31686step2 i j = -(raw31686step1 i j); unfold raw31686step2 raw31686step1; decide +kernel
      have hl : raw31686step2Labels = raw31686step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31686step2 raw31686step2Labels = mixedMoment B raw31686step3 raw31686step3Labels := by
      have ha : raw31686step3 = raw31686step2 := by apply Matrix.ext; unfold raw31686step3 raw31686step2; decide +kernel
      have hl : raw31686step2Labels = labelEmbedding1 ∘ raw31686step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31686step2 raw31686step2Labels raw31686step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2180 node2180Labels := by rfl

def raw31687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31687Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw31687step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw31687step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw31687step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31687step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw31687step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31687 raw31687Labels = mixedMoment B node2180 node2180Labels := by
  calc
    mixedMoment B raw31687 raw31687Labels = mixedMoment B raw31687step0 raw31687step0Labels := by
      have hz : ∀ j, raw31687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31687step0 = (fun i j => raw31687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31687step0 raw31687; decide +kernel
      have hl : raw31687step0Labels = raw31687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31687 raw31687Labels permutation346 hz
    mixedMoment B raw31687step0 raw31687step0Labels = mixedMoment B raw31687step1 raw31687step1Labels := by
      have ha : raw31687step1 = (fun i j => raw31687step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31687step1 raw31687step0; decide +kernel
      have hl : raw31687step1Labels = raw31687step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31687step0 raw31687step0Labels permutation33 permutation7
    mixedMoment B raw31687step1 raw31687step1Labels = mixedMoment B raw31687step2 raw31687step2Labels := by
      have ha : raw31687step2 = -raw31687step1 := by apply Matrix.ext; change ∀ i j, raw31687step2 i j = -(raw31687step1 i j); unfold raw31687step2 raw31687step1; decide +kernel
      have hl : raw31687step2Labels = raw31687step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31687step2 raw31687step2Labels = mixedMoment B raw31687step3 raw31687step3Labels := by
      have ha : raw31687step3 = raw31687step2 := by apply Matrix.ext; unfold raw31687step3 raw31687step2; decide +kernel
      have hl : raw31687step2Labels = labelEmbedding1 ∘ raw31687step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31687step2 raw31687step2Labels raw31687step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2180 node2180Labels := by rfl

def raw31688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw31688Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw31688step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw31688step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31688step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw31688step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31688step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw31688step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31688step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw31688step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31688 raw31688Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw31688 raw31688Labels = mixedMoment B raw31688step0 raw31688step0Labels := by
      have hz : ∀ j, raw31688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31688step0 = (fun i j => raw31688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31688step0 raw31688; decide +kernel
      have hl : raw31688step0Labels = raw31688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31688 raw31688Labels permutation434 hz
    mixedMoment B raw31688step0 raw31688step0Labels = mixedMoment B raw31688step1 raw31688step1Labels := by
      have hz : ∀ j, raw31688step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31688step1 = (fun i j => raw31688step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31688step1 raw31688step0; decide +kernel
      have hl : raw31688step1Labels = raw31688step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31688step0 raw31688step0Labels permutation80 hz
    mixedMoment B raw31688step1 raw31688step1Labels = mixedMoment B raw31688step2 raw31688step2Labels := by
      have ha : raw31688step2 = (fun i j => raw31688step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31688step2 raw31688step1; decide +kernel
      have hl : raw31688step2Labels = raw31688step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31688step1 raw31688step1Labels permutation9 permutation7
    mixedMoment B raw31688step2 raw31688step2Labels = mixedMoment B raw31688step3 raw31688step3Labels := by
      have ha : raw31688step3 = -raw31688step2 := by apply Matrix.ext; change ∀ i j, raw31688step3 i j = -(raw31688step2 i j); unfold raw31688step3 raw31688step2; decide +kernel
      have hl : raw31688step3Labels = raw31688step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31688step3 raw31688step3Labels = mixedMoment B raw31688step4 raw31688step4Labels := by
      have ha : raw31688step4 = raw31688step3 := by apply Matrix.ext; unfold raw31688step4 raw31688step3; decide +kernel
      have hl : raw31688step3Labels = labelEmbedding1 ∘ raw31688step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31688step3 raw31688step3Labels raw31688step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw31689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31689step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31689 raw31689Labels = mixedMoment B node3396 node3396Labels := by
  calc
    mixedMoment B raw31689 raw31689Labels = mixedMoment B raw31689step0 raw31689step0Labels := by
      have hz : ∀ j, raw31689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31689step0 = (fun i j => raw31689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31689step0 raw31689; decide +kernel
      have hl : raw31689step0Labels = raw31689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31689 raw31689Labels permutation434 hz
    mixedMoment B raw31689step0 raw31689step0Labels = mixedMoment B raw31689step1 raw31689step1Labels := by
      have hz : ∀ j, raw31689step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31689step1 = (fun i j => raw31689step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31689step1 raw31689step0; decide +kernel
      have hl : raw31689step1Labels = raw31689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31689step0 raw31689step0Labels permutation80 hz
    mixedMoment B raw31689step1 raw31689step1Labels = mixedMoment B raw31689step2 raw31689step2Labels := by
      have ha : raw31689step2 = (fun i j => raw31689step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31689step2 raw31689step1; decide +kernel
      have hl : raw31689step2Labels = raw31689step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31689step1 raw31689step1Labels permutation9 permutation2
    _ = mixedMoment B node3396 node3396Labels := by rfl

def raw31690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31690 raw31690Labels = mixedMoment B node1809 node1809Labels := by
  calc
    mixedMoment B raw31690 raw31690Labels = mixedMoment B raw31690step0 raw31690step0Labels := by
      have hz : ∀ j, raw31690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31690step0 = (fun i j => raw31690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31690step0 raw31690; decide +kernel
      have hl : raw31690step0Labels = raw31690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31690 raw31690Labels permutation434 hz
    mixedMoment B raw31690step0 raw31690step0Labels = mixedMoment B raw31690step1 raw31690step1Labels := by
      have ha : raw31690step1 = (fun i j => raw31690step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31690step1 raw31690step0; decide +kernel
      have hl : raw31690step1Labels = raw31690step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31690step0 raw31690step0Labels permutation33 permutation2
    _ = mixedMoment B node1809 node1809Labels := by rfl

def raw31691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31691 raw31691Labels = mixedMoment B node1809 node1809Labels := by
  calc
    mixedMoment B raw31691 raw31691Labels = mixedMoment B raw31691step0 raw31691step0Labels := by
      have hz : ∀ j, raw31691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31691step0 = (fun i j => raw31691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31691step0 raw31691; decide +kernel
      have hl : raw31691step0Labels = raw31691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31691 raw31691Labels permutation346 hz
    mixedMoment B raw31691step0 raw31691step0Labels = mixedMoment B raw31691step1 raw31691step1Labels := by
      have ha : raw31691step1 = (fun i j => raw31691step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31691step1 raw31691step0; decide +kernel
      have hl : raw31691step1Labels = raw31691step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31691step0 raw31691step0Labels permutation33 permutation2
    _ = mixedMoment B node1809 node1809Labels := by rfl

def raw31692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, 0, -3], ![2, -2, 0]]
def raw31692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw31692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31692 raw31692Labels = mixedMoment B node1817 node1817Labels := by
  calc
    mixedMoment B raw31692 raw31692Labels = mixedMoment B raw31692step0 raw31692step0Labels := by
      have hz : ∀ j, raw31692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31692step0 = (fun i j => raw31692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31692step0 raw31692; decide +kernel
      have hl : raw31692step0Labels = raw31692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31692 raw31692Labels permutation434 hz
    mixedMoment B raw31692step0 raw31692step0Labels = mixedMoment B raw31692step1 raw31692step1Labels := by
      have hz : ∀ j, raw31692step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31692step1 = (fun i j => raw31692step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31692step1 raw31692step0; decide +kernel
      have hl : raw31692step1Labels = raw31692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31692step0 raw31692step0Labels permutation80 hz
    mixedMoment B raw31692step1 raw31692step1Labels = mixedMoment B raw31692step2 raw31692step2Labels := by
      have ha : raw31692step2 = (fun i j => raw31692step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31692step2 raw31692step1; decide +kernel
      have hl : raw31692step2Labels = raw31692step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31692step1 raw31692step1Labels permutation9 permutation2
    _ = mixedMoment B node1817 node1817Labels := by rfl

def raw31693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31693 raw31693Labels = mixedMoment B node926 node926Labels := by
  calc
    mixedMoment B raw31693 raw31693Labels = mixedMoment B raw31693step0 raw31693step0Labels := by
      have hz : ∀ j, raw31693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31693step0 = (fun i j => raw31693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31693step0 raw31693; decide +kernel
      have hl : raw31693step0Labels = raw31693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31693 raw31693Labels permutation434 hz
    mixedMoment B raw31693step0 raw31693step0Labels = mixedMoment B raw31693step1 raw31693step1Labels := by
      have ha : raw31693step1 = (fun i j => raw31693step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31693step1 raw31693step0; decide +kernel
      have hl : raw31693step1Labels = raw31693step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31693step0 raw31693step0Labels permutation33 permutation2
    _ = mixedMoment B node926 node926Labels := by rfl

def raw31694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw31694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31694 raw31694Labels = mixedMoment B node1962 node1962Labels := by
  calc
    mixedMoment B raw31694 raw31694Labels = mixedMoment B raw31694step0 raw31694step0Labels := by
      have ha : raw31694step0 = (fun i j => raw31694 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31694step0 raw31694; decide +kernel
      have hl : raw31694step0Labels = raw31694Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31694 raw31694Labels permutation159 permutation2
    _ = mixedMoment B node1962 node1962Labels := by rfl

def raw31695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw31695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31695 raw31695Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw31695 raw31695Labels = mixedMoment B raw31695step0 raw31695step0Labels := by
      have hz : ∀ j, raw31695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31695step0 = (fun i j => raw31695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31695step0 raw31695; decide +kernel
      have hl : raw31695step0Labels = raw31695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31695 raw31695Labels permutation434 hz
    _ = mixedMoment B node2055 node2055Labels := by rfl

def raw31696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw31696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw31696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31696 raw31696Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw31696 raw31696Labels = mixedMoment B raw31696step0 raw31696step0Labels := by
      have hz : ∀ j, raw31696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31696step0 = (fun i j => raw31696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31696step0 raw31696; decide +kernel
      have hl : raw31696step0Labels = raw31696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31696 raw31696Labels permutation434 hz
    mixedMoment B raw31696step0 raw31696step0Labels = mixedMoment B raw31696step1 raw31696step1Labels := by
      have ha : raw31696step1 = (fun i j => raw31696step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31696step1 raw31696step0; decide +kernel
      have hl : raw31696step1Labels = raw31696step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31696step0 raw31696step0Labels permutation33 permutation2
    _ = mixedMoment B node2052 node2052Labels := by rfl

def raw31697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw31697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw31697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw31697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31697step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31697step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31697step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31697 raw31697Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw31697 raw31697Labels = mixedMoment B raw31697step0 raw31697step0Labels := by
      have hz : ∀ j, raw31697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31697step0 = (fun i j => raw31697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31697step0 raw31697; decide +kernel
      have hl : raw31697step0Labels = raw31697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31697 raw31697Labels permutation434 hz
    mixedMoment B raw31697step0 raw31697step0Labels = mixedMoment B raw31697step1 raw31697step1Labels := by
      have hz : ∀ j, raw31697step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31697step1 = (fun i j => raw31697step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31697step1 raw31697step0; decide +kernel
      have hl : raw31697step1Labels = raw31697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31697step0 raw31697step0Labels permutation80 hz
    mixedMoment B raw31697step1 raw31697step1Labels = mixedMoment B raw31697step2 raw31697step2Labels := by
      have ha : raw31697step2 = (fun i j => raw31697step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31697step2 raw31697step1; decide +kernel
      have hl : raw31697step2Labels = raw31697step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31697step1 raw31697step1Labels permutation8 permutation3
    mixedMoment B raw31697step2 raw31697step2Labels = mixedMoment B raw31697step3 raw31697step3Labels := by
      have ha : raw31697step3 = raw31697step2 := by apply Matrix.ext; unfold raw31697step3 raw31697step2; decide +kernel
      have hl : raw31697step2Labels = labelEmbedding6 ∘ raw31697step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31697step2 raw31697step2Labels raw31697step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw31698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw31698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31698step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31698 raw31698Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw31698 raw31698Labels = mixedMoment B raw31698step0 raw31698step0Labels := by
      have hz : ∀ j, raw31698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31698step0 = (fun i j => raw31698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31698step0 raw31698; decide +kernel
      have hl : raw31698step0Labels = raw31698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31698 raw31698Labels permutation434 hz
    mixedMoment B raw31698step0 raw31698step0Labels = mixedMoment B raw31698step1 raw31698step1Labels := by
      have hz : ∀ j, raw31698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31698step1 = (fun i j => raw31698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31698step1 raw31698step0; decide +kernel
      have hl : raw31698step1Labels = raw31698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31698step0 raw31698step0Labels permutation80 hz
    mixedMoment B raw31698step1 raw31698step1Labels = mixedMoment B raw31698step2 raw31698step2Labels := by
      have ha : raw31698step2 = (fun i j => raw31698step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31698step2 raw31698step1; decide +kernel
      have hl : raw31698step2Labels = raw31698step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31698step1 raw31698step1Labels permutation9 permutation3
    mixedMoment B raw31698step2 raw31698step2Labels = mixedMoment B raw31698step3 raw31698step3Labels := by
      have ha : raw31698step3 = raw31698step2 := by apply Matrix.ext; unfold raw31698step3 raw31698step2; decide +kernel
      have hl : raw31698step2Labels = labelEmbedding6 ∘ raw31698step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31698step2 raw31698step2Labels raw31698step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

def raw31699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31699step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31699 raw31699Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw31699 raw31699Labels = mixedMoment B raw31699step0 raw31699step0Labels := by
      have hz : ∀ j, raw31699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31699step0 = (fun i j => raw31699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31699step0 raw31699; decide +kernel
      have hl : raw31699step0Labels = raw31699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31699 raw31699Labels permutation434 hz
    mixedMoment B raw31699step0 raw31699step0Labels = mixedMoment B raw31699step1 raw31699step1Labels := by
      have ha : raw31699step1 = (fun i j => raw31699step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31699step1 raw31699step0; decide +kernel
      have hl : raw31699step1Labels = raw31699step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31699step0 raw31699step0Labels permutation39 permutation3
    mixedMoment B raw31699step1 raw31699step1Labels = mixedMoment B raw31699step2 raw31699step2Labels := by
      have ha : raw31699step2 = raw31699step1 := by apply Matrix.ext; unfold raw31699step2 raw31699step1; decide +kernel
      have hl : raw31699step1Labels = labelEmbedding6 ∘ raw31699step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31699step1 raw31699step1Labels raw31699step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

def raw31700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31700step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31700 raw31700Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw31700 raw31700Labels = mixedMoment B raw31700step0 raw31700step0Labels := by
      have hz : ∀ j, raw31700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31700step0 = (fun i j => raw31700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31700step0 raw31700; decide +kernel
      have hl : raw31700step0Labels = raw31700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31700 raw31700Labels permutation346 hz
    mixedMoment B raw31700step0 raw31700step0Labels = mixedMoment B raw31700step1 raw31700step1Labels := by
      have ha : raw31700step1 = (fun i j => raw31700step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31700step1 raw31700step0; decide +kernel
      have hl : raw31700step1Labels = raw31700step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31700step0 raw31700step0Labels permutation39 permutation3
    mixedMoment B raw31700step1 raw31700step1Labels = mixedMoment B raw31700step2 raw31700step2Labels := by
      have ha : raw31700step2 = raw31700step1 := by apply Matrix.ext; unfold raw31700step2 raw31700step1; decide +kernel
      have hl : raw31700step1Labels = labelEmbedding6 ∘ raw31700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31700step1 raw31700step1Labels raw31700step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

def raw31701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw31701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw31701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw31701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw31701step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw31701step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31701step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw31701step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31701step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31701 raw31701Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw31701 raw31701Labels = mixedMoment B raw31701step0 raw31701step0Labels := by
      have hz : ∀ j, raw31701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31701step0 = (fun i j => raw31701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31701step0 raw31701; decide +kernel
      have hl : raw31701step0Labels = raw31701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31701 raw31701Labels permutation434 hz
    mixedMoment B raw31701step0 raw31701step0Labels = mixedMoment B raw31701step1 raw31701step1Labels := by
      have hz : ∀ j, raw31701step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31701step1 = (fun i j => raw31701step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31701step1 raw31701step0; decide +kernel
      have hl : raw31701step1Labels = raw31701step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31701step0 raw31701step0Labels permutation80 hz
    mixedMoment B raw31701step1 raw31701step1Labels = mixedMoment B raw31701step2 raw31701step2Labels := by
      have ha : raw31701step2 = (fun i j => raw31701step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31701step2 raw31701step1; decide +kernel
      have hl : raw31701step2Labels = raw31701step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31701step1 raw31701step1Labels permutation12 permutation5
    mixedMoment B raw31701step2 raw31701step2Labels = mixedMoment B raw31701step3 raw31701step3Labels := by
      have ha : raw31701step3 = -raw31701step2 := by apply Matrix.ext; change ∀ i j, raw31701step3 i j = -(raw31701step2 i j); unfold raw31701step3 raw31701step2; decide +kernel
      have hl : raw31701step3Labels = raw31701step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31701step3 raw31701step3Labels = mixedMoment B raw31701step4 raw31701step4Labels := by
      have ha : raw31701step4 = raw31701step3 := by apply Matrix.ext; unfold raw31701step4 raw31701step3; decide +kernel
      have hl : raw31701step3Labels = labelEmbedding8 ∘ raw31701step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31701step3 raw31701step3Labels raw31701step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw31702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31702step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31702 raw31702Labels = mixedMoment B node4220 node4220Labels := by
  calc
    mixedMoment B raw31702 raw31702Labels = mixedMoment B raw31702step0 raw31702step0Labels := by
      have hz : ∀ j, raw31702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31702step0 = (fun i j => raw31702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31702step0 raw31702; decide +kernel
      have hl : raw31702step0Labels = raw31702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31702 raw31702Labels permutation434 hz
    mixedMoment B raw31702step0 raw31702step0Labels = mixedMoment B raw31702step1 raw31702step1Labels := by
      have ha : raw31702step1 = (fun i j => raw31702step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31702step1 raw31702step0; decide +kernel
      have hl : raw31702step1Labels = raw31702step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31702step0 raw31702step0Labels permutation33 permutation3
    mixedMoment B raw31702step1 raw31702step1Labels = mixedMoment B raw31702step2 raw31702step2Labels := by
      have ha : raw31702step2 = raw31702step1 := by apply Matrix.ext; unfold raw31702step2 raw31702step1; decide +kernel
      have hl : raw31702step1Labels = labelEmbedding6 ∘ raw31702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31702step1 raw31702step1Labels raw31702step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4220 node4220Labels := by rfl

def raw31703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31703step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31703step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31703 raw31703Labels = mixedMoment B node4651 node4651Labels := by
  calc
    mixedMoment B raw31703 raw31703Labels = mixedMoment B raw31703step0 raw31703step0Labels := by
      have hz : ∀ j, raw31703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31703step0 = (fun i j => raw31703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31703step0 raw31703; decide +kernel
      have hl : raw31703step0Labels = raw31703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31703 raw31703Labels permutation434 hz
    mixedMoment B raw31703step0 raw31703step0Labels = mixedMoment B raw31703step1 raw31703step1Labels := by
      have ha : raw31703step1 = (fun i j => raw31703step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31703step1 raw31703step0; decide +kernel
      have hl : raw31703step1Labels = raw31703step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31703step0 raw31703step0Labels permutation33 permutation3
    mixedMoment B raw31703step1 raw31703step1Labels = mixedMoment B raw31703step2 raw31703step2Labels := by
      have ha : raw31703step2 = raw31703step1 := by apply Matrix.ext; unfold raw31703step2 raw31703step1; decide +kernel
      have hl : raw31703step1Labels = labelEmbedding6 ∘ raw31703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31703step1 raw31703step1Labels raw31703step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4651 node4651Labels := by rfl

def raw31704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31704step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31704 raw31704Labels = mixedMoment B node4714 node4714Labels := by
  calc
    mixedMoment B raw31704 raw31704Labels = mixedMoment B raw31704step0 raw31704step0Labels := by
      have ha : raw31704step0 = (fun i j => raw31704 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31704step0 raw31704; decide +kernel
      have hl : raw31704step0Labels = raw31704Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31704 raw31704Labels permutation201 permutation3
    mixedMoment B raw31704step0 raw31704step0Labels = mixedMoment B raw31704step1 raw31704step1Labels := by
      have ha : raw31704step1 = raw31704step0 := by apply Matrix.ext; unfold raw31704step1 raw31704step0; decide +kernel
      have hl : raw31704step0Labels = labelEmbedding6 ∘ raw31704step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31704step0 raw31704step0Labels raw31704step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4714 node4714Labels := by rfl

def raw31705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw31705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw31705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw31705step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw31705step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31705 raw31705Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw31705 raw31705Labels = mixedMoment B raw31705step0 raw31705step0Labels := by
      have hz : ∀ j, raw31705 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31705step0 = (fun i j => raw31705 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31705step0 raw31705; decide +kernel
      have hl : raw31705step0Labels = raw31705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31705 raw31705Labels permutation434 hz
    mixedMoment B raw31705step0 raw31705step0Labels = mixedMoment B raw31705step1 raw31705step1Labels := by
      have ha : raw31705step1 = (fun i j => raw31705step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31705step1 raw31705step0; decide +kernel
      have hl : raw31705step1Labels = raw31705step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31705step0 raw31705step0Labels permutation36 permutation3
    mixedMoment B raw31705step1 raw31705step1Labels = mixedMoment B raw31705step2 raw31705step2Labels := by
      have ha : raw31705step2 = raw31705step1 := by apply Matrix.ext; unfold raw31705step2 raw31705step1; decide +kernel
      have hl : raw31705step1Labels = labelEmbedding6 ∘ raw31705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31705step1 raw31705step1Labels raw31705step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw31706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31706step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31706 raw31706Labels = mixedMoment B node4220 node4220Labels := by
  calc
    mixedMoment B raw31706 raw31706Labels = mixedMoment B raw31706step0 raw31706step0Labels := by
      have hz : ∀ j, raw31706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31706step0 = (fun i j => raw31706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31706step0 raw31706; decide +kernel
      have hl : raw31706step0Labels = raw31706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31706 raw31706Labels permutation346 hz
    mixedMoment B raw31706step0 raw31706step0Labels = mixedMoment B raw31706step1 raw31706step1Labels := by
      have ha : raw31706step1 = (fun i j => raw31706step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31706step1 raw31706step0; decide +kernel
      have hl : raw31706step1Labels = raw31706step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31706step0 raw31706step0Labels permutation33 permutation3
    mixedMoment B raw31706step1 raw31706step1Labels = mixedMoment B raw31706step2 raw31706step2Labels := by
      have ha : raw31706step2 = raw31706step1 := by apply Matrix.ext; unfold raw31706step2 raw31706step1; decide +kernel
      have hl : raw31706step1Labels = labelEmbedding6 ∘ raw31706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31706step1 raw31706step1Labels raw31706step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4220 node4220Labels := by rfl

def raw31707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31707step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31707 raw31707Labels = mixedMoment B node4651 node4651Labels := by
  calc
    mixedMoment B raw31707 raw31707Labels = mixedMoment B raw31707step0 raw31707step0Labels := by
      have hz : ∀ j, raw31707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31707step0 = (fun i j => raw31707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31707step0 raw31707; decide +kernel
      have hl : raw31707step0Labels = raw31707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31707 raw31707Labels permutation346 hz
    mixedMoment B raw31707step0 raw31707step0Labels = mixedMoment B raw31707step1 raw31707step1Labels := by
      have ha : raw31707step1 = (fun i j => raw31707step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31707step1 raw31707step0; decide +kernel
      have hl : raw31707step1Labels = raw31707step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31707step0 raw31707step0Labels permutation33 permutation3
    mixedMoment B raw31707step1 raw31707step1Labels = mixedMoment B raw31707step2 raw31707step2Labels := by
      have ha : raw31707step2 = raw31707step1 := by apply Matrix.ext; unfold raw31707step2 raw31707step1; decide +kernel
      have hl : raw31707step1Labels = labelEmbedding6 ∘ raw31707step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31707step1 raw31707step1Labels raw31707step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4651 node4651Labels := by rfl

def raw31708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw31708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31708step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31708step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31708 raw31708Labels = mixedMoment B node4714 node4714Labels := by
  calc
    mixedMoment B raw31708 raw31708Labels = mixedMoment B raw31708step0 raw31708step0Labels := by
      have ha : raw31708step0 = (fun i j => raw31708 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31708step0 raw31708; decide +kernel
      have hl : raw31708step0Labels = raw31708Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31708 raw31708Labels permutation177 permutation3
    mixedMoment B raw31708step0 raw31708step0Labels = mixedMoment B raw31708step1 raw31708step1Labels := by
      have ha : raw31708step1 = raw31708step0 := by apply Matrix.ext; unfold raw31708step1 raw31708step0; decide +kernel
      have hl : raw31708step0Labels = labelEmbedding6 ∘ raw31708step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31708step0 raw31708step0Labels raw31708step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4714 node4714Labels := by rfl

def raw31709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw31709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw31709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw31709step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw31709step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31709 raw31709Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw31709 raw31709Labels = mixedMoment B raw31709step0 raw31709step0Labels := by
      have hz : ∀ j, raw31709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31709step0 = (fun i j => raw31709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31709step0 raw31709; decide +kernel
      have hl : raw31709step0Labels = raw31709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31709 raw31709Labels permutation346 hz
    mixedMoment B raw31709step0 raw31709step0Labels = mixedMoment B raw31709step1 raw31709step1Labels := by
      have ha : raw31709step1 = (fun i j => raw31709step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31709step1 raw31709step0; decide +kernel
      have hl : raw31709step1Labels = raw31709step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31709step0 raw31709step0Labels permutation36 permutation3
    mixedMoment B raw31709step1 raw31709step1Labels = mixedMoment B raw31709step2 raw31709step2Labels := by
      have ha : raw31709step2 = raw31709step1 := by apply Matrix.ext; unfold raw31709step2 raw31709step1; decide +kernel
      have hl : raw31709step1Labels = labelEmbedding6 ∘ raw31709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31709step1 raw31709step1Labels raw31709step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw31710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw31710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw31710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![3, -4, 1], ![2, 0, -2]]
def raw31710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw31710step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31710step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw31710step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31710 raw31710Labels = mixedMoment B node4226 node4226Labels := by
  calc
    mixedMoment B raw31710 raw31710Labels = mixedMoment B raw31710step0 raw31710step0Labels := by
      have hz : ∀ j, raw31710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31710step0 = (fun i j => raw31710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31710step0 raw31710; decide +kernel
      have hl : raw31710step0Labels = raw31710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31710 raw31710Labels permutation434 hz
    mixedMoment B raw31710step0 raw31710step0Labels = mixedMoment B raw31710step1 raw31710step1Labels := by
      have hz : ∀ j, raw31710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31710step1 = (fun i j => raw31710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31710step1 raw31710step0; decide +kernel
      have hl : raw31710step1Labels = raw31710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31710step0 raw31710step0Labels permutation80 hz
    mixedMoment B raw31710step1 raw31710step1Labels = mixedMoment B raw31710step2 raw31710step2Labels := by
      have ha : raw31710step2 = (fun i j => raw31710step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31710step2 raw31710step1; decide +kernel
      have hl : raw31710step2Labels = raw31710step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31710step1 raw31710step1Labels permutation9 permutation3
    mixedMoment B raw31710step2 raw31710step2Labels = mixedMoment B raw31710step3 raw31710step3Labels := by
      have ha : raw31710step3 = raw31710step2 := by apply Matrix.ext; unfold raw31710step3 raw31710step2; decide +kernel
      have hl : raw31710step2Labels = labelEmbedding6 ∘ raw31710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31710step2 raw31710step2Labels raw31710step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4226 node4226Labels := by rfl

def raw31711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw31711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw31711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![3, -4, 1], ![2, 0, -2]]
def raw31711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def raw31711step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw31711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def raw31711step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31711 raw31711Labels = mixedMoment B node4382 node4382Labels := by
  calc
    mixedMoment B raw31711 raw31711Labels = mixedMoment B raw31711step0 raw31711step0Labels := by
      have hz : ∀ j, raw31711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31711step0 = (fun i j => raw31711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31711step0 raw31711; decide +kernel
      have hl : raw31711step0Labels = raw31711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31711 raw31711Labels permutation434 hz
    mixedMoment B raw31711step0 raw31711step0Labels = mixedMoment B raw31711step1 raw31711step1Labels := by
      have hz : ∀ j, raw31711step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31711step1 = (fun i j => raw31711step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31711step1 raw31711step0; decide +kernel
      have hl : raw31711step1Labels = raw31711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31711step0 raw31711step0Labels permutation80 hz
    mixedMoment B raw31711step1 raw31711step1Labels = mixedMoment B raw31711step2 raw31711step2Labels := by
      have ha : raw31711step2 = (fun i j => raw31711step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31711step2 raw31711step1; decide +kernel
      have hl : raw31711step2Labels = raw31711step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31711step1 raw31711step1Labels permutation25 permutation5
    mixedMoment B raw31711step2 raw31711step2Labels = mixedMoment B raw31711step3 raw31711step3Labels := by
      have ha : raw31711step3 = raw31711step2 := by apply Matrix.ext; unfold raw31711step3 raw31711step2; decide +kernel
      have hl : raw31711step2Labels = labelEmbedding8 ∘ raw31711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31711step2 raw31711step2Labels raw31711step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4382 node4382Labels := by rfl

def raw31712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw31712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw31712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw31712step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw31712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw31712step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31712 raw31712Labels = mixedMoment B node4377 node4377Labels := by
  calc
    mixedMoment B raw31712 raw31712Labels = mixedMoment B raw31712step0 raw31712step0Labels := by
      have hz : ∀ j, raw31712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31712step0 = (fun i j => raw31712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31712step0 raw31712; decide +kernel
      have hl : raw31712step0Labels = raw31712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31712 raw31712Labels permutation434 hz
    mixedMoment B raw31712step0 raw31712step0Labels = mixedMoment B raw31712step1 raw31712step1Labels := by
      have ha : raw31712step1 = (fun i j => raw31712step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31712step1 raw31712step0; decide +kernel
      have hl : raw31712step1Labels = raw31712step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31712step0 raw31712step0Labels permutation125 permutation5
    mixedMoment B raw31712step1 raw31712step1Labels = mixedMoment B raw31712step2 raw31712step2Labels := by
      have ha : raw31712step2 = raw31712step1 := by apply Matrix.ext; unfold raw31712step2 raw31712step1; decide +kernel
      have hl : raw31712step1Labels = labelEmbedding8 ∘ raw31712step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31712step1 raw31712step1Labels raw31712step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4377 node4377Labels := by rfl

def raw31713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw31713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw31713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw31713step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw31713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw31713step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31713 raw31713Labels = mixedMoment B node4377 node4377Labels := by
  calc
    mixedMoment B raw31713 raw31713Labels = mixedMoment B raw31713step0 raw31713step0Labels := by
      have hz : ∀ j, raw31713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31713step0 = (fun i j => raw31713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31713step0 raw31713; decide +kernel
      have hl : raw31713step0Labels = raw31713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31713 raw31713Labels permutation346 hz
    mixedMoment B raw31713step0 raw31713step0Labels = mixedMoment B raw31713step1 raw31713step1Labels := by
      have ha : raw31713step1 = (fun i j => raw31713step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31713step1 raw31713step0; decide +kernel
      have hl : raw31713step1Labels = raw31713step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31713step0 raw31713step0Labels permutation125 permutation5
    mixedMoment B raw31713step1 raw31713step1Labels = mixedMoment B raw31713step2 raw31713step2Labels := by
      have ha : raw31713step2 = raw31713step1 := by apply Matrix.ext; unfold raw31713step2 raw31713step1; decide +kernel
      have hl : raw31713step1Labels = labelEmbedding8 ∘ raw31713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31713step1 raw31713step1Labels raw31713step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4377 node4377Labels := by rfl

def raw31714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![1, 1, -2]]
def raw31714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -4, 1], ![1, 1, -2]]
def raw31714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![3, -4, 1], ![1, 1, -2]]
def raw31714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw31714step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw31714step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw31714step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31714 raw31714Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw31714 raw31714Labels = mixedMoment B raw31714step0 raw31714step0Labels := by
      have hz : ∀ j, raw31714 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31714step0 = (fun i j => raw31714 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31714step0 raw31714; decide +kernel
      have hl : raw31714step0Labels = raw31714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31714 raw31714Labels permutation434 hz
    mixedMoment B raw31714step0 raw31714step0Labels = mixedMoment B raw31714step1 raw31714step1Labels := by
      have hz : ∀ j, raw31714step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31714step1 = (fun i j => raw31714step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31714step1 raw31714step0; decide +kernel
      have hl : raw31714step1Labels = raw31714step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31714step0 raw31714step0Labels permutation80 hz
    mixedMoment B raw31714step1 raw31714step1Labels = mixedMoment B raw31714step2 raw31714step2Labels := by
      have ha : raw31714step2 = (fun i j => raw31714step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31714step2 raw31714step1; decide +kernel
      have hl : raw31714step2Labels = raw31714step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31714step1 raw31714step1Labels permutation23 permutation5
    mixedMoment B raw31714step2 raw31714step2Labels = mixedMoment B raw31714step3 raw31714step3Labels := by
      have ha : raw31714step3 = raw31714step2 := by apply Matrix.ext; unfold raw31714step3 raw31714step2; decide +kernel
      have hl : raw31714step2Labels = labelEmbedding8 ∘ raw31714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31714step2 raw31714step2Labels raw31714step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

def raw31715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw31715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw31715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![2, -3, 1], ![3, -1, -2]]
def raw31715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw31715step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31715step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw31715step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31715 raw31715Labels = mixedMoment B node4229 node4229Labels := by
  calc
    mixedMoment B raw31715 raw31715Labels = mixedMoment B raw31715step0 raw31715step0Labels := by
      have hz : ∀ j, raw31715 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31715step0 = (fun i j => raw31715 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31715step0 raw31715; decide +kernel
      have hl : raw31715step0Labels = raw31715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31715 raw31715Labels permutation434 hz
    mixedMoment B raw31715step0 raw31715step0Labels = mixedMoment B raw31715step1 raw31715step1Labels := by
      have hz : ∀ j, raw31715step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31715step1 = (fun i j => raw31715step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31715step1 raw31715step0; decide +kernel
      have hl : raw31715step1Labels = raw31715step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31715step0 raw31715step0Labels permutation80 hz
    mixedMoment B raw31715step1 raw31715step1Labels = mixedMoment B raw31715step2 raw31715step2Labels := by
      have ha : raw31715step2 = (fun i j => raw31715step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31715step2 raw31715step1; decide +kernel
      have hl : raw31715step2Labels = raw31715step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31715step1 raw31715step1Labels permutation8 permutation3
    mixedMoment B raw31715step2 raw31715step2Labels = mixedMoment B raw31715step3 raw31715step3Labels := by
      have ha : raw31715step3 = raw31715step2 := by apply Matrix.ext; unfold raw31715step3 raw31715step2; decide +kernel
      have hl : raw31715step2Labels = labelEmbedding6 ∘ raw31715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31715step2 raw31715step2Labels raw31715step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4229 node4229Labels := by rfl

def raw31716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw31716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw31716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![2, -3, 1], ![3, -1, -2]]
def raw31716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31716step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw31716step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31716step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw31716step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31716 raw31716Labels = mixedMoment B node4657 node4657Labels := by
  calc
    mixedMoment B raw31716 raw31716Labels = mixedMoment B raw31716step0 raw31716step0Labels := by
      have hz : ∀ j, raw31716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31716step0 = (fun i j => raw31716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31716step0 raw31716; decide +kernel
      have hl : raw31716step0Labels = raw31716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31716 raw31716Labels permutation434 hz
    mixedMoment B raw31716step0 raw31716step0Labels = mixedMoment B raw31716step1 raw31716step1Labels := by
      have hz : ∀ j, raw31716step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31716step1 = (fun i j => raw31716step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31716step1 raw31716step0; decide +kernel
      have hl : raw31716step1Labels = raw31716step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31716step0 raw31716step0Labels permutation80 hz
    mixedMoment B raw31716step1 raw31716step1Labels = mixedMoment B raw31716step2 raw31716step2Labels := by
      have ha : raw31716step2 = (fun i j => raw31716step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31716step2 raw31716step1; decide +kernel
      have hl : raw31716step2Labels = raw31716step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31716step1 raw31716step1Labels permutation8 permutation3
    mixedMoment B raw31716step2 raw31716step2Labels = mixedMoment B raw31716step3 raw31716step3Labels := by
      have ha : raw31716step3 = raw31716step2 := by apply Matrix.ext; unfold raw31716step3 raw31716step2; decide +kernel
      have hl : raw31716step2Labels = labelEmbedding6 ∘ raw31716step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31716step2 raw31716step2Labels raw31716step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4657 node4657Labels := by rfl

def raw31717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw31717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw31717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw31717step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw31717step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31717 raw31717Labels = mixedMoment B node4719 node4719Labels := by
  calc
    mixedMoment B raw31717 raw31717Labels = mixedMoment B raw31717step0 raw31717step0Labels := by
      have hz : ∀ j, raw31717 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31717step0 = (fun i j => raw31717 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31717step0 raw31717; decide +kernel
      have hl : raw31717step0Labels = raw31717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31717 raw31717Labels permutation434 hz
    mixedMoment B raw31717step0 raw31717step0Labels = mixedMoment B raw31717step1 raw31717step1Labels := by
      have ha : raw31717step1 = (fun i j => raw31717step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31717step1 raw31717step0; decide +kernel
      have hl : raw31717step1Labels = raw31717step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31717step0 raw31717step0Labels permutation38 permutation3
    mixedMoment B raw31717step1 raw31717step1Labels = mixedMoment B raw31717step2 raw31717step2Labels := by
      have ha : raw31717step2 = raw31717step1 := by apply Matrix.ext; unfold raw31717step2 raw31717step1; decide +kernel
      have hl : raw31717step1Labels = labelEmbedding6 ∘ raw31717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31717step1 raw31717step1Labels raw31717step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4719 node4719Labels := by rfl

def raw31718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw31718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw31718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw31718step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw31718step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31718 raw31718Labels = mixedMoment B node4719 node4719Labels := by
  calc
    mixedMoment B raw31718 raw31718Labels = mixedMoment B raw31718step0 raw31718step0Labels := by
      have hz : ∀ j, raw31718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31718step0 = (fun i j => raw31718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31718step0 raw31718; decide +kernel
      have hl : raw31718step0Labels = raw31718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31718 raw31718Labels permutation346 hz
    mixedMoment B raw31718step0 raw31718step0Labels = mixedMoment B raw31718step1 raw31718step1Labels := by
      have ha : raw31718step1 = (fun i j => raw31718step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31718step1 raw31718step0; decide +kernel
      have hl : raw31718step1Labels = raw31718step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31718step0 raw31718step0Labels permutation38 permutation3
    mixedMoment B raw31718step1 raw31718step1Labels = mixedMoment B raw31718step2 raw31718step2Labels := by
      have ha : raw31718step2 = raw31718step1 := by apply Matrix.ext; unfold raw31718step2 raw31718step1; decide +kernel
      have hl : raw31718step1Labels = labelEmbedding6 ∘ raw31718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31718step1 raw31718step1Labels raw31718step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4719 node4719Labels := by rfl

def raw31719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw31719step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw31719step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw31719step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31719 raw31719Labels = mixedMoment B node4408 node4408Labels := by
  calc
    mixedMoment B raw31719 raw31719Labels = mixedMoment B raw31719step0 raw31719step0Labels := by
      have hz : ∀ j, raw31719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31719step0 = (fun i j => raw31719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31719step0 raw31719; decide +kernel
      have hl : raw31719step0Labels = raw31719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31719 raw31719Labels permutation346 hz
    mixedMoment B raw31719step0 raw31719step0Labels = mixedMoment B raw31719step1 raw31719step1Labels := by
      have ha : raw31719step1 = (fun i j => raw31719step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31719step1 raw31719step0; decide +kernel
      have hl : raw31719step1Labels = raw31719step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31719step0 raw31719step0Labels permutation36 permutation4
    mixedMoment B raw31719step1 raw31719step1Labels = mixedMoment B raw31719step2 raw31719step2Labels := by
      have ha : raw31719step2 = -raw31719step1 := by apply Matrix.ext; change ∀ i j, raw31719step2 i j = -(raw31719step1 i j); unfold raw31719step2 raw31719step1; decide +kernel
      have hl : raw31719step2Labels = raw31719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31719step2 raw31719step2Labels = mixedMoment B raw31719step3 raw31719step3Labels := by
      have ha : raw31719step3 = raw31719step2 := by apply Matrix.ext; unfold raw31719step3 raw31719step2; decide +kernel
      have hl : raw31719step2Labels = labelEmbedding7 ∘ raw31719step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31719step2 raw31719step2Labels raw31719step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4408 node4408Labels := by rfl

def raw31720 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31720step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31720 raw31720Labels = mixedMoment B node4781 node4781Labels := by
  calc
    mixedMoment B raw31720 raw31720Labels = mixedMoment B raw31720step0 raw31720step0Labels := by
      have ha : raw31720step0 = (fun i j => raw31720 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31720step0 raw31720; decide +kernel
      have hl : raw31720step0Labels = raw31720Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31720 raw31720Labels permutation153 permutation6
    mixedMoment B raw31720step0 raw31720step0Labels = mixedMoment B raw31720step1 raw31720step1Labels := by
      have ha : raw31720step1 = raw31720step0 := by apply Matrix.ext; unfold raw31720step1 raw31720step0; decide +kernel
      have hl : raw31720step0Labels = labelEmbedding9 ∘ raw31720step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31720step0 raw31720step0Labels raw31720step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4781 node4781Labels := by rfl

def raw31721 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw31721step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw31721step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31721 raw31721Labels = mixedMoment B node4809 node4809Labels := by
  calc
    mixedMoment B raw31721 raw31721Labels = mixedMoment B raw31721step0 raw31721step0Labels := by
      have hz : ∀ j, raw31721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31721step0 = (fun i j => raw31721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31721step0 raw31721; decide +kernel
      have hl : raw31721step0Labels = raw31721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31721 raw31721Labels permutation346 hz
    mixedMoment B raw31721step0 raw31721step0Labels = mixedMoment B raw31721step1 raw31721step1Labels := by
      have ha : raw31721step1 = (fun i j => raw31721step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31721step1 raw31721step0; decide +kernel
      have hl : raw31721step1Labels = raw31721step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31721step0 raw31721step0Labels permutation33 permutation6
    mixedMoment B raw31721step1 raw31721step1Labels = mixedMoment B raw31721step2 raw31721step2Labels := by
      have ha : raw31721step2 = raw31721step1 := by apply Matrix.ext; unfold raw31721step2 raw31721step1; decide +kernel
      have hl : raw31721step1Labels = labelEmbedding9 ∘ raw31721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31721step1 raw31721step1Labels raw31721step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4809 node4809Labels := by rfl

def raw31722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw31722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw31722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -4, 2], ![-2, 0, 2]]
def raw31722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-4, 2, 2]]
def raw31722step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31722step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw31722step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31722step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw31722step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31722 raw31722Labels = mixedMoment B node4413 node4413Labels := by
  calc
    mixedMoment B raw31722 raw31722Labels = mixedMoment B raw31722step0 raw31722step0Labels := by
      have hz : ∀ j, raw31722 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31722step0 = (fun i j => raw31722 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31722step0 raw31722; decide +kernel
      have hl : raw31722step0Labels = raw31722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31722 raw31722Labels permutation434 hz
    mixedMoment B raw31722step0 raw31722step0Labels = mixedMoment B raw31722step1 raw31722step1Labels := by
      have hz : ∀ j, raw31722step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31722step1 = (fun i j => raw31722step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31722step1 raw31722step0; decide +kernel
      have hl : raw31722step1Labels = raw31722step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31722step0 raw31722step0Labels permutation80 hz
    mixedMoment B raw31722step1 raw31722step1Labels = mixedMoment B raw31722step2 raw31722step2Labels := by
      have ha : raw31722step2 = (fun i j => raw31722step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31722step2 raw31722step1; decide +kernel
      have hl : raw31722step2Labels = raw31722step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31722step1 raw31722step1Labels permutation9 permutation4
    mixedMoment B raw31722step2 raw31722step2Labels = mixedMoment B raw31722step3 raw31722step3Labels := by
      have ha : raw31722step3 = -raw31722step2 := by apply Matrix.ext; change ∀ i j, raw31722step3 i j = -(raw31722step2 i j); unfold raw31722step3 raw31722step2; decide +kernel
      have hl : raw31722step3Labels = raw31722step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31722step3 raw31722step3Labels = mixedMoment B raw31722step4 raw31722step4Labels := by
      have ha : raw31722step4 = raw31722step3 := by apply Matrix.ext; unfold raw31722step4 raw31722step3; decide +kernel
      have hl : raw31722step3Labels = labelEmbedding7 ∘ raw31722step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31722step3 raw31722step3Labels raw31722step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4413 node4413Labels := by rfl

def raw31723 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw31723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw31723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw31723step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw31723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31723 raw31723Labels = mixedMoment B node4562 node4562Labels := by
  calc
    mixedMoment B raw31723 raw31723Labels = mixedMoment B raw31723step0 raw31723step0Labels := by
      have hz : ∀ j, raw31723 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31723step0 = (fun i j => raw31723 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31723step0 raw31723; decide +kernel
      have hl : raw31723step0Labels = raw31723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31723 raw31723Labels permutation434 hz
    mixedMoment B raw31723step0 raw31723step0Labels = mixedMoment B raw31723step1 raw31723step1Labels := by
      have ha : raw31723step1 = (fun i j => raw31723step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31723step1 raw31723step0; decide +kernel
      have hl : raw31723step1Labels = raw31723step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31723step0 raw31723step0Labels permutation125 permutation4
    mixedMoment B raw31723step1 raw31723step1Labels = mixedMoment B raw31723step2 raw31723step2Labels := by
      have ha : raw31723step2 = raw31723step1 := by apply Matrix.ext; unfold raw31723step2 raw31723step1; decide +kernel
      have hl : raw31723step1Labels = labelEmbedding7 ∘ raw31723step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31723step1 raw31723step1Labels raw31723step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4562 node4562Labels := by rfl

def raw31724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw31724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw31724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw31724step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw31724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31724 raw31724Labels = mixedMoment B node4562 node4562Labels := by
  calc
    mixedMoment B raw31724 raw31724Labels = mixedMoment B raw31724step0 raw31724step0Labels := by
      have hz : ∀ j, raw31724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31724step0 = (fun i j => raw31724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31724step0 raw31724; decide +kernel
      have hl : raw31724step0Labels = raw31724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31724 raw31724Labels permutation346 hz
    mixedMoment B raw31724step0 raw31724step0Labels = mixedMoment B raw31724step1 raw31724step1Labels := by
      have ha : raw31724step1 = (fun i j => raw31724step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31724step1 raw31724step0; decide +kernel
      have hl : raw31724step1Labels = raw31724step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31724step0 raw31724step0Labels permutation125 permutation4
    mixedMoment B raw31724step1 raw31724step1Labels = mixedMoment B raw31724step2 raw31724step2Labels := by
      have ha : raw31724step2 = raw31724step1 := by apply Matrix.ext; unfold raw31724step2 raw31724step1; decide +kernel
      have hl : raw31724step1Labels = labelEmbedding7 ∘ raw31724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31724step1 raw31724step1Labels raw31724step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4562 node4562Labels := by rfl

def raw31725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-3, 1, 2]]
def raw31725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -4, 2], ![-3, 1, 2]]
def raw31725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -4, 2], ![-3, 1, 2]]
def raw31725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw31725step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw31725step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw31725step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31725 raw31725Labels = mixedMoment B node4610 node4610Labels := by
  calc
    mixedMoment B raw31725 raw31725Labels = mixedMoment B raw31725step0 raw31725step0Labels := by
      have hz : ∀ j, raw31725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31725step0 = (fun i j => raw31725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31725step0 raw31725; decide +kernel
      have hl : raw31725step0Labels = raw31725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31725 raw31725Labels permutation434 hz
    mixedMoment B raw31725step0 raw31725step0Labels = mixedMoment B raw31725step1 raw31725step1Labels := by
      have hz : ∀ j, raw31725step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31725step1 = (fun i j => raw31725step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31725step1 raw31725step0; decide +kernel
      have hl : raw31725step1Labels = raw31725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31725step0 raw31725step0Labels permutation80 hz
    mixedMoment B raw31725step1 raw31725step1Labels = mixedMoment B raw31725step2 raw31725step2Labels := by
      have ha : raw31725step2 = (fun i j => raw31725step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31725step2 raw31725step1; decide +kernel
      have hl : raw31725step2Labels = raw31725step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31725step1 raw31725step1Labels permutation23 permutation5
    mixedMoment B raw31725step2 raw31725step2Labels = mixedMoment B raw31725step3 raw31725step3Labels := by
      have ha : raw31725step3 = raw31725step2 := by apply Matrix.ext; unfold raw31725step3 raw31725step2; decide +kernel
      have hl : raw31725step2Labels = labelEmbedding8 ∘ raw31725step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31725step2 raw31725step2Labels raw31725step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4610 node4610Labels := by rfl

def raw31726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -3, 2], ![-1, -1, 2]]
def raw31726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw31726step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw31726step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31726step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw31726step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31726 raw31726Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw31726 raw31726Labels = mixedMoment B raw31726step0 raw31726step0Labels := by
      have hz : ∀ j, raw31726 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31726step0 = (fun i j => raw31726 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31726step0 raw31726; decide +kernel
      have hl : raw31726step0Labels = raw31726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31726 raw31726Labels permutation434 hz
    mixedMoment B raw31726step0 raw31726step0Labels = mixedMoment B raw31726step1 raw31726step1Labels := by
      have hz : ∀ j, raw31726step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31726step1 = (fun i j => raw31726step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31726step1 raw31726step0; decide +kernel
      have hl : raw31726step1Labels = raw31726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31726step0 raw31726step0Labels permutation80 hz
    mixedMoment B raw31726step1 raw31726step1Labels = mixedMoment B raw31726step2 raw31726step2Labels := by
      have ha : raw31726step2 = (fun i j => raw31726step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31726step2 raw31726step1; decide +kernel
      have hl : raw31726step2Labels = raw31726step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31726step1 raw31726step1Labels permutation9 permutation4
    mixedMoment B raw31726step2 raw31726step2Labels = mixedMoment B raw31726step3 raw31726step3Labels := by
      have ha : raw31726step3 = -raw31726step2 := by apply Matrix.ext; change ∀ i j, raw31726step3 i j = -(raw31726step2 i j); unfold raw31726step3 raw31726step2; decide +kernel
      have hl : raw31726step3Labels = raw31726step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31726step3 raw31726step3Labels = mixedMoment B raw31726step4 raw31726step4Labels := by
      have ha : raw31726step4 = raw31726step3 := by apply Matrix.ext; unfold raw31726step4 raw31726step3; decide +kernel
      have hl : raw31726step3Labels = labelEmbedding7 ∘ raw31726step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31726step3 raw31726step3Labels raw31726step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

def raw31727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw31727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw31727step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw31727step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31727step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw31727step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31727 raw31727Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw31727 raw31727Labels = mixedMoment B raw31727step0 raw31727step0Labels := by
      have hz : ∀ j, raw31727 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31727step0 = (fun i j => raw31727 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31727step0 raw31727; decide +kernel
      have hl : raw31727step0Labels = raw31727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31727 raw31727Labels permutation434 hz
    mixedMoment B raw31727step0 raw31727step0Labels = mixedMoment B raw31727step1 raw31727step1Labels := by
      have ha : raw31727step1 = (fun i j => raw31727step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31727step1 raw31727step0; decide +kernel
      have hl : raw31727step1Labels = raw31727step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31727step0 raw31727step0Labels permutation39 permutation4
    mixedMoment B raw31727step1 raw31727step1Labels = mixedMoment B raw31727step2 raw31727step2Labels := by
      have ha : raw31727step2 = -raw31727step1 := by apply Matrix.ext; change ∀ i j, raw31727step2 i j = -(raw31727step1 i j); unfold raw31727step2 raw31727step1; decide +kernel
      have hl : raw31727step2Labels = raw31727step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31727step2 raw31727step2Labels = mixedMoment B raw31727step3 raw31727step3Labels := by
      have ha : raw31727step3 = raw31727step2 := by apply Matrix.ext; unfold raw31727step3 raw31727step2; decide +kernel
      have hl : raw31727step2Labels = labelEmbedding7 ∘ raw31727step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31727step2 raw31727step2Labels raw31727step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw31728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31728step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw31728step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw31728step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31728step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw31728step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31728 raw31728Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw31728 raw31728Labels = mixedMoment B raw31728step0 raw31728step0Labels := by
      have hz : ∀ j, raw31728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31728step0 = (fun i j => raw31728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31728step0 raw31728; decide +kernel
      have hl : raw31728step0Labels = raw31728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31728 raw31728Labels permutation434 hz
    mixedMoment B raw31728step0 raw31728step0Labels = mixedMoment B raw31728step1 raw31728step1Labels := by
      have hz : ∀ j, raw31728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31728step1 = (fun i j => raw31728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31728step1 raw31728step0; decide +kernel
      have hl : raw31728step1Labels = raw31728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31728step0 raw31728step0Labels permutation80 hz
    mixedMoment B raw31728step1 raw31728step1Labels = mixedMoment B raw31728step2 raw31728step2Labels := by
      have ha : raw31728step2 = (fun i j => raw31728step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31728step2 raw31728step1; decide +kernel
      have hl : raw31728step2Labels = raw31728step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31728step1 raw31728step1Labels permutation9 permutation7
    mixedMoment B raw31728step2 raw31728step2Labels = mixedMoment B raw31728step3 raw31728step3Labels := by
      have ha : raw31728step3 = -raw31728step2 := by apply Matrix.ext; change ∀ i j, raw31728step3 i j = -(raw31728step2 i j); unfold raw31728step3 raw31728step2; decide +kernel
      have hl : raw31728step3Labels = raw31728step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31728step3 raw31728step3Labels = mixedMoment B raw31728step4 raw31728step4Labels := by
      have ha : raw31728step4 = raw31728step3 := by apply Matrix.ext; unfold raw31728step4 raw31728step3; decide +kernel
      have hl : raw31728step3Labels = labelEmbedding10 ∘ raw31728step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31728step3 raw31728step3Labels raw31728step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw31729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31729step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31729step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31729step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31729 raw31729Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw31729 raw31729Labels = mixedMoment B raw31729step0 raw31729step0Labels := by
      have hz : ∀ j, raw31729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31729step0 = (fun i j => raw31729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31729step0 raw31729; decide +kernel
      have hl : raw31729step0Labels = raw31729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31729 raw31729Labels permutation434 hz
    mixedMoment B raw31729step0 raw31729step0Labels = mixedMoment B raw31729step1 raw31729step1Labels := by
      have ha : raw31729step1 = (fun i j => raw31729step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31729step1 raw31729step0; decide +kernel
      have hl : raw31729step1Labels = raw31729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31729step0 raw31729step0Labels permutation33 permutation7
    mixedMoment B raw31729step1 raw31729step1Labels = mixedMoment B raw31729step2 raw31729step2Labels := by
      have ha : raw31729step2 = -raw31729step1 := by apply Matrix.ext; change ∀ i j, raw31729step2 i j = -(raw31729step1 i j); unfold raw31729step2 raw31729step1; decide +kernel
      have hl : raw31729step2Labels = raw31729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31729step2 raw31729step2Labels = mixedMoment B raw31729step3 raw31729step3Labels := by
      have ha : raw31729step3 = raw31729step2 := by apply Matrix.ext; unfold raw31729step3 raw31729step2; decide +kernel
      have hl : raw31729step2Labels = labelEmbedding10 ∘ raw31729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31729step2 raw31729step2Labels raw31729step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw31730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31730step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31730step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31730step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31730step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31730 raw31730Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw31730 raw31730Labels = mixedMoment B raw31730step0 raw31730step0Labels := by
      have hz : ∀ j, raw31730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31730step0 = (fun i j => raw31730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31730step0 raw31730; decide +kernel
      have hl : raw31730step0Labels = raw31730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31730 raw31730Labels permutation346 hz
    mixedMoment B raw31730step0 raw31730step0Labels = mixedMoment B raw31730step1 raw31730step1Labels := by
      have ha : raw31730step1 = (fun i j => raw31730step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31730step1 raw31730step0; decide +kernel
      have hl : raw31730step1Labels = raw31730step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31730step0 raw31730step0Labels permutation33 permutation7
    mixedMoment B raw31730step1 raw31730step1Labels = mixedMoment B raw31730step2 raw31730step2Labels := by
      have ha : raw31730step2 = -raw31730step1 := by apply Matrix.ext; change ∀ i j, raw31730step2 i j = -(raw31730step1 i j); unfold raw31730step2 raw31730step1; decide +kernel
      have hl : raw31730step2Labels = raw31730step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31730step2 raw31730step2Labels = mixedMoment B raw31730step3 raw31730step3Labels := by
      have ha : raw31730step3 = raw31730step2 := by apply Matrix.ext; unfold raw31730step3 raw31730step2; decide +kernel
      have hl : raw31730step2Labels = labelEmbedding10 ∘ raw31730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31730step2 raw31730step2Labels raw31730step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw31731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31731step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31731step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31731step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31731step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31731step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31731step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31731 raw31731Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw31731 raw31731Labels = mixedMoment B raw31731step0 raw31731step0Labels := by
      have hz : ∀ j, raw31731 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31731step0 = (fun i j => raw31731 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31731step0 raw31731; decide +kernel
      have hl : raw31731step0Labels = raw31731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31731 raw31731Labels permutation434 hz
    mixedMoment B raw31731step0 raw31731step0Labels = mixedMoment B raw31731step1 raw31731step1Labels := by
      have hz : ∀ j, raw31731step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31731step1 = (fun i j => raw31731step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31731step1 raw31731step0; decide +kernel
      have hl : raw31731step1Labels = raw31731step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31731step0 raw31731step0Labels permutation80 hz
    mixedMoment B raw31731step1 raw31731step1Labels = mixedMoment B raw31731step2 raw31731step2Labels := by
      have ha : raw31731step2 = (fun i j => raw31731step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31731step2 raw31731step1; decide +kernel
      have hl : raw31731step2Labels = raw31731step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31731step1 raw31731step1Labels permutation9 permutation7
    mixedMoment B raw31731step2 raw31731step2Labels = mixedMoment B raw31731step3 raw31731step3Labels := by
      have ha : raw31731step3 = -raw31731step2 := by apply Matrix.ext; change ∀ i j, raw31731step3 i j = -(raw31731step2 i j); unfold raw31731step3 raw31731step2; decide +kernel
      have hl : raw31731step3Labels = raw31731step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31731step3 raw31731step3Labels = mixedMoment B raw31731step4 raw31731step4Labels := by
      have ha : raw31731step4 = raw31731step3 := by apply Matrix.ext; unfold raw31731step4 raw31731step3; decide +kernel
      have hl : raw31731step3Labels = labelEmbedding10 ∘ raw31731step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31731step3 raw31731step3Labels raw31731step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw31732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31732step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31732step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31732 raw31732Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw31732 raw31732Labels = mixedMoment B raw31732step0 raw31732step0Labels := by
      have hz : ∀ j, raw31732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31732step0 = (fun i j => raw31732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31732step0 raw31732; decide +kernel
      have hl : raw31732step0Labels = raw31732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31732 raw31732Labels permutation434 hz
    mixedMoment B raw31732step0 raw31732step0Labels = mixedMoment B raw31732step1 raw31732step1Labels := by
      have ha : raw31732step1 = (fun i j => raw31732step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31732step1 raw31732step0; decide +kernel
      have hl : raw31732step1Labels = raw31732step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31732step0 raw31732step0Labels permutation33 permutation2
    _ = mixedMoment B node4684 node4684Labels := by rfl

def raw31733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31733 raw31733Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw31733 raw31733Labels = mixedMoment B raw31733step0 raw31733step0Labels := by
      have ha : raw31733step0 = (fun i j => raw31733 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31733step0 raw31733; decide +kernel
      have hl : raw31733step0Labels = raw31733Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31733 raw31733Labels permutation159 permutation2
    _ = mixedMoment B node4763 node4763Labels := by rfl

def raw31734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31734step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31734 raw31734Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw31734 raw31734Labels = mixedMoment B raw31734step0 raw31734step0Labels := by
      have hz : ∀ j, raw31734 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31734step0 = (fun i j => raw31734 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31734step0 raw31734; decide +kernel
      have hl : raw31734step0Labels = raw31734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31734 raw31734Labels permutation434 hz
    mixedMoment B raw31734step0 raw31734step0Labels = mixedMoment B raw31734step1 raw31734step1Labels := by
      have ha : raw31734step1 = (fun i j => raw31734step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31734step1 raw31734step0; decide +kernel
      have hl : raw31734step1Labels = raw31734step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31734step0 raw31734step0Labels permutation33 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw31735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31735 raw31735Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw31735 raw31735Labels = mixedMoment B raw31735step0 raw31735step0Labels := by
      have hz : ∀ j, raw31735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31735step0 = (fun i j => raw31735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31735step0 raw31735; decide +kernel
      have hl : raw31735step0Labels = raw31735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31735 raw31735Labels permutation346 hz
    mixedMoment B raw31735step0 raw31735step0Labels = mixedMoment B raw31735step1 raw31735step1Labels := by
      have ha : raw31735step1 = (fun i j => raw31735step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31735step1 raw31735step0; decide +kernel
      have hl : raw31735step1Labels = raw31735step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31735step0 raw31735step0Labels permutation33 permutation2
    _ = mixedMoment B node4684 node4684Labels := by rfl

def raw31736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31736 raw31736Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw31736 raw31736Labels = mixedMoment B raw31736step0 raw31736step0Labels := by
      have ha : raw31736step0 = (fun i j => raw31736 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31736step0 raw31736; decide +kernel
      have hl : raw31736step0Labels = raw31736Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31736 raw31736Labels permutation153 permutation2
    _ = mixedMoment B node4763 node4763Labels := by rfl

def raw31737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31737 raw31737Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw31737 raw31737Labels = mixedMoment B raw31737step0 raw31737step0Labels := by
      have hz : ∀ j, raw31737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31737step0 = (fun i j => raw31737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31737step0 raw31737; decide +kernel
      have hl : raw31737step0Labels = raw31737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31737 raw31737Labels permutation346 hz
    mixedMoment B raw31737step0 raw31737step0Labels = mixedMoment B raw31737step1 raw31737step1Labels := by
      have ha : raw31737step1 = (fun i j => raw31737step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31737step1 raw31737step0; decide +kernel
      have hl : raw31737step1Labels = raw31737step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31737step0 raw31737step0Labels permutation33 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw31738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31738step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31738step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31738 raw31738Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw31738 raw31738Labels = mixedMoment B raw31738step0 raw31738step0Labels := by
      have hz : ∀ j, raw31738 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31738step0 = (fun i j => raw31738 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31738step0 raw31738; decide +kernel
      have hl : raw31738step0Labels = raw31738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31738 raw31738Labels permutation434 hz
    mixedMoment B raw31738step0 raw31738step0Labels = mixedMoment B raw31738step1 raw31738step1Labels := by
      have hz : ∀ j, raw31738step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31738step1 = (fun i j => raw31738step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31738step1 raw31738step0; decide +kernel
      have hl : raw31738step1Labels = raw31738step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31738step0 raw31738step0Labels permutation80 hz
    mixedMoment B raw31738step1 raw31738step1Labels = mixedMoment B raw31738step2 raw31738step2Labels := by
      have ha : raw31738step2 = (fun i j => raw31738step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31738step2 raw31738step1; decide +kernel
      have hl : raw31738step2Labels = raw31738step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31738step1 raw31738step1Labels permutation9 permutation2
    _ = mixedMoment B node4692 node4692Labels := by rfl

def raw31739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31739step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31739 raw31739Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw31739 raw31739Labels = mixedMoment B raw31739step0 raw31739step0Labels := by
      have hz : ∀ j, raw31739 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31739step0 = (fun i j => raw31739 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31739step0 raw31739; decide +kernel
      have hl : raw31739step0Labels = raw31739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31739 raw31739Labels permutation434 hz
    mixedMoment B raw31739step0 raw31739step0Labels = mixedMoment B raw31739step1 raw31739step1Labels := by
      have ha : raw31739step1 = (fun i j => raw31739step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31739step1 raw31739step0; decide +kernel
      have hl : raw31739step1Labels = raw31739step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31739step0 raw31739step0Labels permutation33 permutation2
    _ = mixedMoment B node4769 node4769Labels := by rfl

def raw31740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31740 raw31740Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw31740 raw31740Labels = mixedMoment B raw31740step0 raw31740step0Labels := by
      have hz : ∀ j, raw31740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31740step0 = (fun i j => raw31740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31740step0 raw31740; decide +kernel
      have hl : raw31740step0Labels = raw31740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31740 raw31740Labels permutation346 hz
    mixedMoment B raw31740step0 raw31740step0Labels = mixedMoment B raw31740step1 raw31740step1Labels := by
      have ha : raw31740step1 = (fun i j => raw31740step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31740step1 raw31740step0; decide +kernel
      have hl : raw31740step1Labels = raw31740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31740step0 raw31740step0Labels permutation33 permutation2
    _ = mixedMoment B node4769 node4769Labels := by rfl

def raw31741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw31741step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31741 raw31741Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw31741 raw31741Labels = mixedMoment B raw31741step0 raw31741step0Labels := by
      have hz : ∀ j, raw31741 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31741step0 = (fun i j => raw31741 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31741step0 raw31741; decide +kernel
      have hl : raw31741step0Labels = raw31741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31741 raw31741Labels permutation434 hz
    mixedMoment B raw31741step0 raw31741step0Labels = mixedMoment B raw31741step1 raw31741step1Labels := by
      have hz : ∀ j, raw31741step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31741step1 = (fun i j => raw31741step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31741step1 raw31741step0; decide +kernel
      have hl : raw31741step1Labels = raw31741step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31741step0 raw31741step0Labels permutation80 hz
    mixedMoment B raw31741step1 raw31741step1Labels = mixedMoment B raw31741step2 raw31741step2Labels := by
      have ha : raw31741step2 = (fun i j => raw31741step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31741step2 raw31741step1; decide +kernel
      have hl : raw31741step2Labels = raw31741step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31741step1 raw31741step1Labels permutation9 permutation2
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw31742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31742step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31742 raw31742Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw31742 raw31742Labels = mixedMoment B raw31742step0 raw31742step0Labels := by
      have hz : ∀ j, raw31742 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31742step0 = (fun i j => raw31742 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31742step0 raw31742; decide +kernel
      have hl : raw31742step0Labels = raw31742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31742 raw31742Labels permutation434 hz
    mixedMoment B raw31742step0 raw31742step0Labels = mixedMoment B raw31742step1 raw31742step1Labels := by
      have hz : ∀ j, raw31742step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31742step1 = (fun i j => raw31742step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31742step1 raw31742step0; decide +kernel
      have hl : raw31742step1Labels = raw31742step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31742step0 raw31742step0Labels permutation80 hz
    _ = mixedMoment B node4693 node4693Labels := by rfl

def raw31743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31743 raw31743Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw31743 raw31743Labels = mixedMoment B raw31743step0 raw31743step0Labels := by
      have hz : ∀ j, raw31743 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31743step0 = (fun i j => raw31743 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31743step0 raw31743; decide +kernel
      have hl : raw31743step0Labels = raw31743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31743 raw31743Labels permutation434 hz
    _ = mixedMoment B node4770 node4770Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
