import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14208 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14208Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14208step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14208 raw14208Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw14208 raw14208Labels = mixedMoment B raw14208step0 raw14208step0Labels := by
      have hz : ∀ j, raw14208 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14208step0 = (fun i j => raw14208 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14208step0 raw14208; decide +kernel
      have hl : raw14208step0Labels = raw14208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14208 raw14208Labels permutation265 hz
    mixedMoment B raw14208step0 raw14208step0Labels = mixedMoment B raw14208step1 raw14208step1Labels := by
      have ha : raw14208step1 = (fun i j => raw14208step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14208step1 raw14208step0; decide +kernel
      have hl : raw14208step1Labels = raw14208step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14208step0 raw14208step0Labels permutation37 permutation6
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw14209 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14209Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14209step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14209 raw14209Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw14209 raw14209Labels = mixedMoment B raw14209step0 raw14209step0Labels := by
      have hz : ∀ j, raw14209 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14209step0 = (fun i j => raw14209 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14209step0 raw14209; decide +kernel
      have hl : raw14209step0Labels = raw14209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14209 raw14209Labels permutation265 hz
    mixedMoment B raw14209step0 raw14209step0Labels = mixedMoment B raw14209step1 raw14209step1Labels := by
      have ha : raw14209step1 = (fun i j => raw14209step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14209step1 raw14209step0; decide +kernel
      have hl : raw14209step1Labels = raw14209step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14209step0 raw14209step0Labels permutation35 permutation6
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw14210 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14210Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14210step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14210 raw14210Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw14210 raw14210Labels = mixedMoment B raw14210step0 raw14210step0Labels := by
      have hz : ∀ j, raw14210 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14210step0 = (fun i j => raw14210 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14210step0 raw14210; decide +kernel
      have hl : raw14210step0Labels = raw14210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14210 raw14210Labels permutation265 hz
    mixedMoment B raw14210step0 raw14210step0Labels = mixedMoment B raw14210step1 raw14210step1Labels := by
      have ha : raw14210step1 = (fun i j => raw14210step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14210step1 raw14210step0; decide +kernel
      have hl : raw14210step1Labels = raw14210step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14210step0 raw14210step0Labels permutation37 permutation6
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw14211 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14211Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14211 raw14211Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw14211 raw14211Labels = mixedMoment B raw14211step0 raw14211step0Labels := by
      have ha : raw14211step0 = (fun i j => raw14211 (permutation157 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14211step0 raw14211; decide +kernel
      have hl : raw14211step0Labels = raw14211Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14211 raw14211Labels permutation157 permutation6
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw14212 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14212Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw14212step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw14212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14212 raw14212Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw14212 raw14212Labels = mixedMoment B raw14212step0 raw14212step0Labels := by
      have hz : ∀ j, raw14212 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14212step0 = (fun i j => raw14212 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14212step0 raw14212; decide +kernel
      have hl : raw14212step0Labels = raw14212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14212 raw14212Labels permutation265 hz
    mixedMoment B raw14212step0 raw14212step0Labels = mixedMoment B raw14212step1 raw14212step1Labels := by
      have ha : raw14212step1 = (fun i j => raw14212step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14212step1 raw14212step0; decide +kernel
      have hl : raw14212step1Labels = raw14212step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14212step0 raw14212step0Labels permutation37 permutation6
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw14213 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14213Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14213step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw14213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14213 raw14213Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw14213 raw14213Labels = mixedMoment B raw14213step0 raw14213step0Labels := by
      have hz : ∀ j, raw14213 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14213step0 = (fun i j => raw14213 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14213step0 raw14213; decide +kernel
      have hl : raw14213step0Labels = raw14213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14213 raw14213Labels permutation265 hz
    mixedMoment B raw14213step0 raw14213step0Labels = mixedMoment B raw14213step1 raw14213step1Labels := by
      have ha : raw14213step1 = (fun i j => raw14213step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14213step1 raw14213step0; decide +kernel
      have hl : raw14213step1Labels = raw14213step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14213step0 raw14213step0Labels permutation35 permutation6
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw14214 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14214Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14214step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14214 raw14214Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw14214 raw14214Labels = mixedMoment B raw14214step0 raw14214step0Labels := by
      have hz : ∀ j, raw14214 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14214step0 = (fun i j => raw14214 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14214step0 raw14214; decide +kernel
      have hl : raw14214step0Labels = raw14214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14214 raw14214Labels permutation265 hz
    mixedMoment B raw14214step0 raw14214step0Labels = mixedMoment B raw14214step1 raw14214step1Labels := by
      have ha : raw14214step1 = (fun i j => raw14214step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14214step1 raw14214step0; decide +kernel
      have hl : raw14214step1Labels = raw14214step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14214step0 raw14214step0Labels permutation36 permutation6
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw14215 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14215Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14215 raw14215Labels = mixedMoment B node2701 node2701Labels := by
  calc
    mixedMoment B raw14215 raw14215Labels = mixedMoment B raw14215step0 raw14215step0Labels := by
      have ha : raw14215step0 = (fun i j => raw14215 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14215step0 raw14215; decide +kernel
      have hl : raw14215step0Labels = raw14215Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14215 raw14215Labels permutation156 permutation6
    _ = mixedMoment B node2701 node2701Labels := by rfl

def raw14216 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14216Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -2, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw14216step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw14216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14216 raw14216Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw14216 raw14216Labels = mixedMoment B raw14216step0 raw14216step0Labels := by
      have hz : ∀ j, raw14216 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14216step0 = (fun i j => raw14216 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14216step0 raw14216; decide +kernel
      have hl : raw14216step0Labels = raw14216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14216 raw14216Labels permutation265 hz
    mixedMoment B raw14216step0 raw14216step0Labels = mixedMoment B raw14216step1 raw14216step1Labels := by
      have ha : raw14216step1 = (fun i j => raw14216step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14216step1 raw14216step0; decide +kernel
      have hl : raw14216step1Labels = raw14216step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14216step0 raw14216step0Labels permutation36 permutation6
    _ = mixedMoment B node2682 node2682Labels := by rfl

def raw14217 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14217Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14217step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14217 raw14217Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw14217 raw14217Labels = mixedMoment B raw14217step0 raw14217step0Labels := by
      have hz : ∀ j, raw14217 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14217step0 = (fun i j => raw14217 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14217step0 raw14217; decide +kernel
      have hl : raw14217step0Labels = raw14217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14217 raw14217Labels permutation265 hz
    mixedMoment B raw14217step0 raw14217step0Labels = mixedMoment B raw14217step1 raw14217step1Labels := by
      have ha : raw14217step1 = (fun i j => raw14217step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14217step1 raw14217step0; decide +kernel
      have hl : raw14217step1Labels = raw14217step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14217step0 raw14217step0Labels permutation35 permutation6
    _ = mixedMoment B node2227 node2227Labels := by rfl

def raw14218 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14218Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14218 raw14218Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw14218 raw14218Labels = mixedMoment B raw14218step0 raw14218step0Labels := by
      have ha : raw14218step0 = (fun i j => raw14218 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14218step0 raw14218; decide +kernel
      have hl : raw14218step0Labels = raw14218Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14218 raw14218Labels permutation155 permutation6
    _ = mixedMoment B node2703 node2703Labels := by rfl

def raw14219 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14219Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14219step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14219 raw14219Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw14219 raw14219Labels = mixedMoment B raw14219step0 raw14219step0Labels := by
      have hz : ∀ j, raw14219 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14219step0 = (fun i j => raw14219 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14219step0 raw14219; decide +kernel
      have hl : raw14219step0Labels = raw14219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14219 raw14219Labels permutation265 hz
    mixedMoment B raw14219step0 raw14219step0Labels = mixedMoment B raw14219step1 raw14219step1Labels := by
      have ha : raw14219step1 = (fun i j => raw14219step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14219step1 raw14219step0; decide +kernel
      have hl : raw14219step1Labels = raw14219step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14219step0 raw14219step0Labels permutation35 permutation6
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw14220 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw14220Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw14220step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14220 raw14220Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw14220 raw14220Labels = mixedMoment B raw14220step0 raw14220step0Labels := by
      have hz : ∀ j, raw14220 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14220step0 = (fun i j => raw14220 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14220step0 raw14220; decide +kernel
      have hl : raw14220step0Labels = raw14220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14220 raw14220Labels permutation265 hz
    mixedMoment B raw14220step0 raw14220step0Labels = mixedMoment B raw14220step1 raw14220step1Labels := by
      have ha : raw14220step1 = (fun i j => raw14220step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14220step1 raw14220step0; decide +kernel
      have hl : raw14220step1Labels = raw14220step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14220step0 raw14220step0Labels permutation35 permutation6
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw14221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14221 raw14221Labels = mixedMoment B node5427 node5427Labels := by
  calc
    _ = mixedMoment B node5427 node5427Labels := by rfl

def raw14222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14222step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw14222step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw14222step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw14222step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14222 raw14222Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw14222 raw14222Labels = mixedMoment B raw14222step0 raw14222step0Labels := by
      have hz : ∀ j, raw14222 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14222step0 = (fun i j => raw14222 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14222step0 raw14222; decide +kernel
      have hl : raw14222step0Labels = raw14222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14222 raw14222Labels permutation265 hz
    mixedMoment B raw14222step0 raw14222step0Labels = mixedMoment B raw14222step1 raw14222step1Labels := by
      have hz : ∀ i, raw14222step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw14222step1 = (fun i j => raw14222step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw14222step1 raw14222step0; decide +kernel
      have hl : raw14222step1Labels = (fun j => raw14222step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14222step0 raw14222step0Labels permutation4 hz
    mixedMoment B raw14222step1 raw14222step1Labels = mixedMoment B raw14222step2 raw14222step2Labels := by
      have ha : raw14222step2 = raw14222step1 := by apply Matrix.ext; unfold raw14222step2 raw14222step1; decide +kernel
      have hl : raw14222step1Labels = labelEmbedding2 ∘ raw14222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14222step1 raw14222step1Labels raw14222step2Labels labelEmbedding2 hl
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw14223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14223step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14223step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14223step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14223step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14223 raw14223Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw14223 raw14223Labels = mixedMoment B raw14223step0 raw14223step0Labels := by
      have hz : ∀ j, raw14223 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14223step0 = (fun i j => raw14223 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14223step0 raw14223; decide +kernel
      have hl : raw14223step0Labels = raw14223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14223 raw14223Labels permutation265 hz
    mixedMoment B raw14223step0 raw14223step0Labels = mixedMoment B raw14223step1 raw14223step1Labels := by
      have ha : raw14223step1 = (fun i j => raw14223step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14223step1 raw14223step0; decide +kernel
      have hl : raw14223step1Labels = raw14223step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14223step0 raw14223step0Labels permutation32 permutation7
    mixedMoment B raw14223step1 raw14223step1Labels = mixedMoment B raw14223step2 raw14223step2Labels := by
      have ha : raw14223step2 = -raw14223step1 := by apply Matrix.ext; change ∀ i j, raw14223step2 i j = -(raw14223step1 i j); unfold raw14223step2 raw14223step1; decide +kernel
      have hl : raw14223step2Labels = raw14223step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14223step2 raw14223step2Labels = mixedMoment B raw14223step3 raw14223step3Labels := by
      have ha : raw14223step3 = raw14223step2 := by apply Matrix.ext; unfold raw14223step3 raw14223step2; decide +kernel
      have hl : raw14223step2Labels = labelEmbedding10 ∘ raw14223step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14223step2 raw14223step2Labels raw14223step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw14224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14224step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14224step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14224step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14224step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14224 raw14224Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw14224 raw14224Labels = mixedMoment B raw14224step0 raw14224step0Labels := by
      have hz : ∀ j, raw14224 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14224step0 = (fun i j => raw14224 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14224step0 raw14224; decide +kernel
      have hl : raw14224step0Labels = raw14224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14224 raw14224Labels permutation265 hz
    mixedMoment B raw14224step0 raw14224step0Labels = mixedMoment B raw14224step1 raw14224step1Labels := by
      have ha : raw14224step1 = (fun i j => raw14224step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14224step1 raw14224step0; decide +kernel
      have hl : raw14224step1Labels = raw14224step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14224step0 raw14224step0Labels permutation34 permutation7
    mixedMoment B raw14224step1 raw14224step1Labels = mixedMoment B raw14224step2 raw14224step2Labels := by
      have ha : raw14224step2 = -raw14224step1 := by apply Matrix.ext; change ∀ i j, raw14224step2 i j = -(raw14224step1 i j); unfold raw14224step2 raw14224step1; decide +kernel
      have hl : raw14224step2Labels = raw14224step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14224step2 raw14224step2Labels = mixedMoment B raw14224step3 raw14224step3Labels := by
      have ha : raw14224step3 = raw14224step2 := by apply Matrix.ext; unfold raw14224step3 raw14224step2; decide +kernel
      have hl : raw14224step2Labels = labelEmbedding10 ∘ raw14224step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14224step2 raw14224step2Labels raw14224step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw14225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14225step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14225step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14225step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14225step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14225step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14225 raw14225Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw14225 raw14225Labels = mixedMoment B raw14225step0 raw14225step0Labels := by
      have hz : ∀ j, raw14225 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14225step0 = (fun i j => raw14225 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14225step0 raw14225; decide +kernel
      have hl : raw14225step0Labels = raw14225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14225 raw14225Labels permutation265 hz
    mixedMoment B raw14225step0 raw14225step0Labels = mixedMoment B raw14225step1 raw14225step1Labels := by
      have ha : raw14225step1 = (fun i j => raw14225step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14225step1 raw14225step0; decide +kernel
      have hl : raw14225step1Labels = raw14225step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14225step0 raw14225step0Labels permutation36 permutation7
    mixedMoment B raw14225step1 raw14225step1Labels = mixedMoment B raw14225step2 raw14225step2Labels := by
      have ha : raw14225step2 = -raw14225step1 := by apply Matrix.ext; change ∀ i j, raw14225step2 i j = -(raw14225step1 i j); unfold raw14225step2 raw14225step1; decide +kernel
      have hl : raw14225step2Labels = raw14225step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14225step2 raw14225step2Labels = mixedMoment B raw14225step3 raw14225step3Labels := by
      have ha : raw14225step3 = raw14225step2 := by apply Matrix.ext; unfold raw14225step3 raw14225step2; decide +kernel
      have hl : raw14225step2Labels = labelEmbedding10 ∘ raw14225step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14225step2 raw14225step2Labels raw14225step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw14226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14226 raw14226Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw14226 raw14226Labels = mixedMoment B raw14226step0 raw14226step0Labels := by
      have ha : raw14226step0 = (fun i j => raw14226 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14226step0 raw14226; decide +kernel
      have hl : raw14226step0Labels = raw14226Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14226 raw14226Labels permutation176 permutation2
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw14227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14227 raw14227Labels = mixedMoment B node5100 node5100Labels := by
  calc
    mixedMoment B raw14227 raw14227Labels = mixedMoment B raw14227step0 raw14227step0Labels := by
      have ha : raw14227step0 = (fun i j => raw14227 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14227step0 raw14227; decide +kernel
      have hl : raw14227step0Labels = raw14227Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14227 raw14227Labels permutation176 permutation2
    _ = mixedMoment B node5100 node5100Labels := by rfl

def raw14228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14228 raw14228Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw14228 raw14228Labels = mixedMoment B raw14228step0 raw14228step0Labels := by
      have ha : raw14228step0 = (fun i j => raw14228 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14228step0 raw14228; decide +kernel
      have hl : raw14228step0Labels = raw14228Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14228 raw14228Labels permutation182 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw14229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14229 raw14229Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw14229 raw14229Labels = mixedMoment B raw14229step0 raw14229step0Labels := by
      have ha : raw14229step0 = (fun i j => raw14229 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14229step0 raw14229; decide +kernel
      have hl : raw14229step0Labels = raw14229Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14229 raw14229Labels permutation188 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw14230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14230 raw14230Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw14230 raw14230Labels = mixedMoment B raw14230step0 raw14230step0Labels := by
      have ha : raw14230step0 = (fun i j => raw14230 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14230step0 raw14230; decide +kernel
      have hl : raw14230step0Labels = raw14230Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14230 raw14230Labels permutation194 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw14231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14231 raw14231Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw14231 raw14231Labels = mixedMoment B raw14231step0 raw14231step0Labels := by
      have hz : ∀ j, raw14231 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14231step0 = (fun i j => raw14231 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14231step0 raw14231; decide +kernel
      have hl : raw14231step0Labels = raw14231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14231 raw14231Labels permutation265 hz
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw14232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14232 raw14232Labels = mixedMoment B node5162 node5162Labels := by
  calc
    _ = mixedMoment B node5162 node5162Labels := by rfl

def raw14233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14233 raw14233Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw14233 raw14233Labels = mixedMoment B raw14233step0 raw14233step0Labels := by
      have hz : ∀ j, raw14233 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14233step0 = (fun i j => raw14233 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14233step0 raw14233; decide +kernel
      have hl : raw14233step0Labels = raw14233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14233 raw14233Labels permutation265 hz
    mixedMoment B raw14233step0 raw14233step0Labels = mixedMoment B raw14233step1 raw14233step1Labels := by
      have ha : raw14233step1 = (fun i j => raw14233step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14233step1 raw14233step0; decide +kernel
      have hl : raw14233step1Labels = raw14233step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14233step0 raw14233step0Labels permutation38 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw14234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14234 raw14234Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw14234 raw14234Labels = mixedMoment B raw14234step0 raw14234step0Labels := by
      have hz : ∀ j, raw14234 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14234step0 = (fun i j => raw14234 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14234step0 raw14234; decide +kernel
      have hl : raw14234step0Labels = raw14234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14234 raw14234Labels permutation265 hz
    mixedMoment B raw14234step0 raw14234step0Labels = mixedMoment B raw14234step1 raw14234step1Labels := by
      have ha : raw14234step1 = (fun i j => raw14234step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14234step1 raw14234step0; decide +kernel
      have hl : raw14234step1Labels = raw14234step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14234step0 raw14234step0Labels permutation44 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw14235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14235 raw14235Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw14235 raw14235Labels = mixedMoment B raw14235step0 raw14235step0Labels := by
      have hz : ∀ j, raw14235 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14235step0 = (fun i j => raw14235 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14235step0 raw14235; decide +kernel
      have hl : raw14235step0Labels = raw14235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14235 raw14235Labels permutation265 hz
    mixedMoment B raw14235step0 raw14235step0Labels = mixedMoment B raw14235step1 raw14235step1Labels := by
      have ha : raw14235step1 = (fun i j => raw14235step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14235step1 raw14235step0; decide +kernel
      have hl : raw14235step1Labels = raw14235step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14235step0 raw14235step0Labels permutation50 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw14236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14236 raw14236Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw14236 raw14236Labels = mixedMoment B raw14236step0 raw14236step0Labels := by
      have hz : ∀ j, raw14236 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14236step0 = (fun i j => raw14236 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14236step0 raw14236; decide +kernel
      have hl : raw14236step0Labels = raw14236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14236 raw14236Labels permutation265 hz
    mixedMoment B raw14236step0 raw14236step0Labels = mixedMoment B raw14236step1 raw14236step1Labels := by
      have ha : raw14236step1 = (fun i j => raw14236step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14236step1 raw14236step0; decide +kernel
      have hl : raw14236step1Labels = raw14236step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14236step0 raw14236step0Labels permutation35 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw14237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14237 raw14237Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw14237 raw14237Labels = mixedMoment B raw14237step0 raw14237step0Labels := by
      have ha : raw14237step0 = (fun i j => raw14237 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14237step0 raw14237; decide +kernel
      have hl : raw14237step0Labels = raw14237Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14237 raw14237Labels permutation155 permutation2
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw14238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14238 raw14238Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw14238 raw14238Labels = mixedMoment B raw14238step0 raw14238step0Labels := by
      have hz : ∀ j, raw14238 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14238step0 = (fun i j => raw14238 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14238step0 raw14238; decide +kernel
      have hl : raw14238step0Labels = raw14238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14238 raw14238Labels permutation265 hz
    mixedMoment B raw14238step0 raw14238step0Labels = mixedMoment B raw14238step1 raw14238step1Labels := by
      have ha : raw14238step1 = (fun i j => raw14238step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14238step1 raw14238step0; decide +kernel
      have hl : raw14238step1Labels = raw14238step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14238step0 raw14238step0Labels permutation35 permutation2
    _ = mixedMoment B node5104 node5104Labels := by rfl

def raw14239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw14239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14239 raw14239Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw14239 raw14239Labels = mixedMoment B raw14239step0 raw14239step0Labels := by
      have hz : ∀ j, raw14239 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14239step0 = (fun i j => raw14239 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14239step0 raw14239; decide +kernel
      have hl : raw14239step0Labels = raw14239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14239 raw14239Labels permutation265 hz
    mixedMoment B raw14239step0 raw14239step0Labels = mixedMoment B raw14239step1 raw14239step1Labels := by
      have ha : raw14239step1 = (fun i j => raw14239step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14239step1 raw14239step0; decide +kernel
      have hl : raw14239step1Labels = raw14239step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14239step0 raw14239step0Labels permutation35 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw14240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw14240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14240 raw14240Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw14240 raw14240Labels = mixedMoment B raw14240step0 raw14240step0Labels := by
      have hz : ∀ j, raw14240 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14240step0 = (fun i j => raw14240 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14240step0 raw14240; decide +kernel
      have hl : raw14240step0Labels = raw14240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14240 raw14240Labels permutation265 hz
    mixedMoment B raw14240step0 raw14240step0Labels = mixedMoment B raw14240step1 raw14240step1Labels := by
      have ha : raw14240step1 = (fun i j => raw14240step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14240step1 raw14240step0; decide +kernel
      have hl : raw14240step1Labels = raw14240step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14240step0 raw14240step0Labels permutation37 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw14241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14241 raw14241Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw14241 raw14241Labels = mixedMoment B raw14241step0 raw14241step0Labels := by
      have hz : ∀ j, raw14241 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14241step0 = (fun i j => raw14241 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14241step0 raw14241; decide +kernel
      have hl : raw14241step0Labels = raw14241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14241 raw14241Labels permutation265 hz
    mixedMoment B raw14241step0 raw14241step0Labels = mixedMoment B raw14241step1 raw14241step1Labels := by
      have ha : raw14241step1 = (fun i j => raw14241step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14241step1 raw14241step0; decide +kernel
      have hl : raw14241step1Labels = raw14241step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14241step0 raw14241step0Labels permutation33 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw14242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14242 raw14242Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw14242 raw14242Labels = mixedMoment B raw14242step0 raw14242step0Labels := by
      have ha : raw14242step0 = (fun i j => raw14242 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14242step0 raw14242; decide +kernel
      have hl : raw14242step0Labels = raw14242Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14242 raw14242Labels permutation153 permutation2
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw14243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14243 raw14243Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw14243 raw14243Labels = mixedMoment B raw14243step0 raw14243step0Labels := by
      have hz : ∀ j, raw14243 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14243step0 = (fun i j => raw14243 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14243step0 raw14243; decide +kernel
      have hl : raw14243step0Labels = raw14243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14243 raw14243Labels permutation265 hz
    mixedMoment B raw14243step0 raw14243step0Labels = mixedMoment B raw14243step1 raw14243step1Labels := by
      have ha : raw14243step1 = (fun i j => raw14243step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14243step1 raw14243step0; decide +kernel
      have hl : raw14243step1Labels = raw14243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14243step0 raw14243step0Labels permutation33 permutation2
    _ = mixedMoment B node5104 node5104Labels := by rfl

def raw14244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14244 raw14244Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw14244 raw14244Labels = mixedMoment B raw14244step0 raw14244step0Labels := by
      have hz : ∀ j, raw14244 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14244step0 = (fun i j => raw14244 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14244step0 raw14244; decide +kernel
      have hl : raw14244step0Labels = raw14244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14244 raw14244Labels permutation265 hz
    mixedMoment B raw14244step0 raw14244step0Labels = mixedMoment B raw14244step1 raw14244step1Labels := by
      have ha : raw14244step1 = (fun i j => raw14244step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14244step1 raw14244step0; decide +kernel
      have hl : raw14244step1Labels = raw14244step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14244step0 raw14244step0Labels permutation33 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw14245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw14245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw14245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14245 raw14245Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw14245 raw14245Labels = mixedMoment B raw14245step0 raw14245step0Labels := by
      have hz : ∀ j, raw14245 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14245step0 = (fun i j => raw14245 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14245step0 raw14245; decide +kernel
      have hl : raw14245step0Labels = raw14245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14245 raw14245Labels permutation265 hz
    mixedMoment B raw14245step0 raw14245step0Labels = mixedMoment B raw14245step1 raw14245step1Labels := by
      have ha : raw14245step1 = (fun i j => raw14245step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14245step1 raw14245step0; decide +kernel
      have hl : raw14245step1Labels = raw14245step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14245step0 raw14245step0Labels permutation36 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw14246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14246 raw14246Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw14246 raw14246Labels = mixedMoment B raw14246step0 raw14246step0Labels := by
      have hz : ∀ j, raw14246 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14246step0 = (fun i j => raw14246 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14246step0 raw14246; decide +kernel
      have hl : raw14246step0Labels = raw14246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14246 raw14246Labels permutation265 hz
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw14247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14247 raw14247Labels = mixedMoment B node5137 node5137Labels := by
  calc
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw14248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14248 raw14248Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw14248 raw14248Labels = mixedMoment B raw14248step0 raw14248step0Labels := by
      have hz : ∀ j, raw14248 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14248step0 = (fun i j => raw14248 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14248step0 raw14248; decide +kernel
      have hl : raw14248step0Labels = raw14248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14248 raw14248Labels permutation265 hz
    _ = mixedMoment B node5104 node5104Labels := by rfl

def raw14249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14249 raw14249Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw14249 raw14249Labels = mixedMoment B raw14249step0 raw14249step0Labels := by
      have hz : ∀ j, raw14249 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14249step0 = (fun i j => raw14249 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14249step0 raw14249; decide +kernel
      have hl : raw14249step0Labels = raw14249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14249 raw14249Labels permutation265 hz
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw14250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw14250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw14250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14250 raw14250Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw14250 raw14250Labels = mixedMoment B raw14250step0 raw14250step0Labels := by
      have hz : ∀ j, raw14250 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14250step0 = (fun i j => raw14250 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14250step0 raw14250; decide +kernel
      have hl : raw14250step0Labels = raw14250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14250 raw14250Labels permutation265 hz
    mixedMoment B raw14250step0 raw14250step0Labels = mixedMoment B raw14250step1 raw14250step1Labels := by
      have ha : raw14250step1 = (fun i j => raw14250step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14250step1 raw14250step0; decide +kernel
      have hl : raw14250step1Labels = raw14250step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14250step0 raw14250step0Labels permutation34 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw14251 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14251step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14251step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14251 raw14251Labels = mixedMoment B node5283 node5283Labels := by
  calc
    mixedMoment B raw14251 raw14251Labels = mixedMoment B raw14251step0 raw14251step0Labels := by
      have ha : raw14251step0 = (fun i j => raw14251 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14251step0 raw14251; decide +kernel
      have hl : raw14251step0Labels = raw14251Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14251 raw14251Labels permutation152 permutation7
    mixedMoment B raw14251step0 raw14251step0Labels = mixedMoment B raw14251step1 raw14251step1Labels := by
      have ha : raw14251step1 = raw14251step0 := by apply Matrix.ext; unfold raw14251step1 raw14251step0; decide +kernel
      have hl : raw14251step0Labels = labelEmbedding10 ∘ raw14251step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14251step0 raw14251step0Labels raw14251step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5283 node5283Labels := by rfl

def raw14252 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14252step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14252 raw14252Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw14252 raw14252Labels = mixedMoment B raw14252step0 raw14252step0Labels := by
      have hz : ∀ j, raw14252 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14252step0 = (fun i j => raw14252 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14252step0 raw14252; decide +kernel
      have hl : raw14252step0Labels = raw14252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14252 raw14252Labels permutation265 hz
    mixedMoment B raw14252step0 raw14252step0Labels = mixedMoment B raw14252step1 raw14252step1Labels := by
      have ha : raw14252step1 = (fun i j => raw14252step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14252step1 raw14252step0; decide +kernel
      have hl : raw14252step1Labels = raw14252step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14252step0 raw14252step0Labels permutation32 permutation7
    mixedMoment B raw14252step1 raw14252step1Labels = mixedMoment B raw14252step2 raw14252step2Labels := by
      have ha : raw14252step2 = raw14252step1 := by apply Matrix.ext; unfold raw14252step2 raw14252step1; decide +kernel
      have hl : raw14252step1Labels = labelEmbedding10 ∘ raw14252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14252step1 raw14252step1Labels raw14252step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw14253 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14253step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14253 raw14253Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw14253 raw14253Labels = mixedMoment B raw14253step0 raw14253step0Labels := by
      have hz : ∀ j, raw14253 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14253step0 = (fun i j => raw14253 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14253step0 raw14253; decide +kernel
      have hl : raw14253step0Labels = raw14253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14253 raw14253Labels permutation265 hz
    mixedMoment B raw14253step0 raw14253step0Labels = mixedMoment B raw14253step1 raw14253step1Labels := by
      have ha : raw14253step1 = (fun i j => raw14253step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14253step1 raw14253step0; decide +kernel
      have hl : raw14253step1Labels = raw14253step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14253step0 raw14253step0Labels permutation35 permutation7
    mixedMoment B raw14253step1 raw14253step1Labels = mixedMoment B raw14253step2 raw14253step2Labels := by
      have ha : raw14253step2 = raw14253step1 := by apply Matrix.ext; unfold raw14253step2 raw14253step1; decide +kernel
      have hl : raw14253step1Labels = labelEmbedding10 ∘ raw14253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14253step1 raw14253step1Labels raw14253step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw14254 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw14254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw14254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14254step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14254 raw14254Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw14254 raw14254Labels = mixedMoment B raw14254step0 raw14254step0Labels := by
      have hz : ∀ j, raw14254 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14254step0 = (fun i j => raw14254 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14254step0 raw14254; decide +kernel
      have hl : raw14254step0Labels = raw14254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14254 raw14254Labels permutation265 hz
    mixedMoment B raw14254step0 raw14254step0Labels = mixedMoment B raw14254step1 raw14254step1Labels := by
      have ha : raw14254step1 = (fun i j => raw14254step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14254step1 raw14254step0; decide +kernel
      have hl : raw14254step1Labels = raw14254step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14254step0 raw14254step0Labels permutation33 permutation7
    mixedMoment B raw14254step1 raw14254step1Labels = mixedMoment B raw14254step2 raw14254step2Labels := by
      have ha : raw14254step2 = raw14254step1 := by apply Matrix.ext; unfold raw14254step2 raw14254step1; decide +kernel
      have hl : raw14254step1Labels = labelEmbedding10 ∘ raw14254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14254step1 raw14254step1Labels raw14254step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw14255 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14255step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14255step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw14255step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw14255step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14255step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw14255step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14255step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14255 raw14255Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw14255 raw14255Labels = mixedMoment B raw14255step0 raw14255step0Labels := by
      have hz : ∀ j, raw14255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14255step0 = (fun i j => raw14255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14255step0 raw14255; decide +kernel
      have hl : raw14255step0Labels = raw14255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14255 raw14255Labels permutation346 hz
    mixedMoment B raw14255step0 raw14255step0Labels = mixedMoment B raw14255step1 raw14255step1Labels := by
      have hz : ∀ j, raw14255step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14255step1 = (fun i j => raw14255step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14255step1 raw14255step0; decide +kernel
      have hl : raw14255step1Labels = raw14255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14255step0 raw14255step0Labels permutation56 hz
    mixedMoment B raw14255step1 raw14255step1Labels = mixedMoment B raw14255step2 raw14255step2Labels := by
      have hz : ∀ i, raw14255step1 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw14255step2 = (fun i j => raw14255step1 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw14255step2 raw14255step1; decide +kernel
      have hl : raw14255step2Labels = (fun j => raw14255step1Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14255step1 raw14255step1Labels permutation2 hz
    mixedMoment B raw14255step2 raw14255step2Labels = mixedMoment B raw14255step3 raw14255step3Labels := by
      have ha : raw14255step3 = -raw14255step2 := by apply Matrix.ext; change ∀ i j, raw14255step3 i j = -(raw14255step2 i j); unfold raw14255step3 raw14255step2; decide +kernel
      have hl : raw14255step3Labels = raw14255step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14255step3 raw14255step3Labels = mixedMoment B raw14255step4 raw14255step4Labels := by
      have ha : raw14255step4 = raw14255step3 := by apply Matrix.ext; unfold raw14255step4 raw14255step3; decide +kernel
      have hl : raw14255step3Labels = labelEmbedding3 ∘ raw14255step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14255step3 raw14255step3Labels raw14255step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw14256 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw14256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14256step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14256step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14256 raw14256Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw14256 raw14256Labels = mixedMoment B raw14256step0 raw14256step0Labels := by
      have hz : ∀ j, raw14256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14256step0 = (fun i j => raw14256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14256step0 raw14256; decide +kernel
      have hl : raw14256step0Labels = raw14256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14256 raw14256Labels permutation346 hz
    mixedMoment B raw14256step0 raw14256step0Labels = mixedMoment B raw14256step1 raw14256step1Labels := by
      have ha : raw14256step1 = (fun i j => raw14256step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14256step1 raw14256step0; decide +kernel
      have hl : raw14256step1Labels = raw14256step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14256step0 raw14256step0Labels permutation32 permutation6
    mixedMoment B raw14256step1 raw14256step1Labels = mixedMoment B raw14256step2 raw14256step2Labels := by
      have ha : raw14256step2 = raw14256step1 := by apply Matrix.ext; unfold raw14256step2 raw14256step1; decide +kernel
      have hl : raw14256step1Labels = labelEmbedding9 ∘ raw14256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14256step1 raw14256step1Labels raw14256step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw14257 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14257step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14257step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14257step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14257step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14257 raw14257Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw14257 raw14257Labels = mixedMoment B raw14257step0 raw14257step0Labels := by
      have hz : ∀ j, raw14257 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14257step0 = (fun i j => raw14257 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14257step0 raw14257; decide +kernel
      have hl : raw14257step0Labels = raw14257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14257 raw14257Labels permutation265 hz
    mixedMoment B raw14257step0 raw14257step0Labels = mixedMoment B raw14257step1 raw14257step1Labels := by
      have ha : raw14257step1 = (fun i j => raw14257step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14257step1 raw14257step0; decide +kernel
      have hl : raw14257step1Labels = raw14257step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14257step0 raw14257step0Labels permutation33 permutation4
    mixedMoment B raw14257step1 raw14257step1Labels = mixedMoment B raw14257step2 raw14257step2Labels := by
      have ha : raw14257step2 = -raw14257step1 := by apply Matrix.ext; change ∀ i j, raw14257step2 i j = -(raw14257step1 i j); unfold raw14257step2 raw14257step1; decide +kernel
      have hl : raw14257step2Labels = raw14257step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14257step2 raw14257step2Labels = mixedMoment B raw14257step3 raw14257step3Labels := by
      have ha : raw14257step3 = raw14257step2 := by apply Matrix.ext; unfold raw14257step3 raw14257step2; decide +kernel
      have hl : raw14257step2Labels = labelEmbedding7 ∘ raw14257step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14257step2 raw14257step2Labels raw14257step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw14258 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14258step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14258 raw14258Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw14258 raw14258Labels = mixedMoment B raw14258step0 raw14258step0Labels := by
      have ha : raw14258step0 = (fun i j => raw14258 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14258step0 raw14258; decide +kernel
      have hl : raw14258step0Labels = raw14258Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14258 raw14258Labels permutation153 permutation6
    mixedMoment B raw14258step0 raw14258step0Labels = mixedMoment B raw14258step1 raw14258step1Labels := by
      have ha : raw14258step1 = raw14258step0 := by apply Matrix.ext; unfold raw14258step1 raw14258step0; decide +kernel
      have hl : raw14258step0Labels = labelEmbedding9 ∘ raw14258step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14258step0 raw14258step0Labels raw14258step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

def raw14259 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14259step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14259step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14259 raw14259Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw14259 raw14259Labels = mixedMoment B raw14259step0 raw14259step0Labels := by
      have hz : ∀ j, raw14259 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14259step0 = (fun i j => raw14259 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14259step0 raw14259; decide +kernel
      have hl : raw14259step0Labels = raw14259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14259 raw14259Labels permutation265 hz
    mixedMoment B raw14259step0 raw14259step0Labels = mixedMoment B raw14259step1 raw14259step1Labels := by
      have ha : raw14259step1 = (fun i j => raw14259step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14259step1 raw14259step0; decide +kernel
      have hl : raw14259step1Labels = raw14259step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14259step0 raw14259step0Labels permutation33 permutation6
    mixedMoment B raw14259step1 raw14259step1Labels = mixedMoment B raw14259step2 raw14259step2Labels := by
      have ha : raw14259step2 = raw14259step1 := by apply Matrix.ext; unfold raw14259step2 raw14259step1; decide +kernel
      have hl : raw14259step1Labels = labelEmbedding9 ∘ raw14259step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14259step1 raw14259step1Labels raw14259step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw14260 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw14260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14260step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14260 raw14260Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw14260 raw14260Labels = mixedMoment B raw14260step0 raw14260step0Labels := by
      have hz : ∀ j, raw14260 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14260step0 = (fun i j => raw14260 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14260step0 raw14260; decide +kernel
      have hl : raw14260step0Labels = raw14260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14260 raw14260Labels permutation265 hz
    mixedMoment B raw14260step0 raw14260step0Labels = mixedMoment B raw14260step1 raw14260step1Labels := by
      have ha : raw14260step1 = (fun i j => raw14260step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14260step1 raw14260step0; decide +kernel
      have hl : raw14260step1Labels = raw14260step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14260step0 raw14260step0Labels permutation33 permutation6
    mixedMoment B raw14260step1 raw14260step1Labels = mixedMoment B raw14260step2 raw14260step2Labels := by
      have ha : raw14260step2 = raw14260step1 := by apply Matrix.ext; unfold raw14260step2 raw14260step1; decide +kernel
      have hl : raw14260step1Labels = labelEmbedding9 ∘ raw14260step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14260step1 raw14260step1Labels raw14260step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw14261 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw14261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw14261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14261step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14261step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14261step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14261step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14261 raw14261Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw14261 raw14261Labels = mixedMoment B raw14261step0 raw14261step0Labels := by
      have hz : ∀ j, raw14261 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14261step0 = (fun i j => raw14261 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14261step0 raw14261; decide +kernel
      have hl : raw14261step0Labels = raw14261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14261 raw14261Labels permutation265 hz
    mixedMoment B raw14261step0 raw14261step0Labels = mixedMoment B raw14261step1 raw14261step1Labels := by
      have ha : raw14261step1 = (fun i j => raw14261step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14261step1 raw14261step0; decide +kernel
      have hl : raw14261step1Labels = raw14261step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14261step0 raw14261step0Labels permutation32 permutation4
    mixedMoment B raw14261step1 raw14261step1Labels = mixedMoment B raw14261step2 raw14261step2Labels := by
      have ha : raw14261step2 = -raw14261step1 := by apply Matrix.ext; change ∀ i j, raw14261step2 i j = -(raw14261step1 i j); unfold raw14261step2 raw14261step1; decide +kernel
      have hl : raw14261step2Labels = raw14261step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14261step2 raw14261step2Labels = mixedMoment B raw14261step3 raw14261step3Labels := by
      have ha : raw14261step3 = raw14261step2 := by apply Matrix.ext; unfold raw14261step3 raw14261step2; decide +kernel
      have hl : raw14261step2Labels = labelEmbedding7 ∘ raw14261step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14261step2 raw14261step2Labels raw14261step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw14262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw14262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14262step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14262 raw14262Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw14262 raw14262Labels = mixedMoment B raw14262step0 raw14262step0Labels := by
      have ha : raw14262step0 = (fun i j => raw14262 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14262step0 raw14262; decide +kernel
      have hl : raw14262step0Labels = raw14262Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14262 raw14262Labels permutation152 permutation6
    mixedMoment B raw14262step0 raw14262step0Labels = mixedMoment B raw14262step1 raw14262step1Labels := by
      have ha : raw14262step1 = raw14262step0 := by apply Matrix.ext; unfold raw14262step1 raw14262step0; decide +kernel
      have hl : raw14262step0Labels = labelEmbedding9 ∘ raw14262step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14262step0 raw14262step0Labels raw14262step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

def raw14263 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw14263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw14263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14263step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw14263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14263 raw14263Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw14263 raw14263Labels = mixedMoment B raw14263step0 raw14263step0Labels := by
      have hz : ∀ j, raw14263 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14263step0 = (fun i j => raw14263 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14263step0 raw14263; decide +kernel
      have hl : raw14263step0Labels = raw14263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14263 raw14263Labels permutation265 hz
    mixedMoment B raw14263step0 raw14263step0Labels = mixedMoment B raw14263step1 raw14263step1Labels := by
      have ha : raw14263step1 = (fun i j => raw14263step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14263step1 raw14263step0; decide +kernel
      have hl : raw14263step1Labels = raw14263step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14263step0 raw14263step0Labels permutation32 permutation6
    mixedMoment B raw14263step1 raw14263step1Labels = mixedMoment B raw14263step2 raw14263step2Labels := by
      have ha : raw14263step2 = raw14263step1 := by apply Matrix.ext; unfold raw14263step2 raw14263step1; decide +kernel
      have hl : raw14263step1Labels = labelEmbedding9 ∘ raw14263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14263step1 raw14263step1Labels raw14263step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw14264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14264step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14264step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14264 raw14264Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw14264 raw14264Labels = mixedMoment B raw14264step0 raw14264step0Labels := by
      have ha : raw14264step0 = (fun i j => raw14264 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14264step0 raw14264; decide +kernel
      have hl : raw14264step0Labels = raw14264Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14264 raw14264Labels permutation240 permutation7
    mixedMoment B raw14264step0 raw14264step0Labels = mixedMoment B raw14264step1 raw14264step1Labels := by
      have ha : raw14264step1 = -raw14264step0 := by apply Matrix.ext; change ∀ i j, raw14264step1 i j = -(raw14264step0 i j); unfold raw14264step1 raw14264step0; decide +kernel
      have hl : raw14264step1Labels = raw14264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14264step1 raw14264step1Labels = mixedMoment B raw14264step2 raw14264step2Labels := by
      have ha : raw14264step2 = raw14264step1 := by apply Matrix.ext; unfold raw14264step2 raw14264step1; decide +kernel
      have hl : raw14264step1Labels = labelEmbedding10 ∘ raw14264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14264step1 raw14264step1Labels raw14264step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw14265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14265step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14265step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14265step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14265 raw14265Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw14265 raw14265Labels = mixedMoment B raw14265step0 raw14265step0Labels := by
      have ha : raw14265step0 = (fun i j => raw14265 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14265step0 raw14265; decide +kernel
      have hl : raw14265step0Labels = raw14265Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14265 raw14265Labels permutation242 permutation7
    mixedMoment B raw14265step0 raw14265step0Labels = mixedMoment B raw14265step1 raw14265step1Labels := by
      have ha : raw14265step1 = -raw14265step0 := by apply Matrix.ext; change ∀ i j, raw14265step1 i j = -(raw14265step0 i j); unfold raw14265step1 raw14265step0; decide +kernel
      have hl : raw14265step1Labels = raw14265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14265step1 raw14265step1Labels = mixedMoment B raw14265step2 raw14265step2Labels := by
      have ha : raw14265step2 = raw14265step1 := by apply Matrix.ext; unfold raw14265step2 raw14265step1; decide +kernel
      have hl : raw14265step1Labels = labelEmbedding10 ∘ raw14265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14265step1 raw14265step1Labels raw14265step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw14266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14266step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14266step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14266step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14266step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14266 raw14266Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw14266 raw14266Labels = mixedMoment B raw14266step0 raw14266step0Labels := by
      have hz : ∀ j, raw14266 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14266step0 = (fun i j => raw14266 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14266step0 raw14266; decide +kernel
      have hl : raw14266step0Labels = raw14266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14266 raw14266Labels permutation520 hz
    mixedMoment B raw14266step0 raw14266step0Labels = mixedMoment B raw14266step1 raw14266step1Labels := by
      have ha : raw14266step1 = (fun i j => raw14266step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14266step1 raw14266step0; decide +kernel
      have hl : raw14266step1Labels = raw14266step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14266step0 raw14266step0Labels permutation50 permutation7
    mixedMoment B raw14266step1 raw14266step1Labels = mixedMoment B raw14266step2 raw14266step2Labels := by
      have ha : raw14266step2 = -raw14266step1 := by apply Matrix.ext; change ∀ i j, raw14266step2 i j = -(raw14266step1 i j); unfold raw14266step2 raw14266step1; decide +kernel
      have hl : raw14266step2Labels = raw14266step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14266step2 raw14266step2Labels = mixedMoment B raw14266step3 raw14266step3Labels := by
      have ha : raw14266step3 = raw14266step2 := by apply Matrix.ext; unfold raw14266step3 raw14266step2; decide +kernel
      have hl : raw14266step2Labels = labelEmbedding10 ∘ raw14266step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14266step2 raw14266step2Labels raw14266step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw14267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14267step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14267step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14267step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14267step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14267 raw14267Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw14267 raw14267Labels = mixedMoment B raw14267step0 raw14267step0Labels := by
      have hz : ∀ j, raw14267 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14267step0 = (fun i j => raw14267 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14267step0 raw14267; decide +kernel
      have hl : raw14267step0Labels = raw14267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14267 raw14267Labels permutation590 hz
    mixedMoment B raw14267step0 raw14267step0Labels = mixedMoment B raw14267step1 raw14267step1Labels := by
      have ha : raw14267step1 = (fun i j => raw14267step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14267step1 raw14267step0; decide +kernel
      have hl : raw14267step1Labels = raw14267step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14267step0 raw14267step0Labels permutation50 permutation7
    mixedMoment B raw14267step1 raw14267step1Labels = mixedMoment B raw14267step2 raw14267step2Labels := by
      have ha : raw14267step2 = -raw14267step1 := by apply Matrix.ext; change ∀ i j, raw14267step2 i j = -(raw14267step1 i j); unfold raw14267step2 raw14267step1; decide +kernel
      have hl : raw14267step2Labels = raw14267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14267step2 raw14267step2Labels = mixedMoment B raw14267step3 raw14267step3Labels := by
      have ha : raw14267step3 = raw14267step2 := by apply Matrix.ext; unfold raw14267step3 raw14267step2; decide +kernel
      have hl : raw14267step2Labels = labelEmbedding10 ∘ raw14267step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14267step2 raw14267step2Labels raw14267step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw14268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14268 raw14268Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw14268 raw14268Labels = mixedMoment B raw14268step0 raw14268step0Labels := by
      have ha : raw14268step0 = (fun i j => raw14268 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14268step0 raw14268; decide +kernel
      have hl : raw14268step0Labels = raw14268Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14268 raw14268Labels permutation192 permutation2
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw14269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14269 raw14269Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw14269 raw14269Labels = mixedMoment B raw14269step0 raw14269step0Labels := by
      have ha : raw14269step0 = (fun i j => raw14269 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14269step0 raw14269; decide +kernel
      have hl : raw14269step0Labels = raw14269Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14269 raw14269Labels permutation192 permutation2
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw14270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14270 raw14270Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw14270 raw14270Labels = mixedMoment B raw14270step0 raw14270step0Labels := by
      have hz : ∀ j, raw14270 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14270step0 = (fun i j => raw14270 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14270step0 raw14270; decide +kernel
      have hl : raw14270step0Labels = raw14270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14270 raw14270Labels permutation520 hz
    mixedMoment B raw14270step0 raw14270step0Labels = mixedMoment B raw14270step1 raw14270step1Labels := by
      have ha : raw14270step1 = (fun i j => raw14270step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14270step1 raw14270step0; decide +kernel
      have hl : raw14270step1Labels = raw14270step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14270step0 raw14270step0Labels permutation42 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw14271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14271 raw14271Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw14271 raw14271Labels = mixedMoment B raw14271step0 raw14271step0Labels := by
      have hz : ∀ j, raw14271 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14271step0 = (fun i j => raw14271 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14271step0 raw14271; decide +kernel
      have hl : raw14271step0Labels = raw14271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14271 raw14271Labels permutation590 hz
    mixedMoment B raw14271step0 raw14271step0Labels = mixedMoment B raw14271step1 raw14271step1Labels := by
      have ha : raw14271step1 = (fun i j => raw14271step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14271step1 raw14271step0; decide +kernel
      have hl : raw14271step1Labels = raw14271step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14271step0 raw14271step0Labels permutation42 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw14272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14272 raw14272Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw14272 raw14272Labels = mixedMoment B raw14272step0 raw14272step0Labels := by
      have ha : raw14272step0 = (fun i j => raw14272 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14272step0 raw14272; decide +kernel
      have hl : raw14272step0Labels = raw14272Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14272 raw14272Labels permutation168 permutation2
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw14273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14273 raw14273Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw14273 raw14273Labels = mixedMoment B raw14273step0 raw14273step0Labels := by
      have ha : raw14273step0 = (fun i j => raw14273 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14273step0 raw14273; decide +kernel
      have hl : raw14273step0Labels = raw14273Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14273 raw14273Labels permutation168 permutation2
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw14274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14274 raw14274Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw14274 raw14274Labels = mixedMoment B raw14274step0 raw14274step0Labels := by
      have hz : ∀ j, raw14274 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14274step0 = (fun i j => raw14274 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14274step0 raw14274; decide +kernel
      have hl : raw14274step0Labels = raw14274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14274 raw14274Labels permutation520 hz
    mixedMoment B raw14274step0 raw14274step0Labels = mixedMoment B raw14274step1 raw14274step1Labels := by
      have ha : raw14274step1 = (fun i j => raw14274step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14274step1 raw14274step0; decide +kernel
      have hl : raw14274step1Labels = raw14274step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14274step0 raw14274step0Labels permutation36 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw14275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14275 raw14275Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw14275 raw14275Labels = mixedMoment B raw14275step0 raw14275step0Labels := by
      have hz : ∀ j, raw14275 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14275step0 = (fun i j => raw14275 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14275step0 raw14275; decide +kernel
      have hl : raw14275step0Labels = raw14275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14275 raw14275Labels permutation590 hz
    mixedMoment B raw14275step0 raw14275step0Labels = mixedMoment B raw14275step1 raw14275step1Labels := by
      have ha : raw14275step1 = (fun i j => raw14275step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14275step1 raw14275step0; decide +kernel
      have hl : raw14275step1Labels = raw14275step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14275step0 raw14275step0Labels permutation36 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw14276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14276 raw14276Labels = mixedMoment B node4438 node4438Labels := by
  calc
    mixedMoment B raw14276 raw14276Labels = mixedMoment B raw14276step0 raw14276step0Labels := by
      have ha : raw14276step0 = (fun i j => raw14276 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14276step0 raw14276; decide +kernel
      have hl : raw14276step0Labels = raw14276Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14276 raw14276Labels permutation155 permutation2
    _ = mixedMoment B node4438 node4438Labels := by rfl

def raw14277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14277 raw14277Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw14277 raw14277Labels = mixedMoment B raw14277step0 raw14277step0Labels := by
      have ha : raw14277step0 = (fun i j => raw14277 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14277step0 raw14277; decide +kernel
      have hl : raw14277step0Labels = raw14277Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14277 raw14277Labels permutation155 permutation2
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw14278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14278 raw14278Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw14278 raw14278Labels = mixedMoment B raw14278step0 raw14278step0Labels := by
      have ha : raw14278step0 = (fun i j => raw14278 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14278step0 raw14278; decide +kernel
      have hl : raw14278step0Labels = raw14278Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14278 raw14278Labels permutation179 permutation2
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw14279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14279 raw14279Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw14279 raw14279Labels = mixedMoment B raw14279step0 raw14279step0Labels := by
      have hz : ∀ j, raw14279 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14279step0 = (fun i j => raw14279 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14279step0 raw14279; decide +kernel
      have hl : raw14279step0Labels = raw14279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14279 raw14279Labels permutation520 hz
    mixedMoment B raw14279step0 raw14279step0Labels = mixedMoment B raw14279step1 raw14279step1Labels := by
      have ha : raw14279step1 = (fun i j => raw14279step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14279step1 raw14279step0; decide +kernel
      have hl : raw14279step1Labels = raw14279step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14279step0 raw14279step0Labels permutation33 permutation2
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw14280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14280 raw14280Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw14280 raw14280Labels = mixedMoment B raw14280step0 raw14280step0Labels := by
      have hz : ∀ j, raw14280 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14280step0 = (fun i j => raw14280 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14280step0 raw14280; decide +kernel
      have hl : raw14280step0Labels = raw14280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14280 raw14280Labels permutation590 hz
    mixedMoment B raw14280step0 raw14280step0Labels = mixedMoment B raw14280step1 raw14280step1Labels := by
      have ha : raw14280step1 = (fun i j => raw14280step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14280step1 raw14280step0; decide +kernel
      have hl : raw14280step1Labels = raw14280step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14280step0 raw14280step0Labels permutation33 permutation2
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw14281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw14281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14281 raw14281Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw14281 raw14281Labels = mixedMoment B raw14281step0 raw14281step0Labels := by
      have ha : raw14281step0 = (fun i j => raw14281 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14281step0 raw14281; decide +kernel
      have hl : raw14281step0Labels = raw14281Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14281 raw14281Labels permutation156 permutation2
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw14282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw14282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14282 raw14282Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw14282 raw14282Labels = mixedMoment B raw14282step0 raw14282step0Labels := by
      have ha : raw14282step0 = (fun i j => raw14282 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14282step0 raw14282; decide +kernel
      have hl : raw14282step0Labels = raw14282Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14282 raw14282Labels permutation156 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw14283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw14283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14283 raw14283Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw14283 raw14283Labels = mixedMoment B raw14283step0 raw14283step0Labels := by
      have ha : raw14283step0 = (fun i j => raw14283 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14283step0 raw14283; decide +kernel
      have hl : raw14283step0Labels = raw14283Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14283 raw14283Labels permutation180 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw14284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw14284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14284 raw14284Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw14284 raw14284Labels = mixedMoment B raw14284step0 raw14284step0Labels := by
      have hz : ∀ j, raw14284 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14284step0 = (fun i j => raw14284 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14284step0 raw14284; decide +kernel
      have hl : raw14284step0Labels = raw14284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14284 raw14284Labels permutation590 hz
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw14285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14285 raw14285Labels = mixedMoment B node4885 node4885Labels := by
  calc
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw14286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14286step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14286 raw14286Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw14286 raw14286Labels = mixedMoment B raw14286step0 raw14286step0Labels := by
      have ha : raw14286step0 = (fun i j => raw14286 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14286step0 raw14286; decide +kernel
      have hl : raw14286step0Labels = raw14286Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14286 raw14286Labels permutation240 permutation7
    mixedMoment B raw14286step0 raw14286step0Labels = mixedMoment B raw14286step1 raw14286step1Labels := by
      have ha : raw14286step1 = -raw14286step0 := by apply Matrix.ext; change ∀ i j, raw14286step1 i j = -(raw14286step0 i j); unfold raw14286step1 raw14286step0; decide +kernel
      have hl : raw14286step1Labels = raw14286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14286step1 raw14286step1Labels = mixedMoment B raw14286step2 raw14286step2Labels := by
      have ha : raw14286step2 = raw14286step1 := by apply Matrix.ext; unfold raw14286step2 raw14286step1; decide +kernel
      have hl : raw14286step1Labels = labelEmbedding1 ∘ raw14286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14286step1 raw14286step1Labels raw14286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw14287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14287Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14287step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14287step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14287step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14287 raw14287Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw14287 raw14287Labels = mixedMoment B raw14287step0 raw14287step0Labels := by
      have ha : raw14287step0 = (fun i j => raw14287 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14287step0 raw14287; decide +kernel
      have hl : raw14287step0Labels = raw14287Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14287 raw14287Labels permutation242 permutation7
    mixedMoment B raw14287step0 raw14287step0Labels = mixedMoment B raw14287step1 raw14287step1Labels := by
      have ha : raw14287step1 = -raw14287step0 := by apply Matrix.ext; change ∀ i j, raw14287step1 i j = -(raw14287step0 i j); unfold raw14287step1 raw14287step0; decide +kernel
      have hl : raw14287step1Labels = raw14287step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14287step1 raw14287step1Labels = mixedMoment B raw14287step2 raw14287step2Labels := by
      have ha : raw14287step2 = raw14287step1 := by apply Matrix.ext; unfold raw14287step2 raw14287step1; decide +kernel
      have hl : raw14287step1Labels = labelEmbedding1 ∘ raw14287step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14287step1 raw14287step1Labels raw14287step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw14288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14288step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14288step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14288step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14288step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14288 raw14288Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw14288 raw14288Labels = mixedMoment B raw14288step0 raw14288step0Labels := by
      have hz : ∀ j, raw14288 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14288step0 = (fun i j => raw14288 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14288step0 raw14288; decide +kernel
      have hl : raw14288step0Labels = raw14288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14288 raw14288Labels permutation520 hz
    mixedMoment B raw14288step0 raw14288step0Labels = mixedMoment B raw14288step1 raw14288step1Labels := by
      have ha : raw14288step1 = (fun i j => raw14288step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14288step1 raw14288step0; decide +kernel
      have hl : raw14288step1Labels = raw14288step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14288step0 raw14288step0Labels permutation50 permutation7
    mixedMoment B raw14288step1 raw14288step1Labels = mixedMoment B raw14288step2 raw14288step2Labels := by
      have ha : raw14288step2 = -raw14288step1 := by apply Matrix.ext; change ∀ i j, raw14288step2 i j = -(raw14288step1 i j); unfold raw14288step2 raw14288step1; decide +kernel
      have hl : raw14288step2Labels = raw14288step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14288step2 raw14288step2Labels = mixedMoment B raw14288step3 raw14288step3Labels := by
      have ha : raw14288step3 = raw14288step2 := by apply Matrix.ext; unfold raw14288step3 raw14288step2; decide +kernel
      have hl : raw14288step2Labels = labelEmbedding1 ∘ raw14288step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14288step2 raw14288step2Labels raw14288step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw14289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14289step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14289step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14289step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14289 raw14289Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw14289 raw14289Labels = mixedMoment B raw14289step0 raw14289step0Labels := by
      have hz : ∀ j, raw14289 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14289step0 = (fun i j => raw14289 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14289step0 raw14289; decide +kernel
      have hl : raw14289step0Labels = raw14289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14289 raw14289Labels permutation590 hz
    mixedMoment B raw14289step0 raw14289step0Labels = mixedMoment B raw14289step1 raw14289step1Labels := by
      have ha : raw14289step1 = (fun i j => raw14289step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14289step1 raw14289step0; decide +kernel
      have hl : raw14289step1Labels = raw14289step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14289step0 raw14289step0Labels permutation50 permutation7
    mixedMoment B raw14289step1 raw14289step1Labels = mixedMoment B raw14289step2 raw14289step2Labels := by
      have ha : raw14289step2 = -raw14289step1 := by apply Matrix.ext; change ∀ i j, raw14289step2 i j = -(raw14289step1 i j); unfold raw14289step2 raw14289step1; decide +kernel
      have hl : raw14289step2Labels = raw14289step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14289step2 raw14289step2Labels = mixedMoment B raw14289step3 raw14289step3Labels := by
      have ha : raw14289step3 = raw14289step2 := by apply Matrix.ext; unfold raw14289step3 raw14289step2; decide +kernel
      have hl : raw14289step2Labels = labelEmbedding1 ∘ raw14289step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14289step2 raw14289step2Labels raw14289step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw14290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14290step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14290 raw14290Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw14290 raw14290Labels = mixedMoment B raw14290step0 raw14290step0Labels := by
      have ha : raw14290step0 = (fun i j => raw14290 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14290step0 raw14290; decide +kernel
      have hl : raw14290step0Labels = raw14290Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14290 raw14290Labels permutation242 permutation7
    mixedMoment B raw14290step0 raw14290step0Labels = mixedMoment B raw14290step1 raw14290step1Labels := by
      have ha : raw14290step1 = -raw14290step0 := by apply Matrix.ext; change ∀ i j, raw14290step1 i j = -(raw14290step0 i j); unfold raw14290step1 raw14290step0; decide +kernel
      have hl : raw14290step1Labels = raw14290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14290step1 raw14290step1Labels = mixedMoment B raw14290step2 raw14290step2Labels := by
      have ha : raw14290step2 = raw14290step1 := by apply Matrix.ext; unfold raw14290step2 raw14290step1; decide +kernel
      have hl : raw14290step1Labels = labelEmbedding1 ∘ raw14290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14290step1 raw14290step1Labels raw14290step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

def raw14291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14291step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14291step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14291 raw14291Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw14291 raw14291Labels = mixedMoment B raw14291step0 raw14291step0Labels := by
      have ha : raw14291step0 = (fun i j => raw14291 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14291step0 raw14291; decide +kernel
      have hl : raw14291step0Labels = raw14291Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14291 raw14291Labels permutation242 permutation7
    mixedMoment B raw14291step0 raw14291step0Labels = mixedMoment B raw14291step1 raw14291step1Labels := by
      have ha : raw14291step1 = -raw14291step0 := by apply Matrix.ext; change ∀ i j, raw14291step1 i j = -(raw14291step0 i j); unfold raw14291step1 raw14291step0; decide +kernel
      have hl : raw14291step1Labels = raw14291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14291step1 raw14291step1Labels = mixedMoment B raw14291step2 raw14291step2Labels := by
      have ha : raw14291step2 = raw14291step1 := by apply Matrix.ext; unfold raw14291step2 raw14291step1; decide +kernel
      have hl : raw14291step1Labels = labelEmbedding1 ∘ raw14291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14291step1 raw14291step1Labels raw14291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

def raw14292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14292step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14292step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14292step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14292 raw14292Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw14292 raw14292Labels = mixedMoment B raw14292step0 raw14292step0Labels := by
      have hz : ∀ j, raw14292 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14292step0 = (fun i j => raw14292 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14292step0 raw14292; decide +kernel
      have hl : raw14292step0Labels = raw14292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14292 raw14292Labels permutation520 hz
    mixedMoment B raw14292step0 raw14292step0Labels = mixedMoment B raw14292step1 raw14292step1Labels := by
      have ha : raw14292step1 = (fun i j => raw14292step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14292step1 raw14292step0; decide +kernel
      have hl : raw14292step1Labels = raw14292step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14292step0 raw14292step0Labels permutation52 permutation7
    mixedMoment B raw14292step1 raw14292step1Labels = mixedMoment B raw14292step2 raw14292step2Labels := by
      have ha : raw14292step2 = -raw14292step1 := by apply Matrix.ext; change ∀ i j, raw14292step2 i j = -(raw14292step1 i j); unfold raw14292step2 raw14292step1; decide +kernel
      have hl : raw14292step2Labels = raw14292step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14292step2 raw14292step2Labels = mixedMoment B raw14292step3 raw14292step3Labels := by
      have ha : raw14292step3 = raw14292step2 := by apply Matrix.ext; unfold raw14292step3 raw14292step2; decide +kernel
      have hl : raw14292step2Labels = labelEmbedding1 ∘ raw14292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14292step2 raw14292step2Labels raw14292step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw14293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14293step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14293step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14293step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14293 raw14293Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw14293 raw14293Labels = mixedMoment B raw14293step0 raw14293step0Labels := by
      have hz : ∀ j, raw14293 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14293step0 = (fun i j => raw14293 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14293step0 raw14293; decide +kernel
      have hl : raw14293step0Labels = raw14293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14293 raw14293Labels permutation590 hz
    mixedMoment B raw14293step0 raw14293step0Labels = mixedMoment B raw14293step1 raw14293step1Labels := by
      have ha : raw14293step1 = (fun i j => raw14293step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14293step1 raw14293step0; decide +kernel
      have hl : raw14293step1Labels = raw14293step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14293step0 raw14293step0Labels permutation52 permutation7
    mixedMoment B raw14293step1 raw14293step1Labels = mixedMoment B raw14293step2 raw14293step2Labels := by
      have ha : raw14293step2 = -raw14293step1 := by apply Matrix.ext; change ∀ i j, raw14293step2 i j = -(raw14293step1 i j); unfold raw14293step2 raw14293step1; decide +kernel
      have hl : raw14293step2Labels = raw14293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14293step2 raw14293step2Labels = mixedMoment B raw14293step3 raw14293step3Labels := by
      have ha : raw14293step3 = raw14293step2 := by apply Matrix.ext; unfold raw14293step3 raw14293step2; decide +kernel
      have hl : raw14293step2Labels = labelEmbedding1 ∘ raw14293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14293step2 raw14293step2Labels raw14293step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw14294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14294step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14294 raw14294Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw14294 raw14294Labels = mixedMoment B raw14294step0 raw14294step0Labels := by
      have ha : raw14294step0 = (fun i j => raw14294 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14294step0 raw14294; decide +kernel
      have hl : raw14294step0Labels = raw14294Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14294 raw14294Labels permutation240 permutation7
    mixedMoment B raw14294step0 raw14294step0Labels = mixedMoment B raw14294step1 raw14294step1Labels := by
      have ha : raw14294step1 = -raw14294step0 := by apply Matrix.ext; change ∀ i j, raw14294step1 i j = -(raw14294step0 i j); unfold raw14294step1 raw14294step0; decide +kernel
      have hl : raw14294step1Labels = raw14294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14294step1 raw14294step1Labels = mixedMoment B raw14294step2 raw14294step2Labels := by
      have ha : raw14294step2 = raw14294step1 := by apply Matrix.ext; unfold raw14294step2 raw14294step1; decide +kernel
      have hl : raw14294step1Labels = labelEmbedding1 ∘ raw14294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14294step1 raw14294step1Labels raw14294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

def raw14295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14295step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14295step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14295 raw14295Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw14295 raw14295Labels = mixedMoment B raw14295step0 raw14295step0Labels := by
      have ha : raw14295step0 = (fun i j => raw14295 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14295step0 raw14295; decide +kernel
      have hl : raw14295step0Labels = raw14295Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14295 raw14295Labels permutation240 permutation7
    mixedMoment B raw14295step0 raw14295step0Labels = mixedMoment B raw14295step1 raw14295step1Labels := by
      have ha : raw14295step1 = -raw14295step0 := by apply Matrix.ext; change ∀ i j, raw14295step1 i j = -(raw14295step0 i j); unfold raw14295step1 raw14295step0; decide +kernel
      have hl : raw14295step1Labels = raw14295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14295step1 raw14295step1Labels = mixedMoment B raw14295step2 raw14295step2Labels := by
      have ha : raw14295step2 = raw14295step1 := by apply Matrix.ext; unfold raw14295step2 raw14295step1; decide +kernel
      have hl : raw14295step1Labels = labelEmbedding1 ∘ raw14295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14295step1 raw14295step1Labels raw14295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

def raw14296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14296step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14296step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14296step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14296step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14296step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14296 raw14296Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw14296 raw14296Labels = mixedMoment B raw14296step0 raw14296step0Labels := by
      have hz : ∀ j, raw14296 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14296step0 = (fun i j => raw14296 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14296step0 raw14296; decide +kernel
      have hl : raw14296step0Labels = raw14296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14296 raw14296Labels permutation520 hz
    mixedMoment B raw14296step0 raw14296step0Labels = mixedMoment B raw14296step1 raw14296step1Labels := by
      have ha : raw14296step1 = (fun i j => raw14296step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14296step1 raw14296step0; decide +kernel
      have hl : raw14296step1Labels = raw14296step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14296step0 raw14296step0Labels permutation50 permutation7
    mixedMoment B raw14296step1 raw14296step1Labels = mixedMoment B raw14296step2 raw14296step2Labels := by
      have ha : raw14296step2 = -raw14296step1 := by apply Matrix.ext; change ∀ i j, raw14296step2 i j = -(raw14296step1 i j); unfold raw14296step2 raw14296step1; decide +kernel
      have hl : raw14296step2Labels = raw14296step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14296step2 raw14296step2Labels = mixedMoment B raw14296step3 raw14296step3Labels := by
      have ha : raw14296step3 = raw14296step2 := by apply Matrix.ext; unfold raw14296step3 raw14296step2; decide +kernel
      have hl : raw14296step2Labels = labelEmbedding1 ∘ raw14296step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14296step2 raw14296step2Labels raw14296step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw14297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14297step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14297step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14297step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14297step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14297 raw14297Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw14297 raw14297Labels = mixedMoment B raw14297step0 raw14297step0Labels := by
      have hz : ∀ j, raw14297 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14297step0 = (fun i j => raw14297 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14297step0 raw14297; decide +kernel
      have hl : raw14297step0Labels = raw14297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14297 raw14297Labels permutation590 hz
    mixedMoment B raw14297step0 raw14297step0Labels = mixedMoment B raw14297step1 raw14297step1Labels := by
      have ha : raw14297step1 = (fun i j => raw14297step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14297step1 raw14297step0; decide +kernel
      have hl : raw14297step1Labels = raw14297step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14297step0 raw14297step0Labels permutation50 permutation7
    mixedMoment B raw14297step1 raw14297step1Labels = mixedMoment B raw14297step2 raw14297step2Labels := by
      have ha : raw14297step2 = -raw14297step1 := by apply Matrix.ext; change ∀ i j, raw14297step2 i j = -(raw14297step1 i j); unfold raw14297step2 raw14297step1; decide +kernel
      have hl : raw14297step2Labels = raw14297step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14297step2 raw14297step2Labels = mixedMoment B raw14297step3 raw14297step3Labels := by
      have ha : raw14297step3 = raw14297step2 := by apply Matrix.ext; unfold raw14297step3 raw14297step2; decide +kernel
      have hl : raw14297step2Labels = labelEmbedding1 ∘ raw14297step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14297step2 raw14297step2Labels raw14297step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw14298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw14298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14298step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14298step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14298 raw14298Labels = mixedMoment B node1705 node1705Labels := by
  calc
    mixedMoment B raw14298 raw14298Labels = mixedMoment B raw14298step0 raw14298step0Labels := by
      have ha : raw14298step0 = (fun i j => raw14298 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14298step0 raw14298; decide +kernel
      have hl : raw14298step0Labels = raw14298Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14298 raw14298Labels permutation240 permutation7
    mixedMoment B raw14298step0 raw14298step0Labels = mixedMoment B raw14298step1 raw14298step1Labels := by
      have ha : raw14298step1 = -raw14298step0 := by apply Matrix.ext; change ∀ i j, raw14298step1 i j = -(raw14298step0 i j); unfold raw14298step1 raw14298step0; decide +kernel
      have hl : raw14298step1Labels = raw14298step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14298step1 raw14298step1Labels = mixedMoment B raw14298step2 raw14298step2Labels := by
      have ha : raw14298step2 = raw14298step1 := by apply Matrix.ext; unfold raw14298step2 raw14298step1; decide +kernel
      have hl : raw14298step1Labels = labelEmbedding1 ∘ raw14298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14298step1 raw14298step1Labels raw14298step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1705 node1705Labels := by rfl

def raw14299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw14299step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14299step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14299step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14299step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14299 raw14299Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw14299 raw14299Labels = mixedMoment B raw14299step0 raw14299step0Labels := by
      have ha : raw14299step0 = (fun i j => raw14299 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14299step0 raw14299; decide +kernel
      have hl : raw14299step0Labels = raw14299Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14299 raw14299Labels permutation240 permutation7
    mixedMoment B raw14299step0 raw14299step0Labels = mixedMoment B raw14299step1 raw14299step1Labels := by
      have ha : raw14299step1 = -raw14299step0 := by apply Matrix.ext; change ∀ i j, raw14299step1 i j = -(raw14299step0 i j); unfold raw14299step1 raw14299step0; decide +kernel
      have hl : raw14299step1Labels = raw14299step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14299step1 raw14299step1Labels = mixedMoment B raw14299step2 raw14299step2Labels := by
      have ha : raw14299step2 = raw14299step1 := by apply Matrix.ext; unfold raw14299step2 raw14299step1; decide +kernel
      have hl : raw14299step1Labels = labelEmbedding1 ∘ raw14299step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14299step1 raw14299step1Labels raw14299step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw14300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw14300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw14300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14300step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14300 raw14300Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw14300 raw14300Labels = mixedMoment B raw14300step0 raw14300step0Labels := by
      have ha : raw14300step0 = (fun i j => raw14300 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14300step0 raw14300; decide +kernel
      have hl : raw14300step0Labels = raw14300Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14300 raw14300Labels permutation242 permutation7
    mixedMoment B raw14300step0 raw14300step0Labels = mixedMoment B raw14300step1 raw14300step1Labels := by
      have ha : raw14300step1 = -raw14300step0 := by apply Matrix.ext; change ∀ i j, raw14300step1 i j = -(raw14300step0 i j); unfold raw14300step1 raw14300step0; decide +kernel
      have hl : raw14300step1Labels = raw14300step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14300step1 raw14300step1Labels = mixedMoment B raw14300step2 raw14300step2Labels := by
      have ha : raw14300step2 = raw14300step1 := by apply Matrix.ext; unfold raw14300step2 raw14300step1; decide +kernel
      have hl : raw14300step1Labels = labelEmbedding1 ∘ raw14300step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14300step1 raw14300step1Labels raw14300step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw14301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw14301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14301step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw14301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14301step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14301step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14301step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14301 raw14301Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw14301 raw14301Labels = mixedMoment B raw14301step0 raw14301step0Labels := by
      have hz : ∀ j, raw14301 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14301step0 = (fun i j => raw14301 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14301step0 raw14301; decide +kernel
      have hl : raw14301step0Labels = raw14301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14301 raw14301Labels permutation520 hz
    mixedMoment B raw14301step0 raw14301step0Labels = mixedMoment B raw14301step1 raw14301step1Labels := by
      have ha : raw14301step1 = (fun i j => raw14301step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14301step1 raw14301step0; decide +kernel
      have hl : raw14301step1Labels = raw14301step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14301step0 raw14301step0Labels permutation50 permutation7
    mixedMoment B raw14301step1 raw14301step1Labels = mixedMoment B raw14301step2 raw14301step2Labels := by
      have ha : raw14301step2 = -raw14301step1 := by apply Matrix.ext; change ∀ i j, raw14301step2 i j = -(raw14301step1 i j); unfold raw14301step2 raw14301step1; decide +kernel
      have hl : raw14301step2Labels = raw14301step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14301step2 raw14301step2Labels = mixedMoment B raw14301step3 raw14301step3Labels := by
      have ha : raw14301step3 = raw14301step2 := by apply Matrix.ext; unfold raw14301step3 raw14301step2; decide +kernel
      have hl : raw14301step2Labels = labelEmbedding1 ∘ raw14301step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14301step2 raw14301step2Labels raw14301step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw14302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw14302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw14302step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14302step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14302 raw14302Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw14302 raw14302Labels = mixedMoment B raw14302step0 raw14302step0Labels := by
      have hz : ∀ j, raw14302 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14302step0 = (fun i j => raw14302 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14302step0 raw14302; decide +kernel
      have hl : raw14302step0Labels = raw14302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14302 raw14302Labels permutation590 hz
    mixedMoment B raw14302step0 raw14302step0Labels = mixedMoment B raw14302step1 raw14302step1Labels := by
      have ha : raw14302step1 = (fun i j => raw14302step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14302step1 raw14302step0; decide +kernel
      have hl : raw14302step1Labels = raw14302step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14302step0 raw14302step0Labels permutation50 permutation7
    mixedMoment B raw14302step1 raw14302step1Labels = mixedMoment B raw14302step2 raw14302step2Labels := by
      have ha : raw14302step2 = -raw14302step1 := by apply Matrix.ext; change ∀ i j, raw14302step2 i j = -(raw14302step1 i j); unfold raw14302step2 raw14302step1; decide +kernel
      have hl : raw14302step2Labels = raw14302step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14302step2 raw14302step2Labels = mixedMoment B raw14302step3 raw14302step3Labels := by
      have ha : raw14302step3 = raw14302step2 := by apply Matrix.ext; unfold raw14302step3 raw14302step2; decide +kernel
      have hl : raw14302step2Labels = labelEmbedding1 ∘ raw14302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14302step2 raw14302step2Labels raw14302step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw14303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw14303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14303step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14303step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14303step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14303 raw14303Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw14303 raw14303Labels = mixedMoment B raw14303step0 raw14303step0Labels := by
      have ha : raw14303step0 = (fun i j => raw14303 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14303step0 raw14303; decide +kernel
      have hl : raw14303step0Labels = raw14303Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14303 raw14303Labels permutation260 permutation7
    mixedMoment B raw14303step0 raw14303step0Labels = mixedMoment B raw14303step1 raw14303step1Labels := by
      have ha : raw14303step1 = -raw14303step0 := by apply Matrix.ext; change ∀ i j, raw14303step1 i j = -(raw14303step0 i j); unfold raw14303step1 raw14303step0; decide +kernel
      have hl : raw14303step1Labels = raw14303step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14303step1 raw14303step1Labels = mixedMoment B raw14303step2 raw14303step2Labels := by
      have ha : raw14303step2 = raw14303step1 := by apply Matrix.ext; unfold raw14303step2 raw14303step1; decide +kernel
      have hl : raw14303step1Labels = labelEmbedding1 ∘ raw14303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14303step1 raw14303step1Labels raw14303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw14304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw14304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14304step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14304 raw14304Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw14304 raw14304Labels = mixedMoment B raw14304step0 raw14304step0Labels := by
      have ha : raw14304step0 = (fun i j => raw14304 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14304step0 raw14304; decide +kernel
      have hl : raw14304step0Labels = raw14304Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14304 raw14304Labels permutation260 permutation7
    mixedMoment B raw14304step0 raw14304step0Labels = mixedMoment B raw14304step1 raw14304step1Labels := by
      have ha : raw14304step1 = -raw14304step0 := by apply Matrix.ext; change ∀ i j, raw14304step1 i j = -(raw14304step0 i j); unfold raw14304step1 raw14304step0; decide +kernel
      have hl : raw14304step1Labels = raw14304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14304step1 raw14304step1Labels = mixedMoment B raw14304step2 raw14304step2Labels := by
      have ha : raw14304step2 = raw14304step1 := by apply Matrix.ext; unfold raw14304step2 raw14304step1; decide +kernel
      have hl : raw14304step1Labels = labelEmbedding1 ∘ raw14304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14304step1 raw14304step1Labels raw14304step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw14305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw14305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14305step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14305step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14305step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14305 raw14305Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw14305 raw14305Labels = mixedMoment B raw14305step0 raw14305step0Labels := by
      have ha : raw14305step0 = (fun i j => raw14305 (permutation262 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14305step0 raw14305; decide +kernel
      have hl : raw14305step0Labels = raw14305Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14305 raw14305Labels permutation262 permutation7
    mixedMoment B raw14305step0 raw14305step0Labels = mixedMoment B raw14305step1 raw14305step1Labels := by
      have ha : raw14305step1 = -raw14305step0 := by apply Matrix.ext; change ∀ i j, raw14305step1 i j = -(raw14305step0 i j); unfold raw14305step1 raw14305step0; decide +kernel
      have hl : raw14305step1Labels = raw14305step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14305step1 raw14305step1Labels = mixedMoment B raw14305step2 raw14305step2Labels := by
      have ha : raw14305step2 = raw14305step1 := by apply Matrix.ext; unfold raw14305step2 raw14305step1; decide +kernel
      have hl : raw14305step1Labels = labelEmbedding1 ∘ raw14305step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14305step1 raw14305step1Labels raw14305step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw14306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw14306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14306step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14306step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14306step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14306step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14306 raw14306Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw14306 raw14306Labels = mixedMoment B raw14306step0 raw14306step0Labels := by
      have hz : ∀ j, raw14306 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14306step0 = (fun i j => raw14306 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14306step0 raw14306; decide +kernel
      have hl : raw14306step0Labels = raw14306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14306 raw14306Labels permutation590 hz
    mixedMoment B raw14306step0 raw14306step0Labels = mixedMoment B raw14306step1 raw14306step1Labels := by
      have ha : raw14306step1 = (fun i j => raw14306step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14306step1 raw14306step0; decide +kernel
      have hl : raw14306step1Labels = raw14306step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14306step0 raw14306step0Labels permutation50 permutation7
    mixedMoment B raw14306step1 raw14306step1Labels = mixedMoment B raw14306step2 raw14306step2Labels := by
      have ha : raw14306step2 = -raw14306step1 := by apply Matrix.ext; change ∀ i j, raw14306step2 i j = -(raw14306step1 i j); unfold raw14306step2 raw14306step1; decide +kernel
      have hl : raw14306step2Labels = raw14306step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14306step2 raw14306step2Labels = mixedMoment B raw14306step3 raw14306step3Labels := by
      have ha : raw14306step3 = raw14306step2 := by apply Matrix.ext; unfold raw14306step3 raw14306step2; decide +kernel
      have hl : raw14306step2Labels = labelEmbedding1 ∘ raw14306step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14306step2 raw14306step2Labels raw14306step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw14307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw14307step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14307step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14307step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14307step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14307 raw14307Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw14307 raw14307Labels = mixedMoment B raw14307step0 raw14307step0Labels := by
      have ha : raw14307step0 = (fun i j => raw14307 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14307step0 raw14307; decide +kernel
      have hl : raw14307step0Labels = raw14307Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14307 raw14307Labels permutation240 permutation7
    mixedMoment B raw14307step0 raw14307step0Labels = mixedMoment B raw14307step1 raw14307step1Labels := by
      have ha : raw14307step1 = -raw14307step0 := by apply Matrix.ext; change ∀ i j, raw14307step1 i j = -(raw14307step0 i j); unfold raw14307step1 raw14307step0; decide +kernel
      have hl : raw14307step1Labels = raw14307step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14307step1 raw14307step1Labels = mixedMoment B raw14307step2 raw14307step2Labels := by
      have ha : raw14307step2 = raw14307step1 := by apply Matrix.ext; unfold raw14307step2 raw14307step1; decide +kernel
      have hl : raw14307step1Labels = labelEmbedding1 ∘ raw14307step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14307step1 raw14307step1Labels raw14307step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2252 node2252Labels := by rfl

def raw14308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14308step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14308 raw14308Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw14308 raw14308Labels = mixedMoment B raw14308step0 raw14308step0Labels := by
      have ha : raw14308step0 = (fun i j => raw14308 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14308step0 raw14308; decide +kernel
      have hl : raw14308step0Labels = raw14308Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14308 raw14308Labels permutation155 permutation3
    mixedMoment B raw14308step0 raw14308step0Labels = mixedMoment B raw14308step1 raw14308step1Labels := by
      have ha : raw14308step1 = raw14308step0 := by apply Matrix.ext; unfold raw14308step1 raw14308step0; decide +kernel
      have hl : raw14308step0Labels = labelEmbedding6 ∘ raw14308step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14308step0 raw14308step0Labels raw14308step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw14309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14309step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14309step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14309 raw14309Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw14309 raw14309Labels = mixedMoment B raw14309step0 raw14309step0Labels := by
      have ha : raw14309step0 = (fun i j => raw14309 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14309step0 raw14309; decide +kernel
      have hl : raw14309step0Labels = raw14309Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14309 raw14309Labels permutation179 permutation3
    mixedMoment B raw14309step0 raw14309step0Labels = mixedMoment B raw14309step1 raw14309step1Labels := by
      have ha : raw14309step1 = raw14309step0 := by apply Matrix.ext; unfold raw14309step1 raw14309step0; decide +kernel
      have hl : raw14309step0Labels = labelEmbedding6 ∘ raw14309step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14309step0 raw14309step0Labels raw14309step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw14310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw14310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14310step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14310step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14310step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14310step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14310 raw14310Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw14310 raw14310Labels = mixedMoment B raw14310step0 raw14310step0Labels := by
      have ha : raw14310step0 = (fun i j => raw14310 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14310step0 raw14310; decide +kernel
      have hl : raw14310step0Labels = raw14310Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14310 raw14310Labels permutation240 permutation5
    mixedMoment B raw14310step0 raw14310step0Labels = mixedMoment B raw14310step1 raw14310step1Labels := by
      have ha : raw14310step1 = -raw14310step0 := by apply Matrix.ext; change ∀ i j, raw14310step1 i j = -(raw14310step0 i j); unfold raw14310step1 raw14310step0; decide +kernel
      have hl : raw14310step1Labels = raw14310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14310step1 raw14310step1Labels = mixedMoment B raw14310step2 raw14310step2Labels := by
      have ha : raw14310step2 = raw14310step1 := by apply Matrix.ext; unfold raw14310step2 raw14310step1; decide +kernel
      have hl : raw14310step1Labels = labelEmbedding8 ∘ raw14310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14310step1 raw14310step1Labels raw14310step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw14311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw14311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14311step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14311step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14311step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14311step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14311 raw14311Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw14311 raw14311Labels = mixedMoment B raw14311step0 raw14311step0Labels := by
      have ha : raw14311step0 = (fun i j => raw14311 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14311step0 raw14311; decide +kernel
      have hl : raw14311step0Labels = raw14311Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14311 raw14311Labels permutation260 permutation5
    mixedMoment B raw14311step0 raw14311step0Labels = mixedMoment B raw14311step1 raw14311step1Labels := by
      have ha : raw14311step1 = -raw14311step0 := by apply Matrix.ext; change ∀ i j, raw14311step1 i j = -(raw14311step0 i j); unfold raw14311step1 raw14311step0; decide +kernel
      have hl : raw14311step1Labels = raw14311step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14311step1 raw14311step1Labels = mixedMoment B raw14311step2 raw14311step2Labels := by
      have ha : raw14311step2 = raw14311step1 := by apply Matrix.ext; unfold raw14311step2 raw14311step1; decide +kernel
      have hl : raw14311step1Labels = labelEmbedding8 ∘ raw14311step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14311step1 raw14311step1Labels raw14311step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw14312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14312step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14312step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14312step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14312step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14312 raw14312Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw14312 raw14312Labels = mixedMoment B raw14312step0 raw14312step0Labels := by
      have ha : raw14312step0 = (fun i j => raw14312 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14312step0 raw14312; decide +kernel
      have hl : raw14312step0Labels = raw14312Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14312 raw14312Labels permutation243 permutation5
    mixedMoment B raw14312step0 raw14312step0Labels = mixedMoment B raw14312step1 raw14312step1Labels := by
      have ha : raw14312step1 = -raw14312step0 := by apply Matrix.ext; change ∀ i j, raw14312step1 i j = -(raw14312step0 i j); unfold raw14312step1 raw14312step0; decide +kernel
      have hl : raw14312step1Labels = raw14312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14312step1 raw14312step1Labels = mixedMoment B raw14312step2 raw14312step2Labels := by
      have ha : raw14312step2 = raw14312step1 := by apply Matrix.ext; unfold raw14312step2 raw14312step1; decide +kernel
      have hl : raw14312step1Labels = labelEmbedding8 ∘ raw14312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14312step1 raw14312step1Labels raw14312step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw14313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14313step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14313step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14313 raw14313Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw14313 raw14313Labels = mixedMoment B raw14313step0 raw14313step0Labels := by
      have ha : raw14313step0 = (fun i j => raw14313 (permutation193 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14313step0 raw14313; decide +kernel
      have hl : raw14313step0Labels = raw14313Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14313 raw14313Labels permutation193 permutation3
    mixedMoment B raw14313step0 raw14313step0Labels = mixedMoment B raw14313step1 raw14313step1Labels := by
      have ha : raw14313step1 = raw14313step0 := by apply Matrix.ext; unfold raw14313step1 raw14313step0; decide +kernel
      have hl : raw14313step0Labels = labelEmbedding6 ∘ raw14313step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14313step0 raw14313step0Labels raw14313step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw14314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw14314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14314step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14314step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14314step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14314step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14314 raw14314Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14314 raw14314Labels = mixedMoment B raw14314step0 raw14314step0Labels := by
      have ha : raw14314step0 = (fun i j => raw14314 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14314step0 raw14314; decide +kernel
      have hl : raw14314step0Labels = raw14314Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14314 raw14314Labels permutation243 permutation5
    mixedMoment B raw14314step0 raw14314step0Labels = mixedMoment B raw14314step1 raw14314step1Labels := by
      have ha : raw14314step1 = -raw14314step0 := by apply Matrix.ext; change ∀ i j, raw14314step1 i j = -(raw14314step0 i j); unfold raw14314step1 raw14314step0; decide +kernel
      have hl : raw14314step1Labels = raw14314step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14314step1 raw14314step1Labels = mixedMoment B raw14314step2 raw14314step2Labels := by
      have ha : raw14314step2 = raw14314step1 := by apply Matrix.ext; unfold raw14314step2 raw14314step1; decide +kernel
      have hl : raw14314step1Labels = labelEmbedding8 ∘ raw14314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14314step1 raw14314step1Labels raw14314step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw14315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw14315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14315step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14315step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14315step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14315step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14315 raw14315Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14315 raw14315Labels = mixedMoment B raw14315step0 raw14315step0Labels := by
      have ha : raw14315step0 = (fun i j => raw14315 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14315step0 raw14315; decide +kernel
      have hl : raw14315step0Labels = raw14315Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14315 raw14315Labels permutation263 permutation5
    mixedMoment B raw14315step0 raw14315step0Labels = mixedMoment B raw14315step1 raw14315step1Labels := by
      have ha : raw14315step1 = -raw14315step0 := by apply Matrix.ext; change ∀ i j, raw14315step1 i j = -(raw14315step0 i j); unfold raw14315step1 raw14315step0; decide +kernel
      have hl : raw14315step1Labels = raw14315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14315step1 raw14315step1Labels = mixedMoment B raw14315step2 raw14315step2Labels := by
      have ha : raw14315step2 = raw14315step1 := by apply Matrix.ext; unfold raw14315step2 raw14315step1; decide +kernel
      have hl : raw14315step1Labels = labelEmbedding8 ∘ raw14315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14315step1 raw14315step1Labels raw14315step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw14316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14316step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14316step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14316step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14316step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14316 raw14316Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw14316 raw14316Labels = mixedMoment B raw14316step0 raw14316step0Labels := by
      have ha : raw14316step0 = (fun i j => raw14316 (permutation241 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14316step0 raw14316; decide +kernel
      have hl : raw14316step0Labels = raw14316Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14316 raw14316Labels permutation241 permutation5
    mixedMoment B raw14316step0 raw14316step0Labels = mixedMoment B raw14316step1 raw14316step1Labels := by
      have ha : raw14316step1 = -raw14316step0 := by apply Matrix.ext; change ∀ i j, raw14316step1 i j = -(raw14316step0 i j); unfold raw14316step1 raw14316step0; decide +kernel
      have hl : raw14316step1Labels = raw14316step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14316step1 raw14316step1Labels = mixedMoment B raw14316step2 raw14316step2Labels := by
      have ha : raw14316step2 = raw14316step1 := by apply Matrix.ext; unfold raw14316step2 raw14316step1; decide +kernel
      have hl : raw14316step1Labels = labelEmbedding8 ∘ raw14316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14316step1 raw14316step1Labels raw14316step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw14317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14317step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14317 raw14317Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw14317 raw14317Labels = mixedMoment B raw14317step0 raw14317step0Labels := by
      have ha : raw14317step0 = (fun i j => raw14317 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14317step0 raw14317; decide +kernel
      have hl : raw14317step0Labels = raw14317Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14317 raw14317Labels permutation169 permutation3
    mixedMoment B raw14317step0 raw14317step0Labels = mixedMoment B raw14317step1 raw14317step1Labels := by
      have ha : raw14317step1 = raw14317step0 := by apply Matrix.ext; unfold raw14317step1 raw14317step0; decide +kernel
      have hl : raw14317step0Labels = labelEmbedding6 ∘ raw14317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14317step0 raw14317step0Labels raw14317step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw14318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw14318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14318step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14318step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14318step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14318step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14318 raw14318Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14318 raw14318Labels = mixedMoment B raw14318step0 raw14318step0Labels := by
      have ha : raw14318step0 = (fun i j => raw14318 (permutation241 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14318step0 raw14318; decide +kernel
      have hl : raw14318step0Labels = raw14318Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14318 raw14318Labels permutation241 permutation5
    mixedMoment B raw14318step0 raw14318step0Labels = mixedMoment B raw14318step1 raw14318step1Labels := by
      have ha : raw14318step1 = -raw14318step0 := by apply Matrix.ext; change ∀ i j, raw14318step1 i j = -(raw14318step0 i j); unfold raw14318step1 raw14318step0; decide +kernel
      have hl : raw14318step1Labels = raw14318step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14318step1 raw14318step1Labels = mixedMoment B raw14318step2 raw14318step2Labels := by
      have ha : raw14318step2 = raw14318step1 := by apply Matrix.ext; unfold raw14318step2 raw14318step1; decide +kernel
      have hl : raw14318step1Labels = labelEmbedding8 ∘ raw14318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14318step1 raw14318step1Labels raw14318step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw14319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw14319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14319step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14319step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14319step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14319step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14319 raw14319Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14319 raw14319Labels = mixedMoment B raw14319step0 raw14319step0Labels := by
      have ha : raw14319step0 = (fun i j => raw14319 (permutation261 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14319step0 raw14319; decide +kernel
      have hl : raw14319step0Labels = raw14319Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14319 raw14319Labels permutation261 permutation5
    mixedMoment B raw14319step0 raw14319step0Labels = mixedMoment B raw14319step1 raw14319step1Labels := by
      have ha : raw14319step1 = -raw14319step0 := by apply Matrix.ext; change ∀ i j, raw14319step1 i j = -(raw14319step0 i j); unfold raw14319step1 raw14319step0; decide +kernel
      have hl : raw14319step1Labels = raw14319step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14319step1 raw14319step1Labels = mixedMoment B raw14319step2 raw14319step2Labels := by
      have ha : raw14319step2 = raw14319step1 := by apply Matrix.ext; unfold raw14319step2 raw14319step1; decide +kernel
      have hl : raw14319step1Labels = labelEmbedding8 ∘ raw14319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14319step1 raw14319step1Labels raw14319step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw14320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14320step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14320 raw14320Labels = mixedMoment B node4248 node4248Labels := by
  calc
    mixedMoment B raw14320 raw14320Labels = mixedMoment B raw14320step0 raw14320step0Labels := by
      have ha : raw14320step0 = (fun i j => raw14320 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14320step0 raw14320; decide +kernel
      have hl : raw14320step0Labels = raw14320Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14320 raw14320Labels permutation155 permutation3
    mixedMoment B raw14320step0 raw14320step0Labels = mixedMoment B raw14320step1 raw14320step1Labels := by
      have ha : raw14320step1 = raw14320step0 := by apply Matrix.ext; unfold raw14320step1 raw14320step0; decide +kernel
      have hl : raw14320step0Labels = labelEmbedding6 ∘ raw14320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14320step0 raw14320step0Labels raw14320step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4248 node4248Labels := by rfl

def raw14321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14321step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14321step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14321 raw14321Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw14321 raw14321Labels = mixedMoment B raw14321step0 raw14321step0Labels := by
      have ha : raw14321step0 = (fun i j => raw14321 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14321step0 raw14321; decide +kernel
      have hl : raw14321step0Labels = raw14321Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14321 raw14321Labels permutation155 permutation3
    mixedMoment B raw14321step0 raw14321step0Labels = mixedMoment B raw14321step1 raw14321step1Labels := by
      have ha : raw14321step1 = raw14321step0 := by apply Matrix.ext; unfold raw14321step1 raw14321step0; decide +kernel
      have hl : raw14321step0Labels = labelEmbedding6 ∘ raw14321step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14321step0 raw14321step0Labels raw14321step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw14322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14322step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14322 raw14322Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw14322 raw14322Labels = mixedMoment B raw14322step0 raw14322step0Labels := by
      have ha : raw14322step0 = (fun i j => raw14322 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14322step0 raw14322; decide +kernel
      have hl : raw14322step0Labels = raw14322Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14322 raw14322Labels permutation179 permutation3
    mixedMoment B raw14322step0 raw14322step0Labels = mixedMoment B raw14322step1 raw14322step1Labels := by
      have ha : raw14322step1 = raw14322step0 := by apply Matrix.ext; unfold raw14322step1 raw14322step0; decide +kernel
      have hl : raw14322step0Labels = labelEmbedding6 ∘ raw14322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14322step0 raw14322step0Labels raw14322step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw14323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw14323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw14323step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14323step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14323step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14323 raw14323Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw14323 raw14323Labels = mixedMoment B raw14323step0 raw14323step0Labels := by
      have ha : raw14323step0 = (fun i j => raw14323 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14323step0 raw14323; decide +kernel
      have hl : raw14323step0Labels = raw14323Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14323 raw14323Labels permutation240 permutation5
    mixedMoment B raw14323step0 raw14323step0Labels = mixedMoment B raw14323step1 raw14323step1Labels := by
      have ha : raw14323step1 = -raw14323step0 := by apply Matrix.ext; change ∀ i j, raw14323step1 i j = -(raw14323step0 i j); unfold raw14323step1 raw14323step0; decide +kernel
      have hl : raw14323step1Labels = raw14323step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14323step1 raw14323step1Labels = mixedMoment B raw14323step2 raw14323step2Labels := by
      have ha : raw14323step2 = raw14323step1 := by apply Matrix.ext; unfold raw14323step2 raw14323step1; decide +kernel
      have hl : raw14323step1Labels = labelEmbedding8 ∘ raw14323step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14323step1 raw14323step1Labels raw14323step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw14324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw14324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw14324step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14324step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14324step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14324step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14324 raw14324Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw14324 raw14324Labels = mixedMoment B raw14324step0 raw14324step0Labels := by
      have ha : raw14324step0 = (fun i j => raw14324 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14324step0 raw14324; decide +kernel
      have hl : raw14324step0Labels = raw14324Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14324 raw14324Labels permutation260 permutation5
    mixedMoment B raw14324step0 raw14324step0Labels = mixedMoment B raw14324step1 raw14324step1Labels := by
      have ha : raw14324step1 = -raw14324step0 := by apply Matrix.ext; change ∀ i j, raw14324step1 i j = -(raw14324step0 i j); unfold raw14324step1 raw14324step0; decide +kernel
      have hl : raw14324step1Labels = raw14324step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14324step1 raw14324step1Labels = mixedMoment B raw14324step2 raw14324step2Labels := by
      have ha : raw14324step2 = raw14324step1 := by apply Matrix.ext; unfold raw14324step2 raw14324step1; decide +kernel
      have hl : raw14324step1Labels = labelEmbedding8 ∘ raw14324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14324step1 raw14324step1Labels raw14324step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw14325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw14325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14325step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14325 raw14325Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw14325 raw14325Labels = mixedMoment B raw14325step0 raw14325step0Labels := by
      have ha : raw14325step0 = (fun i j => raw14325 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14325step0 raw14325; decide +kernel
      have hl : raw14325step0Labels = raw14325Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14325 raw14325Labels permutation156 permutation3
    mixedMoment B raw14325step0 raw14325step0Labels = mixedMoment B raw14325step1 raw14325step1Labels := by
      have ha : raw14325step1 = raw14325step0 := by apply Matrix.ext; unfold raw14325step1 raw14325step0; decide +kernel
      have hl : raw14325step0Labels = labelEmbedding6 ∘ raw14325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14325step0 raw14325step0Labels raw14325step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw14326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw14326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14326step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14326step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14326 raw14326Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14326 raw14326Labels = mixedMoment B raw14326step0 raw14326step0Labels := by
      have ha : raw14326step0 = (fun i j => raw14326 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14326step0 raw14326; decide +kernel
      have hl : raw14326step0Labels = raw14326Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14326 raw14326Labels permutation156 permutation3
    mixedMoment B raw14326step0 raw14326step0Labels = mixedMoment B raw14326step1 raw14326step1Labels := by
      have ha : raw14326step1 = raw14326step0 := by apply Matrix.ext; unfold raw14326step1 raw14326step0; decide +kernel
      have hl : raw14326step0Labels = labelEmbedding6 ∘ raw14326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14326step0 raw14326step0Labels raw14326step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw14327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw14327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14327step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14327 raw14327Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14327 raw14327Labels = mixedMoment B raw14327step0 raw14327step0Labels := by
      have ha : raw14327step0 = (fun i j => raw14327 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14327step0 raw14327; decide +kernel
      have hl : raw14327step0Labels = raw14327Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14327 raw14327Labels permutation180 permutation3
    mixedMoment B raw14327step0 raw14327step0Labels = mixedMoment B raw14327step1 raw14327step1Labels := by
      have ha : raw14327step1 = raw14327step0 := by apply Matrix.ext; unfold raw14327step1 raw14327step0; decide +kernel
      have hl : raw14327step0Labels = labelEmbedding6 ∘ raw14327step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14327step0 raw14327step0Labels raw14327step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw14328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw14328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw14328step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14328step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14328step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14328step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14328 raw14328Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw14328 raw14328Labels = mixedMoment B raw14328step0 raw14328step0Labels := by
      have ha : raw14328step0 = (fun i j => raw14328 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14328step0 raw14328; decide +kernel
      have hl : raw14328step0Labels = raw14328Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14328 raw14328Labels permutation246 permutation5
    mixedMoment B raw14328step0 raw14328step0Labels = mixedMoment B raw14328step1 raw14328step1Labels := by
      have ha : raw14328step1 = -raw14328step0 := by apply Matrix.ext; change ∀ i j, raw14328step1 i j = -(raw14328step0 i j); unfold raw14328step1 raw14328step0; decide +kernel
      have hl : raw14328step1Labels = raw14328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14328step1 raw14328step1Labels = mixedMoment B raw14328step2 raw14328step2Labels := by
      have ha : raw14328step2 = raw14328step1 := by apply Matrix.ext; unfold raw14328step2 raw14328step1; decide +kernel
      have hl : raw14328step1Labels = labelEmbedding8 ∘ raw14328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14328step1 raw14328step1Labels raw14328step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw14329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14329step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14329step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14329 raw14329Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw14329 raw14329Labels = mixedMoment B raw14329step0 raw14329step0Labels := by
      have hz : ∀ j, raw14329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14329step0 = (fun i j => raw14329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14329step0 raw14329; decide +kernel
      have hl : raw14329step0Labels = raw14329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14329 raw14329Labels permutation434 hz
    mixedMoment B raw14329step0 raw14329step0Labels = mixedMoment B raw14329step1 raw14329step1Labels := by
      have ha : raw14329step1 = (fun i j => raw14329step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14329step1 raw14329step0; decide +kernel
      have hl : raw14329step1Labels = raw14329step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14329step0 raw14329step0Labels permutation32 permutation3
    mixedMoment B raw14329step1 raw14329step1Labels = mixedMoment B raw14329step2 raw14329step2Labels := by
      have ha : raw14329step2 = raw14329step1 := by apply Matrix.ext; unfold raw14329step2 raw14329step1; decide +kernel
      have hl : raw14329step1Labels = labelEmbedding6 ∘ raw14329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14329step1 raw14329step1Labels raw14329step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw14330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14330step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14330step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14330step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14330step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14330 raw14330Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw14330 raw14330Labels = mixedMoment B raw14330step0 raw14330step0Labels := by
      have hz : ∀ j, raw14330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14330step0 = (fun i j => raw14330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14330step0 raw14330; decide +kernel
      have hl : raw14330step0Labels = raw14330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14330 raw14330Labels permutation346 hz
    mixedMoment B raw14330step0 raw14330step0Labels = mixedMoment B raw14330step1 raw14330step1Labels := by
      have ha : raw14330step1 = (fun i j => raw14330step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14330step1 raw14330step0; decide +kernel
      have hl : raw14330step1Labels = raw14330step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14330step0 raw14330step0Labels permutation50 permutation7
    mixedMoment B raw14330step1 raw14330step1Labels = mixedMoment B raw14330step2 raw14330step2Labels := by
      have ha : raw14330step2 = -raw14330step1 := by apply Matrix.ext; change ∀ i j, raw14330step2 i j = -(raw14330step1 i j); unfold raw14330step2 raw14330step1; decide +kernel
      have hl : raw14330step2Labels = raw14330step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14330step2 raw14330step2Labels = mixedMoment B raw14330step3 raw14330step3Labels := by
      have ha : raw14330step3 = raw14330step2 := by apply Matrix.ext; unfold raw14330step3 raw14330step2; decide +kernel
      have hl : raw14330step2Labels = labelEmbedding10 ∘ raw14330step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14330step2 raw14330step2Labels raw14330step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw14331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14331step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14331step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14331step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14331 raw14331Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw14331 raw14331Labels = mixedMoment B raw14331step0 raw14331step0Labels := by
      have ha : raw14331step0 = (fun i j => raw14331 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14331step0 raw14331; decide +kernel
      have hl : raw14331step0Labels = raw14331Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14331 raw14331Labels permutation194 permutation7
    mixedMoment B raw14331step0 raw14331step0Labels = mixedMoment B raw14331step1 raw14331step1Labels := by
      have ha : raw14331step1 = -raw14331step0 := by apply Matrix.ext; change ∀ i j, raw14331step1 i j = -(raw14331step0 i j); unfold raw14331step1 raw14331step0; decide +kernel
      have hl : raw14331step1Labels = raw14331step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14331step1 raw14331step1Labels = mixedMoment B raw14331step2 raw14331step2Labels := by
      have ha : raw14331step2 = raw14331step1 := by apply Matrix.ext; unfold raw14331step2 raw14331step1; decide +kernel
      have hl : raw14331step1Labels = labelEmbedding10 ∘ raw14331step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14331step1 raw14331step1Labels raw14331step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw14332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14332step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14332step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14332step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14332step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14332 raw14332Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw14332 raw14332Labels = mixedMoment B raw14332step0 raw14332step0Labels := by
      have hz : ∀ j, raw14332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14332step0 = (fun i j => raw14332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14332step0 raw14332; decide +kernel
      have hl : raw14332step0Labels = raw14332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14332 raw14332Labels permutation346 hz
    mixedMoment B raw14332step0 raw14332step0Labels = mixedMoment B raw14332step1 raw14332step1Labels := by
      have ha : raw14332step1 = (fun i j => raw14332step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14332step1 raw14332step0; decide +kernel
      have hl : raw14332step1Labels = raw14332step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14332step0 raw14332step0Labels permutation50 permutation7
    mixedMoment B raw14332step1 raw14332step1Labels = mixedMoment B raw14332step2 raw14332step2Labels := by
      have ha : raw14332step2 = -raw14332step1 := by apply Matrix.ext; change ∀ i j, raw14332step2 i j = -(raw14332step1 i j); unfold raw14332step2 raw14332step1; decide +kernel
      have hl : raw14332step2Labels = raw14332step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14332step2 raw14332step2Labels = mixedMoment B raw14332step3 raw14332step3Labels := by
      have ha : raw14332step3 = raw14332step2 := by apply Matrix.ext; unfold raw14332step3 raw14332step2; decide +kernel
      have hl : raw14332step2Labels = labelEmbedding10 ∘ raw14332step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14332step2 raw14332step2Labels raw14332step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw14333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14333step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14333step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14333step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14333step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14333 raw14333Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw14333 raw14333Labels = mixedMoment B raw14333step0 raw14333step0Labels := by
      have hz : ∀ j, raw14333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14333step0 = (fun i j => raw14333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14333step0 raw14333; decide +kernel
      have hl : raw14333step0Labels = raw14333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14333 raw14333Labels permutation346 hz
    mixedMoment B raw14333step0 raw14333step0Labels = mixedMoment B raw14333step1 raw14333step1Labels := by
      have ha : raw14333step1 = (fun i j => raw14333step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14333step1 raw14333step0; decide +kernel
      have hl : raw14333step1Labels = raw14333step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14333step0 raw14333step0Labels permutation51 permutation7
    mixedMoment B raw14333step1 raw14333step1Labels = mixedMoment B raw14333step2 raw14333step2Labels := by
      have ha : raw14333step2 = -raw14333step1 := by apply Matrix.ext; change ∀ i j, raw14333step2 i j = -(raw14333step1 i j); unfold raw14333step2 raw14333step1; decide +kernel
      have hl : raw14333step2Labels = raw14333step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14333step2 raw14333step2Labels = mixedMoment B raw14333step3 raw14333step3Labels := by
      have ha : raw14333step3 = raw14333step2 := by apply Matrix.ext; unfold raw14333step3 raw14333step2; decide +kernel
      have hl : raw14333step2Labels = labelEmbedding10 ∘ raw14333step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14333step2 raw14333step2Labels raw14333step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw14334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14334step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14334step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14334step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14334step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14334step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14334 raw14334Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw14334 raw14334Labels = mixedMoment B raw14334step0 raw14334step0Labels := by
      have hz : ∀ j, raw14334 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14334step0 = (fun i j => raw14334 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14334step0 raw14334; decide +kernel
      have hl : raw14334step0Labels = raw14334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14334 raw14334Labels permutation590 hz
    mixedMoment B raw14334step0 raw14334step0Labels = mixedMoment B raw14334step1 raw14334step1Labels := by
      have hz : ∀ j, raw14334step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14334step1 = (fun i j => raw14334step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14334step1 raw14334step0; decide +kernel
      have hl : raw14334step1Labels = raw14334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14334step0 raw14334step0Labels permutation80 hz
    mixedMoment B raw14334step1 raw14334step1Labels = mixedMoment B raw14334step2 raw14334step2Labels := by
      have ha : raw14334step2 = (fun i j => raw14334step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14334step2 raw14334step1; decide +kernel
      have hl : raw14334step2Labels = raw14334step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14334step1 raw14334step1Labels permutation8 permutation7
    mixedMoment B raw14334step2 raw14334step2Labels = mixedMoment B raw14334step3 raw14334step3Labels := by
      have ha : raw14334step3 = -raw14334step2 := by apply Matrix.ext; change ∀ i j, raw14334step3 i j = -(raw14334step2 i j); unfold raw14334step3 raw14334step2; decide +kernel
      have hl : raw14334step3Labels = raw14334step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14334step3 raw14334step3Labels = mixedMoment B raw14334step4 raw14334step4Labels := by
      have ha : raw14334step4 = raw14334step3 := by apply Matrix.ext; unfold raw14334step4 raw14334step3; decide +kernel
      have hl : raw14334step3Labels = labelEmbedding10 ∘ raw14334step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14334step3 raw14334step3Labels raw14334step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw14335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14335step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14335 raw14335Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw14335 raw14335Labels = mixedMoment B raw14335step0 raw14335step0Labels := by
      have hz : ∀ j, raw14335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14335step0 = (fun i j => raw14335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14335step0 raw14335; decide +kernel
      have hl : raw14335step0Labels = raw14335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14335 raw14335Labels permutation346 hz
    mixedMoment B raw14335step0 raw14335step0Labels = mixedMoment B raw14335step1 raw14335step1Labels := by
      have ha : raw14335step1 = (fun i j => raw14335step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14335step1 raw14335step0; decide +kernel
      have hl : raw14335step1Labels = raw14335step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14335step0 raw14335step0Labels permutation50 permutation2
    _ = mixedMoment B node4497 node4497Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
