import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2944 raw2944Labels = mixedMoment B node5283 node5283Labels := by
  calc
    mixedMoment B raw2944 raw2944Labels = mixedMoment B raw2944step0 raw2944step0Labels := by
      have ha : raw2944step0 = (fun i j => raw2944 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2944step0 raw2944; decide +kernel
      have hl : raw2944step0Labels = raw2944Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2944 raw2944Labels permutation182 permutation2
    _ = mixedMoment B node5283 node5283Labels := by rfl

def raw2945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2945 raw2945Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw2945 raw2945Labels = mixedMoment B raw2945step0 raw2945step0Labels := by
      have ha : raw2945step0 = (fun i j => raw2945 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2945step0 raw2945; decide +kernel
      have hl : raw2945step0Labels = raw2945Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2945 raw2945Labels permutation182 permutation2
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw2946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2946 raw2946Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw2946 raw2946Labels = mixedMoment B raw2946step0 raw2946step0Labels := by
      have ha : raw2946step0 = (fun i j => raw2946 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2946step0 raw2946; decide +kernel
      have hl : raw2946step0Labels = raw2946Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2946 raw2946Labels permutation206 permutation2
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw2947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2947 raw2947Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw2947 raw2947Labels = mixedMoment B raw2947step0 raw2947step0Labels := by
      have hz : ∀ j, raw2947 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2947step0 = (fun i j => raw2947 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2947step0 raw2947; decide +kernel
      have hl : raw2947step0Labels = raw2947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2947 raw2947Labels permutation520 hz
    mixedMoment B raw2947step0 raw2947step0Labels = mixedMoment B raw2947step1 raw2947step1Labels := by
      have ha : raw2947step1 = (fun i j => raw2947step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2947step1 raw2947step0; decide +kernel
      have hl : raw2947step1Labels = raw2947step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2947step0 raw2947step0Labels permutation40 permutation2
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw2948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2948 raw2948Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw2948 raw2948Labels = mixedMoment B raw2948step0 raw2948step0Labels := by
      have hz : ∀ j, raw2948 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw2948step0 = (fun i j => raw2948 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw2948step0 raw2948; decide +kernel
      have hl : raw2948step0Labels = raw2948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2948 raw2948Labels permutation590 hz
    mixedMoment B raw2948step0 raw2948step0Labels = mixedMoment B raw2948step1 raw2948step1Labels := by
      have ha : raw2948step1 = (fun i j => raw2948step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2948step1 raw2948step0; decide +kernel
      have hl : raw2948step1Labels = raw2948step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2948step0 raw2948step0Labels permutation40 permutation2
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw2949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2949step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2949 raw2949Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw2949 raw2949Labels = mixedMoment B raw2949step0 raw2949step0Labels := by
      have hz : ∀ j, raw2949 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2949step0 = (fun i j => raw2949 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2949step0 raw2949; decide +kernel
      have hl : raw2949step0Labels = raw2949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2949 raw2949Labels permutation265 hz
    mixedMoment B raw2949step0 raw2949step0Labels = mixedMoment B raw2949step1 raw2949step1Labels := by
      have ha : raw2949step1 = (fun i j => raw2949step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2949step1 raw2949step0; decide +kernel
      have hl : raw2949step1Labels = raw2949step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2949step0 raw2949step0Labels permutation41 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw2950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2950 raw2950Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw2950 raw2950Labels = mixedMoment B raw2950step0 raw2950step0Labels := by
      have ha : raw2950step0 = (fun i j => raw2950 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2950step0 raw2950; decide +kernel
      have hl : raw2950step0Labels = raw2950Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2950 raw2950Labels permutation161 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw2951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2951 raw2951Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw2951 raw2951Labels = mixedMoment B raw2951step0 raw2951step0Labels := by
      have hz : ∀ j, raw2951 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2951step0 = (fun i j => raw2951 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2951step0 raw2951; decide +kernel
      have hl : raw2951step0Labels = raw2951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2951 raw2951Labels permutation265 hz
    mixedMoment B raw2951step0 raw2951step0Labels = mixedMoment B raw2951step1 raw2951step1Labels := by
      have ha : raw2951step1 = (fun i j => raw2951step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2951step1 raw2951step0; decide +kernel
      have hl : raw2951step1Labels = raw2951step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2951step0 raw2951step0Labels permutation41 permutation2
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw2952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2952step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2952 raw2952Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw2952 raw2952Labels = mixedMoment B raw2952step0 raw2952step0Labels := by
      have hz : ∀ j, raw2952 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2952step0 = (fun i j => raw2952 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2952step0 raw2952; decide +kernel
      have hl : raw2952step0Labels = raw2952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2952 raw2952Labels permutation520 hz
    mixedMoment B raw2952step0 raw2952step0Labels = mixedMoment B raw2952step1 raw2952step1Labels := by
      have hz : ∀ j, raw2952step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2952step1 = (fun i j => raw2952step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2952step1 raw2952step0; decide +kernel
      have hl : raw2952step1Labels = raw2952step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2952step0 raw2952step0Labels permutation56 hz
    mixedMoment B raw2952step1 raw2952step1Labels = mixedMoment B raw2952step2 raw2952step2Labels := by
      have ha : raw2952step2 = (fun i j => raw2952step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2952step2 raw2952step1; decide +kernel
      have hl : raw2952step2Labels = raw2952step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2952step1 raw2952step1Labels permutation11 permutation2
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw2953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2953step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2953 raw2953Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw2953 raw2953Labels = mixedMoment B raw2953step0 raw2953step0Labels := by
      have hz : ∀ j, raw2953 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw2953step0 = (fun i j => raw2953 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw2953step0 raw2953; decide +kernel
      have hl : raw2953step0Labels = raw2953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2953 raw2953Labels permutation590 hz
    mixedMoment B raw2953step0 raw2953step0Labels = mixedMoment B raw2953step1 raw2953step1Labels := by
      have hz : ∀ j, raw2953step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2953step1 = (fun i j => raw2953step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2953step1 raw2953step0; decide +kernel
      have hl : raw2953step1Labels = raw2953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2953step0 raw2953step0Labels permutation56 hz
    mixedMoment B raw2953step1 raw2953step1Labels = mixedMoment B raw2953step2 raw2953step2Labels := by
      have ha : raw2953step2 = (fun i j => raw2953step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2953step2 raw2953step1; decide +kernel
      have hl : raw2953step2Labels = raw2953step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2953step1 raw2953step1Labels permutation11 permutation2
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw2954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2954step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2954 raw2954Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw2954 raw2954Labels = mixedMoment B raw2954step0 raw2954step0Labels := by
      have hz : ∀ j, raw2954 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2954step0 = (fun i j => raw2954 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2954step0 raw2954; decide +kernel
      have hl : raw2954step0Labels = raw2954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2954 raw2954Labels permutation265 hz
    mixedMoment B raw2954step0 raw2954step0Labels = mixedMoment B raw2954step1 raw2954step1Labels := by
      have ha : raw2954step1 = (fun i j => raw2954step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2954step1 raw2954step0; decide +kernel
      have hl : raw2954step1Labels = raw2954step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2954step0 raw2954step0Labels permutation35 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw2955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2955 raw2955Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw2955 raw2955Labels = mixedMoment B raw2955step0 raw2955step0Labels := by
      have ha : raw2955step0 = (fun i j => raw2955 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2955step0 raw2955; decide +kernel
      have hl : raw2955step0Labels = raw2955Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2955 raw2955Labels permutation155 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw2956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2956 raw2956Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw2956 raw2956Labels = mixedMoment B raw2956step0 raw2956step0Labels := by
      have hz : ∀ j, raw2956 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2956step0 = (fun i j => raw2956 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2956step0 raw2956; decide +kernel
      have hl : raw2956step0Labels = raw2956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2956 raw2956Labels permutation265 hz
    mixedMoment B raw2956step0 raw2956step0Labels = mixedMoment B raw2956step1 raw2956step1Labels := by
      have ha : raw2956step1 = (fun i j => raw2956step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2956step1 raw2956step0; decide +kernel
      have hl : raw2956step1Labels = raw2956step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2956step0 raw2956step0Labels permutation35 permutation2
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw2957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2957 raw2957Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw2957 raw2957Labels = mixedMoment B raw2957step0 raw2957step0Labels := by
      have hz : ∀ j, raw2957 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2957step0 = (fun i j => raw2957 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2957step0 raw2957; decide +kernel
      have hl : raw2957step0Labels = raw2957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2957 raw2957Labels permutation520 hz
    mixedMoment B raw2957step0 raw2957step0Labels = mixedMoment B raw2957step1 raw2957step1Labels := by
      have hz : ∀ j, raw2957step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2957step1 = (fun i j => raw2957step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2957step1 raw2957step0; decide +kernel
      have hl : raw2957step1Labels = raw2957step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2957step0 raw2957step0Labels permutation56 hz
    mixedMoment B raw2957step1 raw2957step1Labels = mixedMoment B raw2957step2 raw2957step2Labels := by
      have ha : raw2957step2 = (fun i j => raw2957step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2957step2 raw2957step1; decide +kernel
      have hl : raw2957step2Labels = raw2957step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2957step1 raw2957step1Labels permutation9 permutation2
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw2958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2958step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2958step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2958 raw2958Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw2958 raw2958Labels = mixedMoment B raw2958step0 raw2958step0Labels := by
      have hz : ∀ j, raw2958 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw2958step0 = (fun i j => raw2958 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw2958step0 raw2958; decide +kernel
      have hl : raw2958step0Labels = raw2958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2958 raw2958Labels permutation590 hz
    mixedMoment B raw2958step0 raw2958step0Labels = mixedMoment B raw2958step1 raw2958step1Labels := by
      have hz : ∀ j, raw2958step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2958step1 = (fun i j => raw2958step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2958step1 raw2958step0; decide +kernel
      have hl : raw2958step1Labels = raw2958step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2958step0 raw2958step0Labels permutation56 hz
    mixedMoment B raw2958step1 raw2958step1Labels = mixedMoment B raw2958step2 raw2958step2Labels := by
      have ha : raw2958step2 = (fun i j => raw2958step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2958step2 raw2958step1; decide +kernel
      have hl : raw2958step2Labels = raw2958step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2958step1 raw2958step1Labels permutation9 permutation2
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw2959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2959step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2959 raw2959Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw2959 raw2959Labels = mixedMoment B raw2959step0 raw2959step0Labels := by
      have hz : ∀ j, raw2959 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2959step0 = (fun i j => raw2959 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2959step0 raw2959; decide +kernel
      have hl : raw2959step0Labels = raw2959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2959 raw2959Labels permutation265 hz
    mixedMoment B raw2959step0 raw2959step0Labels = mixedMoment B raw2959step1 raw2959step1Labels := by
      have ha : raw2959step1 = (fun i j => raw2959step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2959step1 raw2959step0; decide +kernel
      have hl : raw2959step1Labels = raw2959step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2959step0 raw2959step0Labels permutation33 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw2960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2960step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2960step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2960step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2960step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2960 raw2960Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw2960 raw2960Labels = mixedMoment B raw2960step0 raw2960step0Labels := by
      have ha : raw2960step0 = (fun i j => raw2960 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2960step0 raw2960; decide +kernel
      have hl : raw2960step0Labels = raw2960Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2960 raw2960Labels permutation584 permutation3
    mixedMoment B raw2960step0 raw2960step0Labels = mixedMoment B raw2960step1 raw2960step1Labels := by
      have ha : raw2960step1 = -raw2960step0 := by apply Matrix.ext; change ∀ i j, raw2960step1 i j = -(raw2960step0 i j); unfold raw2960step1 raw2960step0; decide +kernel
      have hl : raw2960step1Labels = raw2960step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2960step1 raw2960step1Labels = mixedMoment B raw2960step2 raw2960step2Labels := by
      have ha : raw2960step2 = raw2960step1 := by apply Matrix.ext; unfold raw2960step2 raw2960step1; decide +kernel
      have hl : raw2960step1Labels = labelEmbedding6 ∘ raw2960step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2960step1 raw2960step1Labels raw2960step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw2961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2961step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2961step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2961step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2961step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2961 raw2961Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2961 raw2961Labels = mixedMoment B raw2961step0 raw2961step0Labels := by
      have hz : ∀ j, raw2961 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2961step0 = (fun i j => raw2961 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2961step0 raw2961; decide +kernel
      have hl : raw2961step0Labels = raw2961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2961 raw2961Labels permutation265 hz
    mixedMoment B raw2961step0 raw2961step0Labels = mixedMoment B raw2961step1 raw2961step1Labels := by
      have ha : raw2961step1 = (fun i j => raw2961step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2961step1 raw2961step0; decide +kernel
      have hl : raw2961step1Labels = raw2961step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2961step0 raw2961step0Labels permutation127 permutation3
    mixedMoment B raw2961step1 raw2961step1Labels = mixedMoment B raw2961step2 raw2961step2Labels := by
      have ha : raw2961step2 = -raw2961step1 := by apply Matrix.ext; change ∀ i j, raw2961step2 i j = -(raw2961step1 i j); unfold raw2961step2 raw2961step1; decide +kernel
      have hl : raw2961step2Labels = raw2961step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2961step2 raw2961step2Labels = mixedMoment B raw2961step3 raw2961step3Labels := by
      have ha : raw2961step3 = raw2961step2 := by apply Matrix.ext; unfold raw2961step3 raw2961step2; decide +kernel
      have hl : raw2961step2Labels = labelEmbedding6 ∘ raw2961step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2961step2 raw2961step2Labels raw2961step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw2962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2962step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2962step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2962step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2962 raw2962Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2962 raw2962Labels = mixedMoment B raw2962step0 raw2962step0Labels := by
      have hz : ∀ j, raw2962 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2962step0 = (fun i j => raw2962 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2962step0 raw2962; decide +kernel
      have hl : raw2962step0Labels = raw2962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2962 raw2962Labels permutation265 hz
    mixedMoment B raw2962step0 raw2962step0Labels = mixedMoment B raw2962step1 raw2962step1Labels := by
      have ha : raw2962step1 = (fun i j => raw2962step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2962step1 raw2962step0; decide +kernel
      have hl : raw2962step1Labels = raw2962step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2962step0 raw2962step0Labels permutation125 permutation3
    mixedMoment B raw2962step1 raw2962step1Labels = mixedMoment B raw2962step2 raw2962step2Labels := by
      have ha : raw2962step2 = -raw2962step1 := by apply Matrix.ext; change ∀ i j, raw2962step2 i j = -(raw2962step1 i j); unfold raw2962step2 raw2962step1; decide +kernel
      have hl : raw2962step2Labels = raw2962step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2962step2 raw2962step2Labels = mixedMoment B raw2962step3 raw2962step3Labels := by
      have ha : raw2962step3 = raw2962step2 := by apply Matrix.ext; unfold raw2962step3 raw2962step2; decide +kernel
      have hl : raw2962step2Labels = labelEmbedding6 ∘ raw2962step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2962step2 raw2962step2Labels raw2962step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw2963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0]]
def raw2963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2963step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2963step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2963 raw2963Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2963 raw2963Labels = mixedMoment B raw2963step0 raw2963step0Labels := by
      have hz : ∀ j, raw2963 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw2963step0 = (fun i j => raw2963 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw2963step0 raw2963; decide +kernel
      have hl : raw2963step0Labels = raw2963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2963 raw2963Labels permutation590 hz
    mixedMoment B raw2963step0 raw2963step0Labels = mixedMoment B raw2963step1 raw2963step1Labels := by
      have hz : ∀ j, raw2963step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2963step1 = (fun i j => raw2963step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2963step1 raw2963step0; decide +kernel
      have hl : raw2963step1Labels = raw2963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2963step0 raw2963step0Labels permutation56 hz
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw2964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2964step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2964 raw2964Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw2964 raw2964Labels = mixedMoment B raw2964step0 raw2964step0Labels := by
      have hz : ∀ j, raw2964 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2964step0 = (fun i j => raw2964 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2964step0 raw2964; decide +kernel
      have hl : raw2964step0Labels = raw2964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2964 raw2964Labels permutation265 hz
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw2965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2965step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2965step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2965step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2965step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2965 raw2965Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw2965 raw2965Labels = mixedMoment B raw2965step0 raw2965step0Labels := by
      have ha : raw2965step0 = (fun i j => raw2965 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2965step0 raw2965; decide +kernel
      have hl : raw2965step0Labels = raw2965Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2965 raw2965Labels permutation682 permutation3
    mixedMoment B raw2965step0 raw2965step0Labels = mixedMoment B raw2965step1 raw2965step1Labels := by
      have ha : raw2965step1 = -raw2965step0 := by apply Matrix.ext; change ∀ i j, raw2965step1 i j = -(raw2965step0 i j); unfold raw2965step1 raw2965step0; decide +kernel
      have hl : raw2965step1Labels = raw2965step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2965step1 raw2965step1Labels = mixedMoment B raw2965step2 raw2965step2Labels := by
      have ha : raw2965step2 = raw2965step1 := by apply Matrix.ext; unfold raw2965step2 raw2965step1; decide +kernel
      have hl : raw2965step1Labels = labelEmbedding6 ∘ raw2965step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2965step1 raw2965step1Labels raw2965step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw2966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2966step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2966step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2966step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2966step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2966 raw2966Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2966 raw2966Labels = mixedMoment B raw2966step0 raw2966step0Labels := by
      have hz : ∀ j, raw2966 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2966step0 = (fun i j => raw2966 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2966step0 raw2966; decide +kernel
      have hl : raw2966step0Labels = raw2966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2966 raw2966Labels permutation265 hz
    mixedMoment B raw2966step0 raw2966step0Labels = mixedMoment B raw2966step1 raw2966step1Labels := by
      have ha : raw2966step1 = (fun i j => raw2966step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2966step1 raw2966step0; decide +kernel
      have hl : raw2966step1Labels = raw2966step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2966step0 raw2966step0Labels permutation151 permutation3
    mixedMoment B raw2966step1 raw2966step1Labels = mixedMoment B raw2966step2 raw2966step2Labels := by
      have ha : raw2966step2 = -raw2966step1 := by apply Matrix.ext; change ∀ i j, raw2966step2 i j = -(raw2966step1 i j); unfold raw2966step2 raw2966step1; decide +kernel
      have hl : raw2966step2Labels = raw2966step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2966step2 raw2966step2Labels = mixedMoment B raw2966step3 raw2966step3Labels := by
      have ha : raw2966step3 = raw2966step2 := by apply Matrix.ext; unfold raw2966step3 raw2966step2; decide +kernel
      have hl : raw2966step2Labels = labelEmbedding6 ∘ raw2966step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2966step2 raw2966step2Labels raw2966step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw2967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2967step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2967step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2967step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2967step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2967 raw2967Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2967 raw2967Labels = mixedMoment B raw2967step0 raw2967step0Labels := by
      have hz : ∀ j, raw2967 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2967step0 = (fun i j => raw2967 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2967step0 raw2967; decide +kernel
      have hl : raw2967step0Labels = raw2967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2967 raw2967Labels permutation265 hz
    mixedMoment B raw2967step0 raw2967step0Labels = mixedMoment B raw2967step1 raw2967step1Labels := by
      have ha : raw2967step1 = (fun i j => raw2967step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2967step1 raw2967step0; decide +kernel
      have hl : raw2967step1Labels = raw2967step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2967step0 raw2967step0Labels permutation149 permutation3
    mixedMoment B raw2967step1 raw2967step1Labels = mixedMoment B raw2967step2 raw2967step2Labels := by
      have ha : raw2967step2 = -raw2967step1 := by apply Matrix.ext; change ∀ i j, raw2967step2 i j = -(raw2967step1 i j); unfold raw2967step2 raw2967step1; decide +kernel
      have hl : raw2967step2Labels = raw2967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2967step2 raw2967step2Labels = mixedMoment B raw2967step3 raw2967step3Labels := by
      have ha : raw2967step3 = raw2967step2 := by apply Matrix.ext; unfold raw2967step3 raw2967step2; decide +kernel
      have hl : raw2967step2Labels = labelEmbedding6 ∘ raw2967step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2967step2 raw2967step2Labels raw2967step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw2968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw2968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2968step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2968 raw2968Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2968 raw2968Labels = mixedMoment B raw2968step0 raw2968step0Labels := by
      have hz : ∀ j, raw2968 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2968step0 = (fun i j => raw2968 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2968step0 raw2968; decide +kernel
      have hl : raw2968step0Labels = raw2968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2968 raw2968Labels permutation520 hz
    mixedMoment B raw2968step0 raw2968step0Labels = mixedMoment B raw2968step1 raw2968step1Labels := by
      have hz : ∀ j, raw2968step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2968step1 = (fun i j => raw2968step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2968step1 raw2968step0; decide +kernel
      have hl : raw2968step1Labels = raw2968step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2968step0 raw2968step0Labels permutation56 hz
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw2969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2969 raw2969Labels = mixedMoment B node4009 node4009Labels := by
  calc
    mixedMoment B raw2969 raw2969Labels = mixedMoment B raw2969step0 raw2969step0Labels := by
      have ha : raw2969step0 = (fun i j => raw2969 (permutation240 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2969step0 raw2969; decide +kernel
      have hl : raw2969step0Labels = raw2969Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2969 raw2969Labels permutation240 permutation6
    mixedMoment B raw2969step0 raw2969step0Labels = mixedMoment B raw2969step1 raw2969step1Labels := by
      have ha : raw2969step1 = -raw2969step0 := by apply Matrix.ext; change ∀ i j, raw2969step1 i j = -(raw2969step0 i j); unfold raw2969step1 raw2969step0; decide +kernel
      have hl : raw2969step1Labels = raw2969step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4009 node4009Labels := by rfl

def raw2970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2970 raw2970Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw2970 raw2970Labels = mixedMoment B raw2970step0 raw2970step0Labels := by
      have hz : ∀ j, raw2970 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2970step0 = (fun i j => raw2970 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2970step0 raw2970; decide +kernel
      have hl : raw2970step0Labels = raw2970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2970 raw2970Labels permutation265 hz
    mixedMoment B raw2970step0 raw2970step0Labels = mixedMoment B raw2970step1 raw2970step1Labels := by
      have ha : raw2970step1 = (fun i j => raw2970step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2970step1 raw2970step0; decide +kernel
      have hl : raw2970step1Labels = raw2970step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2970step0 raw2970step0Labels permutation49 permutation6
    mixedMoment B raw2970step1 raw2970step1Labels = mixedMoment B raw2970step2 raw2970step2Labels := by
      have ha : raw2970step2 = -raw2970step1 := by apply Matrix.ext; change ∀ i j, raw2970step2 i j = -(raw2970step1 i j); unfold raw2970step2 raw2970step1; decide +kernel
      have hl : raw2970step2Labels = raw2970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw2971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2971 raw2971Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw2971 raw2971Labels = mixedMoment B raw2971step0 raw2971step0Labels := by
      have hz : ∀ j, raw2971 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2971step0 = (fun i j => raw2971 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2971step0 raw2971; decide +kernel
      have hl : raw2971step0Labels = raw2971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2971 raw2971Labels permutation265 hz
    mixedMoment B raw2971step0 raw2971step0Labels = mixedMoment B raw2971step1 raw2971step1Labels := by
      have ha : raw2971step1 = (fun i j => raw2971step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2971step1 raw2971step0; decide +kernel
      have hl : raw2971step1Labels = raw2971step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2971step0 raw2971step0Labels permutation48 permutation6
    mixedMoment B raw2971step1 raw2971step1Labels = mixedMoment B raw2971step2 raw2971step2Labels := by
      have ha : raw2971step2 = -raw2971step1 := by apply Matrix.ext; change ∀ i j, raw2971step2 i j = -(raw2971step1 i j); unfold raw2971step2 raw2971step1; decide +kernel
      have hl : raw2971step2Labels = raw2971step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw2972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2972step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2972 raw2972Labels = mixedMoment B node4016 node4016Labels := by
  calc
    mixedMoment B raw2972 raw2972Labels = mixedMoment B raw2972step0 raw2972step0Labels := by
      have hz : ∀ j, raw2972 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2972step0 = (fun i j => raw2972 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2972step0 raw2972; decide +kernel
      have hl : raw2972step0Labels = raw2972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2972 raw2972Labels permutation520 hz
    mixedMoment B raw2972step0 raw2972step0Labels = mixedMoment B raw2972step1 raw2972step1Labels := by
      have hz : ∀ j, raw2972step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2972step1 = (fun i j => raw2972step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2972step1 raw2972step0; decide +kernel
      have hl : raw2972step1Labels = raw2972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2972step0 raw2972step0Labels permutation56 hz
    mixedMoment B raw2972step1 raw2972step1Labels = mixedMoment B raw2972step2 raw2972step2Labels := by
      have ha : raw2972step2 = (fun i j => raw2972step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2972step2 raw2972step1; decide +kernel
      have hl : raw2972step2Labels = raw2972step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2972step1 raw2972step1Labels permutation12 permutation6
    mixedMoment B raw2972step2 raw2972step2Labels = mixedMoment B raw2972step3 raw2972step3Labels := by
      have ha : raw2972step3 = -raw2972step2 := by apply Matrix.ext; change ∀ i j, raw2972step3 i j = -(raw2972step2 i j); unfold raw2972step3 raw2972step2; decide +kernel
      have hl : raw2972step3Labels = raw2972step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4016 node4016Labels := by rfl

def raw2973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2973step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2973step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2973step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2973step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2973 raw2973Labels = mixedMoment B node4016 node4016Labels := by
  calc
    mixedMoment B raw2973 raw2973Labels = mixedMoment B raw2973step0 raw2973step0Labels := by
      have hz : ∀ j, raw2973 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw2973step0 = (fun i j => raw2973 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw2973step0 raw2973; decide +kernel
      have hl : raw2973step0Labels = raw2973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2973 raw2973Labels permutation590 hz
    mixedMoment B raw2973step0 raw2973step0Labels = mixedMoment B raw2973step1 raw2973step1Labels := by
      have hz : ∀ j, raw2973step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2973step1 = (fun i j => raw2973step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2973step1 raw2973step0; decide +kernel
      have hl : raw2973step1Labels = raw2973step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2973step0 raw2973step0Labels permutation56 hz
    mixedMoment B raw2973step1 raw2973step1Labels = mixedMoment B raw2973step2 raw2973step2Labels := by
      have ha : raw2973step2 = (fun i j => raw2973step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2973step2 raw2973step1; decide +kernel
      have hl : raw2973step2Labels = raw2973step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2973step1 raw2973step1Labels permutation12 permutation6
    mixedMoment B raw2973step2 raw2973step2Labels = mixedMoment B raw2973step3 raw2973step3Labels := by
      have ha : raw2973step3 = -raw2973step2 := by apply Matrix.ext; change ∀ i j, raw2973step3 i j = -(raw2973step2 i j); unfold raw2973step3 raw2973step2; decide +kernel
      have hl : raw2973step3Labels = raw2973step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4016 node4016Labels := by rfl

def raw2974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2974 raw2974Labels = mixedMoment B node3076 node3076Labels := by
  calc
    mixedMoment B raw2974 raw2974Labels = mixedMoment B raw2974step0 raw2974step0Labels := by
      have ha : raw2974step0 = (fun i j => raw2974 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2974step0 raw2974; decide +kernel
      have hl : raw2974step0Labels = raw2974Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2974 raw2974Labels permutation182 permutation3
    _ = mixedMoment B node3076 node3076Labels := by rfl

def raw2975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2975 raw2975Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw2975 raw2975Labels = mixedMoment B raw2975step0 raw2975step0Labels := by
      have ha : raw2975step0 = (fun i j => raw2975 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2975step0 raw2975; decide +kernel
      have hl : raw2975step0Labels = raw2975Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2975 raw2975Labels permutation182 permutation3
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw2976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2976 raw2976Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw2976 raw2976Labels = mixedMoment B raw2976step0 raw2976step0Labels := by
      have ha : raw2976step0 = (fun i j => raw2976 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2976step0 raw2976; decide +kernel
      have hl : raw2976step0Labels = raw2976Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2976 raw2976Labels permutation206 permutation3
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw2977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2977 raw2977Labels = mixedMoment B node4039 node4039Labels := by
  calc
    mixedMoment B raw2977 raw2977Labels = mixedMoment B raw2977step0 raw2977step0Labels := by
      have hz : ∀ j, raw2977 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2977step0 = (fun i j => raw2977 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2977step0 raw2977; decide +kernel
      have hl : raw2977step0Labels = raw2977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2977 raw2977Labels permutation520 hz
    mixedMoment B raw2977step0 raw2977step0Labels = mixedMoment B raw2977step1 raw2977step1Labels := by
      have ha : raw2977step1 = (fun i j => raw2977step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2977step1 raw2977step0; decide +kernel
      have hl : raw2977step1Labels = raw2977step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2977step0 raw2977step0Labels permutation40 permutation3
    _ = mixedMoment B node4039 node4039Labels := by rfl

def raw2978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2978 raw2978Labels = mixedMoment B node4039 node4039Labels := by
  calc
    mixedMoment B raw2978 raw2978Labels = mixedMoment B raw2978step0 raw2978step0Labels := by
      have hz : ∀ j, raw2978 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw2978step0 = (fun i j => raw2978 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw2978step0 raw2978; decide +kernel
      have hl : raw2978step0Labels = raw2978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2978 raw2978Labels permutation590 hz
    mixedMoment B raw2978step0 raw2978step0Labels = mixedMoment B raw2978step1 raw2978step1Labels := by
      have ha : raw2978step1 = (fun i j => raw2978step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2978step1 raw2978step0; decide +kernel
      have hl : raw2978step1Labels = raw2978step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2978step0 raw2978step0Labels permutation40 permutation3
    _ = mixedMoment B node4039 node4039Labels := by rfl

def raw2979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2979 raw2979Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw2979 raw2979Labels = mixedMoment B raw2979step0 raw2979step0Labels := by
      have hz : ∀ j, raw2979 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2979step0 = (fun i j => raw2979 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2979step0 raw2979; decide +kernel
      have hl : raw2979step0Labels = raw2979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2979 raw2979Labels permutation265 hz
    mixedMoment B raw2979step0 raw2979step0Labels = mixedMoment B raw2979step1 raw2979step1Labels := by
      have ha : raw2979step1 = (fun i j => raw2979step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2979step1 raw2979step0; decide +kernel
      have hl : raw2979step1Labels = raw2979step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2979step0 raw2979step0Labels permutation38 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw2980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2980 raw2980Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw2980 raw2980Labels = mixedMoment B raw2980step0 raw2980step0Labels := by
      have ha : raw2980step0 = (fun i j => raw2980 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2980step0 raw2980; decide +kernel
      have hl : raw2980step0Labels = raw2980Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2980 raw2980Labels permutation158 permutation3
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw2981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2981 raw2981Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw2981 raw2981Labels = mixedMoment B raw2981step0 raw2981step0Labels := by
      have hz : ∀ j, raw2981 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2981step0 = (fun i j => raw2981 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2981step0 raw2981; decide +kernel
      have hl : raw2981step0Labels = raw2981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2981 raw2981Labels permutation265 hz
    mixedMoment B raw2981step0 raw2981step0Labels = mixedMoment B raw2981step1 raw2981step1Labels := by
      have ha : raw2981step1 = (fun i j => raw2981step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2981step1 raw2981step0; decide +kernel
      have hl : raw2981step1Labels = raw2981step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2981step0 raw2981step0Labels permutation38 permutation3
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw2982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2982step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2982 raw2982Labels = mixedMoment B node4040 node4040Labels := by
  calc
    mixedMoment B raw2982 raw2982Labels = mixedMoment B raw2982step0 raw2982step0Labels := by
      have hz : ∀ j, raw2982 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2982step0 = (fun i j => raw2982 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2982step0 raw2982; decide +kernel
      have hl : raw2982step0Labels = raw2982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2982 raw2982Labels permutation520 hz
    mixedMoment B raw2982step0 raw2982step0Labels = mixedMoment B raw2982step1 raw2982step1Labels := by
      have hz : ∀ j, raw2982step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2982step1 = (fun i j => raw2982step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2982step1 raw2982step0; decide +kernel
      have hl : raw2982step1Labels = raw2982step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2982step0 raw2982step0Labels permutation56 hz
    mixedMoment B raw2982step1 raw2982step1Labels = mixedMoment B raw2982step2 raw2982step2Labels := by
      have ha : raw2982step2 = (fun i j => raw2982step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2982step2 raw2982step1; decide +kernel
      have hl : raw2982step2Labels = raw2982step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2982step1 raw2982step1Labels permutation10 permutation3
    _ = mixedMoment B node4040 node4040Labels := by rfl

def raw2983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2983step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2983step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2983 raw2983Labels = mixedMoment B node4040 node4040Labels := by
  calc
    mixedMoment B raw2983 raw2983Labels = mixedMoment B raw2983step0 raw2983step0Labels := by
      have hz : ∀ j, raw2983 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw2983step0 = (fun i j => raw2983 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw2983step0 raw2983; decide +kernel
      have hl : raw2983step0Labels = raw2983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2983 raw2983Labels permutation590 hz
    mixedMoment B raw2983step0 raw2983step0Labels = mixedMoment B raw2983step1 raw2983step1Labels := by
      have hz : ∀ j, raw2983step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2983step1 = (fun i j => raw2983step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2983step1 raw2983step0; decide +kernel
      have hl : raw2983step1Labels = raw2983step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2983step0 raw2983step0Labels permutation56 hz
    mixedMoment B raw2983step1 raw2983step1Labels = mixedMoment B raw2983step2 raw2983step2Labels := by
      have ha : raw2983step2 = (fun i j => raw2983step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2983step2 raw2983step1; decide +kernel
      have hl : raw2983step2Labels = raw2983step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2983step1 raw2983step1Labels permutation10 permutation3
    _ = mixedMoment B node4040 node4040Labels := by rfl

def raw2984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2984step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2984 raw2984Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw2984 raw2984Labels = mixedMoment B raw2984step0 raw2984step0Labels := by
      have hz : ∀ j, raw2984 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2984step0 = (fun i j => raw2984 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2984step0 raw2984; decide +kernel
      have hl : raw2984step0Labels = raw2984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2984 raw2984Labels permutation265 hz
    mixedMoment B raw2984step0 raw2984step0Labels = mixedMoment B raw2984step1 raw2984step1Labels := by
      have ha : raw2984step1 = (fun i j => raw2984step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2984step1 raw2984step0; decide +kernel
      have hl : raw2984step1Labels = raw2984step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2984step0 raw2984step0Labels permutation32 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw2985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2985 raw2985Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw2985 raw2985Labels = mixedMoment B raw2985step0 raw2985step0Labels := by
      have ha : raw2985step0 = (fun i j => raw2985 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2985step0 raw2985; decide +kernel
      have hl : raw2985step0Labels = raw2985Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2985 raw2985Labels permutation152 permutation3
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw2986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2986 raw2986Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw2986 raw2986Labels = mixedMoment B raw2986step0 raw2986step0Labels := by
      have hz : ∀ j, raw2986 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2986step0 = (fun i j => raw2986 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2986step0 raw2986; decide +kernel
      have hl : raw2986step0Labels = raw2986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2986 raw2986Labels permutation265 hz
    mixedMoment B raw2986step0 raw2986step0Labels = mixedMoment B raw2986step1 raw2986step1Labels := by
      have ha : raw2986step1 = (fun i j => raw2986step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2986step1 raw2986step0; decide +kernel
      have hl : raw2986step1Labels = raw2986step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2986step0 raw2986step0Labels permutation32 permutation3
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw2987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2987Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2987step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2987step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2987 raw2987Labels = mixedMoment B node4040 node4040Labels := by
  calc
    mixedMoment B raw2987 raw2987Labels = mixedMoment B raw2987step0 raw2987step0Labels := by
      have hz : ∀ j, raw2987 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2987step0 = (fun i j => raw2987 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2987step0 raw2987; decide +kernel
      have hl : raw2987step0Labels = raw2987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2987 raw2987Labels permutation520 hz
    mixedMoment B raw2987step0 raw2987step0Labels = mixedMoment B raw2987step1 raw2987step1Labels := by
      have hz : ∀ j, raw2987step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2987step1 = (fun i j => raw2987step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2987step1 raw2987step0; decide +kernel
      have hl : raw2987step1Labels = raw2987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2987step0 raw2987step0Labels permutation56 hz
    mixedMoment B raw2987step1 raw2987step1Labels = mixedMoment B raw2987step2 raw2987step2Labels := by
      have ha : raw2987step2 = (fun i j => raw2987step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2987step2 raw2987step1; decide +kernel
      have hl : raw2987step2Labels = raw2987step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2987step1 raw2987step1Labels permutation8 permutation3
    _ = mixedMoment B node4040 node4040Labels := by rfl

def raw2988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2988Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2988step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2988step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2988 raw2988Labels = mixedMoment B node4040 node4040Labels := by
  calc
    mixedMoment B raw2988 raw2988Labels = mixedMoment B raw2988step0 raw2988step0Labels := by
      have hz : ∀ j, raw2988 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw2988step0 = (fun i j => raw2988 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw2988step0 raw2988; decide +kernel
      have hl : raw2988step0Labels = raw2988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2988 raw2988Labels permutation590 hz
    mixedMoment B raw2988step0 raw2988step0Labels = mixedMoment B raw2988step1 raw2988step1Labels := by
      have hz : ∀ j, raw2988step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2988step1 = (fun i j => raw2988step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2988step1 raw2988step0; decide +kernel
      have hl : raw2988step1Labels = raw2988step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2988step0 raw2988step0Labels permutation56 hz
    mixedMoment B raw2988step1 raw2988step1Labels = mixedMoment B raw2988step2 raw2988step2Labels := by
      have ha : raw2988step2 = (fun i j => raw2988step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2988step2 raw2988step1; decide +kernel
      have hl : raw2988step2Labels = raw2988step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2988step1 raw2988step1Labels permutation8 permutation3
    _ = mixedMoment B node4040 node4040Labels := by rfl

def raw2989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2989Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2989step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2989 raw2989Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw2989 raw2989Labels = mixedMoment B raw2989step0 raw2989step0Labels := by
      have hz : ∀ j, raw2989 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2989step0 = (fun i j => raw2989 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2989step0 raw2989; decide +kernel
      have hl : raw2989step0Labels = raw2989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2989 raw2989Labels permutation265 hz
    mixedMoment B raw2989step0 raw2989step0Labels = mixedMoment B raw2989step1 raw2989step1Labels := by
      have ha : raw2989step1 = (fun i j => raw2989step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2989step1 raw2989step0; decide +kernel
      have hl : raw2989step1Labels = raw2989step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2989step0 raw2989step0Labels permutation33 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw2990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2990Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2990 raw2990Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw2990 raw2990Labels = mixedMoment B raw2990step0 raw2990step0Labels := by
      have ha : raw2990step0 = (fun i j => raw2990 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2990step0 raw2990; decide +kernel
      have hl : raw2990step0Labels = raw2990Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2990 raw2990Labels permutation584 permutation3
    mixedMoment B raw2990step0 raw2990step0Labels = mixedMoment B raw2990step1 raw2990step1Labels := by
      have ha : raw2990step1 = -raw2990step0 := by apply Matrix.ext; change ∀ i j, raw2990step1 i j = -(raw2990step0 i j); unfold raw2990step1 raw2990step0; decide +kernel
      have hl : raw2990step1Labels = raw2990step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw2991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2991Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2991step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2991 raw2991Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2991 raw2991Labels = mixedMoment B raw2991step0 raw2991step0Labels := by
      have hz : ∀ j, raw2991 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2991step0 = (fun i j => raw2991 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2991step0 raw2991; decide +kernel
      have hl : raw2991step0Labels = raw2991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2991 raw2991Labels permutation265 hz
    mixedMoment B raw2991step0 raw2991step0Labels = mixedMoment B raw2991step1 raw2991step1Labels := by
      have ha : raw2991step1 = (fun i j => raw2991step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2991step1 raw2991step0; decide +kernel
      have hl : raw2991step1Labels = raw2991step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2991step0 raw2991step0Labels permutation127 permutation3
    mixedMoment B raw2991step1 raw2991step1Labels = mixedMoment B raw2991step2 raw2991step2Labels := by
      have ha : raw2991step2 = -raw2991step1 := by apply Matrix.ext; change ∀ i j, raw2991step2 i j = -(raw2991step1 i j); unfold raw2991step2 raw2991step1; decide +kernel
      have hl : raw2991step2Labels = raw2991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw2992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2992step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2992 raw2992Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2992 raw2992Labels = mixedMoment B raw2992step0 raw2992step0Labels := by
      have hz : ∀ j, raw2992 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2992step0 = (fun i j => raw2992 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2992step0 raw2992; decide +kernel
      have hl : raw2992step0Labels = raw2992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2992 raw2992Labels permutation265 hz
    mixedMoment B raw2992step0 raw2992step0Labels = mixedMoment B raw2992step1 raw2992step1Labels := by
      have ha : raw2992step1 = (fun i j => raw2992step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2992step1 raw2992step0; decide +kernel
      have hl : raw2992step1Labels = raw2992step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2992step0 raw2992step0Labels permutation125 permutation3
    mixedMoment B raw2992step1 raw2992step1Labels = mixedMoment B raw2992step2 raw2992step2Labels := by
      have ha : raw2992step2 = -raw2992step1 := by apply Matrix.ext; change ∀ i j, raw2992step2 i j = -(raw2992step1 i j); unfold raw2992step2 raw2992step1; decide +kernel
      have hl : raw2992step2Labels = raw2992step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw2993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0]]
def raw2993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2993step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2993 raw2993Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw2993 raw2993Labels = mixedMoment B raw2993step0 raw2993step0Labels := by
      have hz : ∀ j, raw2993 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw2993step0 = (fun i j => raw2993 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw2993step0 raw2993; decide +kernel
      have hl : raw2993step0Labels = raw2993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2993 raw2993Labels permutation590 hz
    mixedMoment B raw2993step0 raw2993step0Labels = mixedMoment B raw2993step1 raw2993step1Labels := by
      have hz : ∀ j, raw2993step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2993step1 = (fun i j => raw2993step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2993step1 raw2993step0; decide +kernel
      have hl : raw2993step1Labels = raw2993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2993step0 raw2993step0Labels permutation56 hz
    mixedMoment B raw2993step1 raw2993step1Labels = mixedMoment B raw2993step2 raw2993step2Labels := by
      have ha : raw2993step2 = (fun i j => raw2993step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2993step2 raw2993step1; decide +kernel
      have hl : raw2993step2Labels = raw2993step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2993step1 raw2993step1Labels permutation29 permutation3
    mixedMoment B raw2993step2 raw2993step2Labels = mixedMoment B raw2993step3 raw2993step3Labels := by
      have ha : raw2993step3 = -raw2993step2 := by apply Matrix.ext; change ∀ i j, raw2993step3 i j = -(raw2993step2 i j); unfold raw2993step3 raw2993step2; decide +kernel
      have hl : raw2993step3Labels = raw2993step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw2994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2994step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2994 raw2994Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw2994 raw2994Labels = mixedMoment B raw2994step0 raw2994step0Labels := by
      have hz : ∀ j, raw2994 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2994step0 = (fun i j => raw2994 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2994step0 raw2994; decide +kernel
      have hl : raw2994step0Labels = raw2994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2994 raw2994Labels permutation265 hz
    mixedMoment B raw2994step0 raw2994step0Labels = mixedMoment B raw2994step1 raw2994step1Labels := by
      have ha : raw2994step1 = (fun i j => raw2994step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2994step1 raw2994step0; decide +kernel
      have hl : raw2994step1Labels = raw2994step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2994step0 raw2994step0Labels permutation32 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw2995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2995step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2995 raw2995Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw2995 raw2995Labels = mixedMoment B raw2995step0 raw2995step0Labels := by
      have ha : raw2995step0 = (fun i j => raw2995 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2995step0 raw2995; decide +kernel
      have hl : raw2995step0Labels = raw2995Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2995 raw2995Labels permutation682 permutation3
    mixedMoment B raw2995step0 raw2995step0Labels = mixedMoment B raw2995step1 raw2995step1Labels := by
      have ha : raw2995step1 = -raw2995step0 := by apply Matrix.ext; change ∀ i j, raw2995step1 i j = -(raw2995step0 i j); unfold raw2995step1 raw2995step0; decide +kernel
      have hl : raw2995step1Labels = raw2995step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw2996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2996step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2996 raw2996Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2996 raw2996Labels = mixedMoment B raw2996step0 raw2996step0Labels := by
      have hz : ∀ j, raw2996 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2996step0 = (fun i j => raw2996 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2996step0 raw2996; decide +kernel
      have hl : raw2996step0Labels = raw2996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2996 raw2996Labels permutation265 hz
    mixedMoment B raw2996step0 raw2996step0Labels = mixedMoment B raw2996step1 raw2996step1Labels := by
      have ha : raw2996step1 = (fun i j => raw2996step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2996step1 raw2996step0; decide +kernel
      have hl : raw2996step1Labels = raw2996step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2996step0 raw2996step0Labels permutation151 permutation3
    mixedMoment B raw2996step1 raw2996step1Labels = mixedMoment B raw2996step2 raw2996step2Labels := by
      have ha : raw2996step2 = -raw2996step1 := by apply Matrix.ext; change ∀ i j, raw2996step2 i j = -(raw2996step1 i j); unfold raw2996step2 raw2996step1; decide +kernel
      have hl : raw2996step2Labels = raw2996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw2997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2997step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2997 raw2997Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2997 raw2997Labels = mixedMoment B raw2997step0 raw2997step0Labels := by
      have hz : ∀ j, raw2997 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2997step0 = (fun i j => raw2997 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2997step0 raw2997; decide +kernel
      have hl : raw2997step0Labels = raw2997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2997 raw2997Labels permutation265 hz
    mixedMoment B raw2997step0 raw2997step0Labels = mixedMoment B raw2997step1 raw2997step1Labels := by
      have ha : raw2997step1 = (fun i j => raw2997step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2997step1 raw2997step0; decide +kernel
      have hl : raw2997step1Labels = raw2997step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2997step0 raw2997step0Labels permutation149 permutation3
    mixedMoment B raw2997step1 raw2997step1Labels = mixedMoment B raw2997step2 raw2997step2Labels := by
      have ha : raw2997step2 = -raw2997step1 := by apply Matrix.ext; change ∀ i j, raw2997step2 i j = -(raw2997step1 i j); unfold raw2997step2 raw2997step1; decide +kernel
      have hl : raw2997step2Labels = raw2997step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw2998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw2998Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2998step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2998step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2998 raw2998Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw2998 raw2998Labels = mixedMoment B raw2998step0 raw2998step0Labels := by
      have hz : ∀ j, raw2998 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2998step0 = (fun i j => raw2998 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2998step0 raw2998; decide +kernel
      have hl : raw2998step0Labels = raw2998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2998 raw2998Labels permutation520 hz
    mixedMoment B raw2998step0 raw2998step0Labels = mixedMoment B raw2998step1 raw2998step1Labels := by
      have hz : ∀ j, raw2998step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2998step1 = (fun i j => raw2998step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2998step1 raw2998step0; decide +kernel
      have hl : raw2998step1Labels = raw2998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2998step0 raw2998step0Labels permutation56 hz
    mixedMoment B raw2998step1 raw2998step1Labels = mixedMoment B raw2998step2 raw2998step2Labels := by
      have ha : raw2998step2 = (fun i j => raw2998step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2998step2 raw2998step1; decide +kernel
      have hl : raw2998step2Labels = raw2998step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2998step1 raw2998step1Labels permutation29 permutation3
    mixedMoment B raw2998step2 raw2998step2Labels = mixedMoment B raw2998step3 raw2998step3Labels := by
      have ha : raw2998step3 = -raw2998step2 := by apply Matrix.ext; change ∀ i j, raw2998step3 i j = -(raw2998step2 i j); unfold raw2998step3 raw2998step2; decide +kernel
      have hl : raw2998step3Labels = raw2998step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw2999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw2999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2999step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2999 raw2999Labels = mixedMoment B node5498 node5498Labels := by
  calc
    mixedMoment B raw2999 raw2999Labels = mixedMoment B raw2999step0 raw2999step0Labels := by
      have ha : raw2999step0 = (fun i j => raw2999 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2999step0 raw2999; decide +kernel
      have hl : raw2999step0Labels = raw2999Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2999 raw2999Labels permutation583 permutation2
    mixedMoment B raw2999step0 raw2999step0Labels = mixedMoment B raw2999step1 raw2999step1Labels := by
      have ha : raw2999step1 = -raw2999step0 := by apply Matrix.ext; change ∀ i j, raw2999step1 i j = -(raw2999step0 i j); unfold raw2999step1 raw2999step0; decide +kernel
      have hl : raw2999step1Labels = raw2999step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5498 node5498Labels := by rfl

def raw3000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3000step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3000step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3000 raw3000Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3000 raw3000Labels = mixedMoment B raw3000step0 raw3000step0Labels := by
      have hz : ∀ j, raw3000 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3000step0 = (fun i j => raw3000 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3000step0 raw3000; decide +kernel
      have hl : raw3000step0Labels = raw3000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3000 raw3000Labels permutation265 hz
    mixedMoment B raw3000step0 raw3000step0Labels = mixedMoment B raw3000step1 raw3000step1Labels := by
      have ha : raw3000step1 = (fun i j => raw3000step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3000step1 raw3000step0; decide +kernel
      have hl : raw3000step1Labels = raw3000step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3000step0 raw3000step0Labels permutation126 permutation2
    mixedMoment B raw3000step1 raw3000step1Labels = mixedMoment B raw3000step2 raw3000step2Labels := by
      have ha : raw3000step2 = -raw3000step1 := by apply Matrix.ext; change ∀ i j, raw3000step2 i j = -(raw3000step1 i j); unfold raw3000step2 raw3000step1; decide +kernel
      have hl : raw3000step2Labels = raw3000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3001step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3001 raw3001Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3001 raw3001Labels = mixedMoment B raw3001step0 raw3001step0Labels := by
      have hz : ∀ j, raw3001 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3001step0 = (fun i j => raw3001 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3001step0 raw3001; decide +kernel
      have hl : raw3001step0Labels = raw3001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3001 raw3001Labels permutation265 hz
    mixedMoment B raw3001step0 raw3001step0Labels = mixedMoment B raw3001step1 raw3001step1Labels := by
      have ha : raw3001step1 = (fun i j => raw3001step0 (permutation124 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3001step1 raw3001step0; decide +kernel
      have hl : raw3001step1Labels = raw3001step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3001step0 raw3001step0Labels permutation124 permutation2
    mixedMoment B raw3001step1 raw3001step1Labels = mixedMoment B raw3001step2 raw3001step2Labels := by
      have ha : raw3001step2 = -raw3001step1 := by apply Matrix.ext; change ∀ i j, raw3001step2 i j = -(raw3001step1 i j); unfold raw3001step2 raw3001step1; decide +kernel
      have hl : raw3001step2Labels = raw3001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3002step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3002step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3002 raw3002Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3002 raw3002Labels = mixedMoment B raw3002step0 raw3002step0Labels := by
      have hz : ∀ j, raw3002 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3002step0 = (fun i j => raw3002 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3002step0 raw3002; decide +kernel
      have hl : raw3002step0Labels = raw3002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3002 raw3002Labels permutation265 hz
    mixedMoment B raw3002step0 raw3002step0Labels = mixedMoment B raw3002step1 raw3002step1Labels := by
      have ha : raw3002step1 = (fun i j => raw3002step0 (permutation66 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3002step1 raw3002step0; decide +kernel
      have hl : raw3002step1Labels = raw3002step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3002step0 raw3002step0Labels permutation66 permutation4
    mixedMoment B raw3002step1 raw3002step1Labels = mixedMoment B raw3002step2 raw3002step2Labels := by
      have ha : raw3002step2 = raw3002step1 := by apply Matrix.ext; unfold raw3002step2 raw3002step1; decide +kernel
      have hl : raw3002step1Labels = labelEmbedding7 ∘ raw3002step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3002step1 raw3002step1Labels raw3002step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3003step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3003step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3003 raw3003Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3003 raw3003Labels = mixedMoment B raw3003step0 raw3003step0Labels := by
      have hz : ∀ j, raw3003 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3003step0 = (fun i j => raw3003 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3003step0 raw3003; decide +kernel
      have hl : raw3003step0Labels = raw3003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3003 raw3003Labels permutation265 hz
    mixedMoment B raw3003step0 raw3003step0Labels = mixedMoment B raw3003step1 raw3003step1Labels := by
      have ha : raw3003step1 = (fun i j => raw3003step0 (permutation64 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3003step1 raw3003step0; decide +kernel
      have hl : raw3003step1Labels = raw3003step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3003step0 raw3003step0Labels permutation64 permutation4
    mixedMoment B raw3003step1 raw3003step1Labels = mixedMoment B raw3003step2 raw3003step2Labels := by
      have ha : raw3003step2 = raw3003step1 := by apply Matrix.ext; unfold raw3003step2 raw3003step1; decide +kernel
      have hl : raw3003step1Labels = labelEmbedding7 ∘ raw3003step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3003step1 raw3003step1Labels raw3003step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3004step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3004step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3004 raw3004Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw3004 raw3004Labels = mixedMoment B raw3004step0 raw3004step0Labels := by
      have ha : raw3004step0 = (fun i j => raw3004 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3004step0 raw3004; decide +kernel
      have hl : raw3004step0Labels = raw3004Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3004 raw3004Labels permutation185 permutation3
    mixedMoment B raw3004step0 raw3004step0Labels = mixedMoment B raw3004step1 raw3004step1Labels := by
      have ha : raw3004step1 = raw3004step0 := by apply Matrix.ext; unfold raw3004step1 raw3004step0; decide +kernel
      have hl : raw3004step0Labels = labelEmbedding6 ∘ raw3004step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3004step0 raw3004step0Labels raw3004step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw3005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3005step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3005 raw3005Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3005 raw3005Labels = mixedMoment B raw3005step0 raw3005step0Labels := by
      have ha : raw3005step0 = (fun i j => raw3005 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3005step0 raw3005; decide +kernel
      have hl : raw3005step0Labels = raw3005Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3005 raw3005Labels permutation185 permutation3
    mixedMoment B raw3005step0 raw3005step0Labels = mixedMoment B raw3005step1 raw3005step1Labels := by
      have ha : raw3005step1 = raw3005step0 := by apply Matrix.ext; unfold raw3005step1 raw3005step0; decide +kernel
      have hl : raw3005step0Labels = labelEmbedding6 ∘ raw3005step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3005step0 raw3005step0Labels raw3005step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw3006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3006step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3006 raw3006Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3006 raw3006Labels = mixedMoment B raw3006step0 raw3006step0Labels := by
      have ha : raw3006step0 = (fun i j => raw3006 (permutation209 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3006step0 raw3006; decide +kernel
      have hl : raw3006step0Labels = raw3006Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3006 raw3006Labels permutation209 permutation3
    mixedMoment B raw3006step0 raw3006step0Labels = mixedMoment B raw3006step1 raw3006step1Labels := by
      have ha : raw3006step1 = raw3006step0 := by apply Matrix.ext; unfold raw3006step1 raw3006step0; decide +kernel
      have hl : raw3006step0Labels = labelEmbedding6 ∘ raw3006step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3006step0 raw3006step0Labels raw3006step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw3007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3007step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3007step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3007step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3007step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3007 raw3007Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3007 raw3007Labels = mixedMoment B raw3007step0 raw3007step0Labels := by
      have ha : raw3007step0 = (fun i j => raw3007 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3007step0 raw3007; decide +kernel
      have hl : raw3007step0Labels = raw3007Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3007 raw3007Labels permutation243 permutation5
    mixedMoment B raw3007step0 raw3007step0Labels = mixedMoment B raw3007step1 raw3007step1Labels := by
      have ha : raw3007step1 = -raw3007step0 := by apply Matrix.ext; change ∀ i j, raw3007step1 i j = -(raw3007step0 i j); unfold raw3007step1 raw3007step0; decide +kernel
      have hl : raw3007step1Labels = raw3007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3007step1 raw3007step1Labels = mixedMoment B raw3007step2 raw3007step2Labels := by
      have ha : raw3007step2 = raw3007step1 := by apply Matrix.ext; unfold raw3007step2 raw3007step1; decide +kernel
      have hl : raw3007step1Labels = labelEmbedding8 ∘ raw3007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3007step1 raw3007step1Labels raw3007step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw3008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3008step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3008step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3008step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3008step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3008 raw3008Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3008 raw3008Labels = mixedMoment B raw3008step0 raw3008step0Labels := by
      have ha : raw3008step0 = (fun i j => raw3008 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3008step0 raw3008; decide +kernel
      have hl : raw3008step0Labels = raw3008Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3008 raw3008Labels permutation263 permutation5
    mixedMoment B raw3008step0 raw3008step0Labels = mixedMoment B raw3008step1 raw3008step1Labels := by
      have ha : raw3008step1 = -raw3008step0 := by apply Matrix.ext; change ∀ i j, raw3008step1 i j = -(raw3008step0 i j); unfold raw3008step1 raw3008step0; decide +kernel
      have hl : raw3008step1Labels = raw3008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3008step1 raw3008step1Labels = mixedMoment B raw3008step2 raw3008step2Labels := by
      have ha : raw3008step2 = raw3008step1 := by apply Matrix.ext; unfold raw3008step2 raw3008step1; decide +kernel
      have hl : raw3008step1Labels = labelEmbedding8 ∘ raw3008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3008step1 raw3008step1Labels raw3008step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw3009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3009step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3009step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3009step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3009step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3009 raw3009Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw3009 raw3009Labels = mixedMoment B raw3009step0 raw3009step0Labels := by
      have hz : ∀ j, raw3009 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3009step0 = (fun i j => raw3009 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3009step0 raw3009; decide +kernel
      have hl : raw3009step0Labels = raw3009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3009 raw3009Labels permutation265 hz
    mixedMoment B raw3009step0 raw3009step0Labels = mixedMoment B raw3009step1 raw3009step1Labels := by
      have ha : raw3009step1 = (fun i j => raw3009step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3009step1 raw3009step0; decide +kernel
      have hl : raw3009step1Labels = raw3009step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3009step0 raw3009step0Labels permutation49 permutation5
    mixedMoment B raw3009step1 raw3009step1Labels = mixedMoment B raw3009step2 raw3009step2Labels := by
      have ha : raw3009step2 = -raw3009step1 := by apply Matrix.ext; change ∀ i j, raw3009step2 i j = -(raw3009step1 i j); unfold raw3009step2 raw3009step1; decide +kernel
      have hl : raw3009step2Labels = raw3009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3009step2 raw3009step2Labels = mixedMoment B raw3009step3 raw3009step3Labels := by
      have ha : raw3009step3 = raw3009step2 := by apply Matrix.ext; unfold raw3009step3 raw3009step2; decide +kernel
      have hl : raw3009step2Labels = labelEmbedding8 ∘ raw3009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3009step2 raw3009step2Labels raw3009step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw3010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3010step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3010step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3010step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3010step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3010 raw3010Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3010 raw3010Labels = mixedMoment B raw3010step0 raw3010step0Labels := by
      have ha : raw3010step0 = (fun i j => raw3010 (permutation169 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3010step0 raw3010; decide +kernel
      have hl : raw3010step0Labels = raw3010Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3010 raw3010Labels permutation169 permutation5
    mixedMoment B raw3010step0 raw3010step0Labels = mixedMoment B raw3010step1 raw3010step1Labels := by
      have ha : raw3010step1 = -raw3010step0 := by apply Matrix.ext; change ∀ i j, raw3010step1 i j = -(raw3010step0 i j); unfold raw3010step1 raw3010step0; decide +kernel
      have hl : raw3010step1Labels = raw3010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3010step1 raw3010step1Labels = mixedMoment B raw3010step2 raw3010step2Labels := by
      have ha : raw3010step2 = raw3010step1 := by apply Matrix.ext; unfold raw3010step2 raw3010step1; decide +kernel
      have hl : raw3010step1Labels = labelEmbedding8 ∘ raw3010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3010step1 raw3010step1Labels raw3010step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw3011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3011step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3011step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3011 raw3011Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw3011 raw3011Labels = mixedMoment B raw3011step0 raw3011step0Labels := by
      have hz : ∀ j, raw3011 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3011step0 = (fun i j => raw3011 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3011step0 raw3011; decide +kernel
      have hl : raw3011step0Labels = raw3011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3011 raw3011Labels permutation265 hz
    mixedMoment B raw3011step0 raw3011step0Labels = mixedMoment B raw3011step1 raw3011step1Labels := by
      have ha : raw3011step1 = (fun i j => raw3011step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3011step1 raw3011step0; decide +kernel
      have hl : raw3011step1Labels = raw3011step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3011step0 raw3011step0Labels permutation41 permutation3
    mixedMoment B raw3011step1 raw3011step1Labels = mixedMoment B raw3011step2 raw3011step2Labels := by
      have ha : raw3011step2 = raw3011step1 := by apply Matrix.ext; unfold raw3011step2 raw3011step1; decide +kernel
      have hl : raw3011step1Labels = labelEmbedding6 ∘ raw3011step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3011step1 raw3011step1Labels raw3011step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw3012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3012step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3012step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3012step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3012step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3012 raw3012Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3012 raw3012Labels = mixedMoment B raw3012step0 raw3012step0Labels := by
      have hz : ∀ j, raw3012 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3012step0 = (fun i j => raw3012 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3012step0 raw3012; decide +kernel
      have hl : raw3012step0Labels = raw3012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3012 raw3012Labels permutation265 hz
    mixedMoment B raw3012step0 raw3012step0Labels = mixedMoment B raw3012step1 raw3012step1Labels := by
      have ha : raw3012step1 = (fun i j => raw3012step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3012step1 raw3012step0; decide +kernel
      have hl : raw3012step1Labels = raw3012step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3012step0 raw3012step0Labels permutation49 permutation5
    mixedMoment B raw3012step1 raw3012step1Labels = mixedMoment B raw3012step2 raw3012step2Labels := by
      have ha : raw3012step2 = -raw3012step1 := by apply Matrix.ext; change ∀ i j, raw3012step2 i j = -(raw3012step1 i j); unfold raw3012step2 raw3012step1; decide +kernel
      have hl : raw3012step2Labels = raw3012step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3012step2 raw3012step2Labels = mixedMoment B raw3012step3 raw3012step3Labels := by
      have ha : raw3012step3 = raw3012step2 := by apply Matrix.ext; unfold raw3012step3 raw3012step2; decide +kernel
      have hl : raw3012step2Labels = labelEmbedding8 ∘ raw3012step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3012step2 raw3012step2Labels raw3012step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3013step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3013step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3013step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3013step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3013 raw3013Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3013 raw3013Labels = mixedMoment B raw3013step0 raw3013step0Labels := by
      have hz : ∀ j, raw3013 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3013step0 = (fun i j => raw3013 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3013step0 raw3013; decide +kernel
      have hl : raw3013step0Labels = raw3013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3013 raw3013Labels permutation265 hz
    mixedMoment B raw3013step0 raw3013step0Labels = mixedMoment B raw3013step1 raw3013step1Labels := by
      have ha : raw3013step1 = (fun i j => raw3013step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3013step1 raw3013step0; decide +kernel
      have hl : raw3013step1Labels = raw3013step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3013step0 raw3013step0Labels permutation55 permutation5
    mixedMoment B raw3013step1 raw3013step1Labels = mixedMoment B raw3013step2 raw3013step2Labels := by
      have ha : raw3013step2 = -raw3013step1 := by apply Matrix.ext; change ∀ i j, raw3013step2 i j = -(raw3013step1 i j); unfold raw3013step2 raw3013step1; decide +kernel
      have hl : raw3013step2Labels = raw3013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3013step2 raw3013step2Labels = mixedMoment B raw3013step3 raw3013step3Labels := by
      have ha : raw3013step3 = raw3013step2 := by apply Matrix.ext; unfold raw3013step3 raw3013step2; decide +kernel
      have hl : raw3013step2Labels = labelEmbedding8 ∘ raw3013step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3013step2 raw3013step2Labels raw3013step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3014step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3014step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3014step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3014step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3014 raw3014Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw3014 raw3014Labels = mixedMoment B raw3014step0 raw3014step0Labels := by
      have hz : ∀ j, raw3014 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3014step0 = (fun i j => raw3014 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3014step0 raw3014; decide +kernel
      have hl : raw3014step0Labels = raw3014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3014 raw3014Labels permutation265 hz
    mixedMoment B raw3014step0 raw3014step0Labels = mixedMoment B raw3014step1 raw3014step1Labels := by
      have ha : raw3014step1 = (fun i j => raw3014step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3014step1 raw3014step0; decide +kernel
      have hl : raw3014step1Labels = raw3014step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3014step0 raw3014step0Labels permutation48 permutation5
    mixedMoment B raw3014step1 raw3014step1Labels = mixedMoment B raw3014step2 raw3014step2Labels := by
      have ha : raw3014step2 = -raw3014step1 := by apply Matrix.ext; change ∀ i j, raw3014step2 i j = -(raw3014step1 i j); unfold raw3014step2 raw3014step1; decide +kernel
      have hl : raw3014step2Labels = raw3014step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3014step2 raw3014step2Labels = mixedMoment B raw3014step3 raw3014step3Labels := by
      have ha : raw3014step3 = raw3014step2 := by apply Matrix.ext; unfold raw3014step3 raw3014step2; decide +kernel
      have hl : raw3014step2Labels = labelEmbedding8 ∘ raw3014step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3014step2 raw3014step2Labels raw3014step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw3015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3015step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3015step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3015step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3015step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3015 raw3015Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3015 raw3015Labels = mixedMoment B raw3015step0 raw3015step0Labels := by
      have ha : raw3015step0 = (fun i j => raw3015 (permutation168 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3015step0 raw3015; decide +kernel
      have hl : raw3015step0Labels = raw3015Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3015 raw3015Labels permutation168 permutation5
    mixedMoment B raw3015step0 raw3015step0Labels = mixedMoment B raw3015step1 raw3015step1Labels := by
      have ha : raw3015step1 = -raw3015step0 := by apply Matrix.ext; change ∀ i j, raw3015step1 i j = -(raw3015step0 i j); unfold raw3015step1 raw3015step0; decide +kernel
      have hl : raw3015step1Labels = raw3015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3015step1 raw3015step1Labels = mixedMoment B raw3015step2 raw3015step2Labels := by
      have ha : raw3015step2 = raw3015step1 := by apply Matrix.ext; unfold raw3015step2 raw3015step1; decide +kernel
      have hl : raw3015step1Labels = labelEmbedding8 ∘ raw3015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3015step1 raw3015step1Labels raw3015step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw3016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3016step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3016 raw3016Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw3016 raw3016Labels = mixedMoment B raw3016step0 raw3016step0Labels := by
      have hz : ∀ j, raw3016 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3016step0 = (fun i j => raw3016 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3016step0 raw3016; decide +kernel
      have hl : raw3016step0Labels = raw3016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3016 raw3016Labels permutation265 hz
    mixedMoment B raw3016step0 raw3016step0Labels = mixedMoment B raw3016step1 raw3016step1Labels := by
      have ha : raw3016step1 = (fun i j => raw3016step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3016step1 raw3016step0; decide +kernel
      have hl : raw3016step1Labels = raw3016step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3016step0 raw3016step0Labels permutation35 permutation3
    mixedMoment B raw3016step1 raw3016step1Labels = mixedMoment B raw3016step2 raw3016step2Labels := by
      have ha : raw3016step2 = raw3016step1 := by apply Matrix.ext; unfold raw3016step2 raw3016step1; decide +kernel
      have hl : raw3016step1Labels = labelEmbedding6 ∘ raw3016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3016step1 raw3016step1Labels raw3016step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw3017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3017step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3017step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3017step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3017step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3017 raw3017Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3017 raw3017Labels = mixedMoment B raw3017step0 raw3017step0Labels := by
      have hz : ∀ j, raw3017 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3017step0 = (fun i j => raw3017 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3017step0 raw3017; decide +kernel
      have hl : raw3017step0Labels = raw3017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3017 raw3017Labels permutation265 hz
    mixedMoment B raw3017step0 raw3017step0Labels = mixedMoment B raw3017step1 raw3017step1Labels := by
      have ha : raw3017step1 = (fun i j => raw3017step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3017step1 raw3017step0; decide +kernel
      have hl : raw3017step1Labels = raw3017step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3017step0 raw3017step0Labels permutation48 permutation5
    mixedMoment B raw3017step1 raw3017step1Labels = mixedMoment B raw3017step2 raw3017step2Labels := by
      have ha : raw3017step2 = -raw3017step1 := by apply Matrix.ext; change ∀ i j, raw3017step2 i j = -(raw3017step1 i j); unfold raw3017step2 raw3017step1; decide +kernel
      have hl : raw3017step2Labels = raw3017step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3017step2 raw3017step2Labels = mixedMoment B raw3017step3 raw3017step3Labels := by
      have ha : raw3017step3 = raw3017step2 := by apply Matrix.ext; unfold raw3017step3 raw3017step2; decide +kernel
      have hl : raw3017step2Labels = labelEmbedding8 ∘ raw3017step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3017step2 raw3017step2Labels raw3017step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3018step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3018step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3018step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3018step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3018 raw3018Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3018 raw3018Labels = mixedMoment B raw3018step0 raw3018step0Labels := by
      have hz : ∀ j, raw3018 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3018step0 = (fun i j => raw3018 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3018step0 raw3018; decide +kernel
      have hl : raw3018step0Labels = raw3018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3018 raw3018Labels permutation265 hz
    mixedMoment B raw3018step0 raw3018step0Labels = mixedMoment B raw3018step1 raw3018step1Labels := by
      have ha : raw3018step1 = (fun i j => raw3018step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3018step1 raw3018step0; decide +kernel
      have hl : raw3018step1Labels = raw3018step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3018step0 raw3018step0Labels permutation54 permutation5
    mixedMoment B raw3018step1 raw3018step1Labels = mixedMoment B raw3018step2 raw3018step2Labels := by
      have ha : raw3018step2 = -raw3018step1 := by apply Matrix.ext; change ∀ i j, raw3018step2 i j = -(raw3018step1 i j); unfold raw3018step2 raw3018step1; decide +kernel
      have hl : raw3018step2Labels = raw3018step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3018step2 raw3018step2Labels = mixedMoment B raw3018step3 raw3018step3Labels := by
      have ha : raw3018step3 = raw3018step2 := by apply Matrix.ext; unfold raw3018step3 raw3018step2; decide +kernel
      have hl : raw3018step2Labels = labelEmbedding8 ∘ raw3018step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3018step2 raw3018step2Labels raw3018step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3019step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3019step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3019 raw3019Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw3019 raw3019Labels = mixedMoment B raw3019step0 raw3019step0Labels := by
      have hz : ∀ j, raw3019 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3019step0 = (fun i j => raw3019 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3019step0 raw3019; decide +kernel
      have hl : raw3019step0Labels = raw3019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3019 raw3019Labels permutation265 hz
    mixedMoment B raw3019step0 raw3019step0Labels = mixedMoment B raw3019step1 raw3019step1Labels := by
      have ha : raw3019step1 = (fun i j => raw3019step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3019step1 raw3019step0; decide +kernel
      have hl : raw3019step1Labels = raw3019step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3019step0 raw3019step0Labels permutation33 permutation3
    mixedMoment B raw3019step1 raw3019step1Labels = mixedMoment B raw3019step2 raw3019step2Labels := by
      have ha : raw3019step2 = raw3019step1 := by apply Matrix.ext; unfold raw3019step2 raw3019step1; decide +kernel
      have hl : raw3019step1Labels = labelEmbedding6 ∘ raw3019step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3019step1 raw3019step1Labels raw3019step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw3020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3020step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3020 raw3020Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3020 raw3020Labels = mixedMoment B raw3020step0 raw3020step0Labels := by
      have ha : raw3020step0 = (fun i j => raw3020 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3020step0 raw3020; decide +kernel
      have hl : raw3020step0Labels = raw3020Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3020 raw3020Labels permutation153 permutation3
    mixedMoment B raw3020step0 raw3020step0Labels = mixedMoment B raw3020step1 raw3020step1Labels := by
      have ha : raw3020step1 = raw3020step0 := by apply Matrix.ext; unfold raw3020step1 raw3020step0; decide +kernel
      have hl : raw3020step0Labels = labelEmbedding6 ∘ raw3020step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3020step0 raw3020step0Labels raw3020step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw3021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3021step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3021step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3021 raw3021Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3021 raw3021Labels = mixedMoment B raw3021step0 raw3021step0Labels := by
      have hz : ∀ j, raw3021 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3021step0 = (fun i j => raw3021 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3021step0 raw3021; decide +kernel
      have hl : raw3021step0Labels = raw3021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3021 raw3021Labels permutation265 hz
    mixedMoment B raw3021step0 raw3021step0Labels = mixedMoment B raw3021step1 raw3021step1Labels := by
      have ha : raw3021step1 = (fun i j => raw3021step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3021step1 raw3021step0; decide +kernel
      have hl : raw3021step1Labels = raw3021step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3021step0 raw3021step0Labels permutation33 permutation3
    mixedMoment B raw3021step1 raw3021step1Labels = mixedMoment B raw3021step2 raw3021step2Labels := by
      have ha : raw3021step2 = raw3021step1 := by apply Matrix.ext; unfold raw3021step2 raw3021step1; decide +kernel
      have hl : raw3021step1Labels = labelEmbedding6 ∘ raw3021step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3021step1 raw3021step1Labels raw3021step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3022step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3022 raw3022Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3022 raw3022Labels = mixedMoment B raw3022step0 raw3022step0Labels := by
      have hz : ∀ j, raw3022 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3022step0 = (fun i j => raw3022 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3022step0 raw3022; decide +kernel
      have hl : raw3022step0Labels = raw3022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3022 raw3022Labels permutation265 hz
    mixedMoment B raw3022step0 raw3022step0Labels = mixedMoment B raw3022step1 raw3022step1Labels := by
      have ha : raw3022step1 = (fun i j => raw3022step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3022step1 raw3022step0; decide +kernel
      have hl : raw3022step1Labels = raw3022step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3022step0 raw3022step0Labels permutation39 permutation3
    mixedMoment B raw3022step1 raw3022step1Labels = mixedMoment B raw3022step2 raw3022step2Labels := by
      have ha : raw3022step2 = raw3022step1 := by apply Matrix.ext; unfold raw3022step2 raw3022step1; decide +kernel
      have hl : raw3022step1Labels = labelEmbedding6 ∘ raw3022step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3022step1 raw3022step1Labels raw3022step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw3023step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3023step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3023step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3023step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3023 raw3023Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw3023 raw3023Labels = mixedMoment B raw3023step0 raw3023step0Labels := by
      have hz : ∀ j, raw3023 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3023step0 = (fun i j => raw3023 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3023step0 raw3023; decide +kernel
      have hl : raw3023step0Labels = raw3023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3023 raw3023Labels permutation265 hz
    mixedMoment B raw3023step0 raw3023step0Labels = mixedMoment B raw3023step1 raw3023step1Labels := by
      have ha : raw3023step1 = (fun i j => raw3023step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3023step1 raw3023step0; decide +kernel
      have hl : raw3023step1Labels = raw3023step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3023step0 raw3023step0Labels permutation50 permutation5
    mixedMoment B raw3023step1 raw3023step1Labels = mixedMoment B raw3023step2 raw3023step2Labels := by
      have ha : raw3023step2 = -raw3023step1 := by apply Matrix.ext; change ∀ i j, raw3023step2 i j = -(raw3023step1 i j); unfold raw3023step2 raw3023step1; decide +kernel
      have hl : raw3023step2Labels = raw3023step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3023step2 raw3023step2Labels = mixedMoment B raw3023step3 raw3023step3Labels := by
      have ha : raw3023step3 = raw3023step2 := by apply Matrix.ext; unfold raw3023step3 raw3023step2; decide +kernel
      have hl : raw3023step2Labels = labelEmbedding8 ∘ raw3023step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3023step2 raw3023step2Labels raw3023step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw3024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3024step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3024step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3024 raw3024Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw3024 raw3024Labels = mixedMoment B raw3024step0 raw3024step0Labels := by
      have hz : ∀ j, raw3024 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3024step0 = (fun i j => raw3024 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3024step0 raw3024; decide +kernel
      have hl : raw3024step0Labels = raw3024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3024 raw3024Labels permutation265 hz
    mixedMoment B raw3024step0 raw3024step0Labels = mixedMoment B raw3024step1 raw3024step1Labels := by
      have ha : raw3024step1 = (fun i j => raw3024step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3024step1 raw3024step0; decide +kernel
      have hl : raw3024step1Labels = raw3024step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3024step0 raw3024step0Labels permutation32 permutation3
    mixedMoment B raw3024step1 raw3024step1Labels = mixedMoment B raw3024step2 raw3024step2Labels := by
      have ha : raw3024step2 = raw3024step1 := by apply Matrix.ext; unfold raw3024step2 raw3024step1; decide +kernel
      have hl : raw3024step1Labels = labelEmbedding6 ∘ raw3024step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3024step1 raw3024step1Labels raw3024step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw3025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3025step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3025 raw3025Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3025 raw3025Labels = mixedMoment B raw3025step0 raw3025step0Labels := by
      have ha : raw3025step0 = (fun i j => raw3025 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3025step0 raw3025; decide +kernel
      have hl : raw3025step0Labels = raw3025Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3025 raw3025Labels permutation152 permutation3
    mixedMoment B raw3025step0 raw3025step0Labels = mixedMoment B raw3025step1 raw3025step1Labels := by
      have ha : raw3025step1 = raw3025step0 := by apply Matrix.ext; unfold raw3025step1 raw3025step0; decide +kernel
      have hl : raw3025step0Labels = labelEmbedding6 ∘ raw3025step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3025step0 raw3025step0Labels raw3025step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw3026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3026step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3026step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3026 raw3026Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3026 raw3026Labels = mixedMoment B raw3026step0 raw3026step0Labels := by
      have hz : ∀ j, raw3026 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3026step0 = (fun i j => raw3026 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3026step0 raw3026; decide +kernel
      have hl : raw3026step0Labels = raw3026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3026 raw3026Labels permutation265 hz
    mixedMoment B raw3026step0 raw3026step0Labels = mixedMoment B raw3026step1 raw3026step1Labels := by
      have ha : raw3026step1 = (fun i j => raw3026step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3026step1 raw3026step0; decide +kernel
      have hl : raw3026step1Labels = raw3026step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3026step0 raw3026step0Labels permutation32 permutation3
    mixedMoment B raw3026step1 raw3026step1Labels = mixedMoment B raw3026step2 raw3026step2Labels := by
      have ha : raw3026step2 = raw3026step1 := by apply Matrix.ext; unfold raw3026step2 raw3026step1; decide +kernel
      have hl : raw3026step1Labels = labelEmbedding6 ∘ raw3026step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3026step1 raw3026step1Labels raw3026step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3027step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3027 raw3027Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3027 raw3027Labels = mixedMoment B raw3027step0 raw3027step0Labels := by
      have hz : ∀ j, raw3027 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3027step0 = (fun i j => raw3027 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3027step0 raw3027; decide +kernel
      have hl : raw3027step0Labels = raw3027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3027 raw3027Labels permutation265 hz
    mixedMoment B raw3027step0 raw3027step0Labels = mixedMoment B raw3027step1 raw3027step1Labels := by
      have ha : raw3027step1 = (fun i j => raw3027step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3027step1 raw3027step0; decide +kernel
      have hl : raw3027step1Labels = raw3027step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3027step0 raw3027step0Labels permutation38 permutation3
    mixedMoment B raw3027step1 raw3027step1Labels = mixedMoment B raw3027step2 raw3027step2Labels := by
      have ha : raw3027step2 = raw3027step1 := by apply Matrix.ext; unfold raw3027step2 raw3027step1; decide +kernel
      have hl : raw3027step1Labels = labelEmbedding6 ∘ raw3027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3027step1 raw3027step1Labels raw3027step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw3028step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3028step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3028step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3028step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3028 raw3028Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw3028 raw3028Labels = mixedMoment B raw3028step0 raw3028step0Labels := by
      have hz : ∀ j, raw3028 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3028step0 = (fun i j => raw3028 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3028step0 raw3028; decide +kernel
      have hl : raw3028step0Labels = raw3028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3028 raw3028Labels permutation265 hz
    mixedMoment B raw3028step0 raw3028step0Labels = mixedMoment B raw3028step1 raw3028step1Labels := by
      have ha : raw3028step1 = (fun i j => raw3028step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3028step1 raw3028step0; decide +kernel
      have hl : raw3028step1Labels = raw3028step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3028step0 raw3028step0Labels permutation44 permutation5
    mixedMoment B raw3028step1 raw3028step1Labels = mixedMoment B raw3028step2 raw3028step2Labels := by
      have ha : raw3028step2 = -raw3028step1 := by apply Matrix.ext; change ∀ i j, raw3028step2 i j = -(raw3028step1 i j); unfold raw3028step2 raw3028step1; decide +kernel
      have hl : raw3028step2Labels = raw3028step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3028step2 raw3028step2Labels = mixedMoment B raw3028step3 raw3028step3Labels := by
      have ha : raw3028step3 = raw3028step2 := by apply Matrix.ext; unfold raw3028step3 raw3028step2; decide +kernel
      have hl : raw3028step2Labels = labelEmbedding8 ∘ raw3028step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3028step2 raw3028step2Labels raw3028step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw3029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3029step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3029step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3029step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3029step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3029 raw3029Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw3029 raw3029Labels = mixedMoment B raw3029step0 raw3029step0Labels := by
      have hz : ∀ j, raw3029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3029step0 = (fun i j => raw3029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3029step0 raw3029; decide +kernel
      have hl : raw3029step0Labels = raw3029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3029 raw3029Labels permutation434 hz
    mixedMoment B raw3029step0 raw3029step0Labels = mixedMoment B raw3029step1 raw3029step1Labels := by
      have hz : ∀ j, raw3029step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3029step1 = (fun i j => raw3029step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3029step1 raw3029step0; decide +kernel
      have hl : raw3029step1Labels = raw3029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3029step0 raw3029step0Labels permutation80 hz
    mixedMoment B raw3029step1 raw3029step1Labels = mixedMoment B raw3029step2 raw3029step2Labels := by
      have ha : raw3029step2 = (fun i j => raw3029step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3029step2 raw3029step1; decide +kernel
      have hl : raw3029step2Labels = raw3029step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3029step1 raw3029step1Labels permutation30 permutation7
    mixedMoment B raw3029step2 raw3029step2Labels = mixedMoment B raw3029step3 raw3029step3Labels := by
      have ha : raw3029step3 = raw3029step2 := by apply Matrix.ext; unfold raw3029step3 raw3029step2; decide +kernel
      have hl : raw3029step2Labels = labelEmbedding10 ∘ raw3029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3029step2 raw3029step2Labels raw3029step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw3030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3030step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3030step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3030 raw3030Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3030 raw3030Labels = mixedMoment B raw3030step0 raw3030step0Labels := by
      have hz : ∀ j, raw3030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3030step0 = (fun i j => raw3030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3030step0 raw3030; decide +kernel
      have hl : raw3030step0Labels = raw3030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3030 raw3030Labels permutation434 hz
    mixedMoment B raw3030step0 raw3030step0Labels = mixedMoment B raw3030step1 raw3030step1Labels := by
      have ha : raw3030step1 = (fun i j => raw3030step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3030step1 raw3030step0; decide +kernel
      have hl : raw3030step1Labels = raw3030step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3030step0 raw3030step0Labels permutation144 permutation6
    mixedMoment B raw3030step1 raw3030step1Labels = mixedMoment B raw3030step2 raw3030step2Labels := by
      have ha : raw3030step2 = raw3030step1 := by apply Matrix.ext; unfold raw3030step2 raw3030step1; decide +kernel
      have hl : raw3030step1Labels = labelEmbedding9 ∘ raw3030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3030step1 raw3030step1Labels raw3030step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3031step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3031 raw3031Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3031 raw3031Labels = mixedMoment B raw3031step0 raw3031step0Labels := by
      have hz : ∀ j, raw3031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3031step0 = (fun i j => raw3031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3031step0 raw3031; decide +kernel
      have hl : raw3031step0Labels = raw3031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3031 raw3031Labels permutation346 hz
    mixedMoment B raw3031step0 raw3031step0Labels = mixedMoment B raw3031step1 raw3031step1Labels := by
      have ha : raw3031step1 = (fun i j => raw3031step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3031step1 raw3031step0; decide +kernel
      have hl : raw3031step1Labels = raw3031step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3031step0 raw3031step0Labels permutation144 permutation6
    mixedMoment B raw3031step1 raw3031step1Labels = mixedMoment B raw3031step2 raw3031step2Labels := by
      have ha : raw3031step2 = raw3031step1 := by apply Matrix.ext; unfold raw3031step2 raw3031step1; decide +kernel
      have hl : raw3031step1Labels = labelEmbedding9 ∘ raw3031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3031step1 raw3031step1Labels raw3031step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2]]
def raw3032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3032step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, 1, -2]]
def raw3032step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3032step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3032step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3032step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3032step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3032 raw3032Labels = mixedMoment B node5495 node5495Labels := by
  calc
    mixedMoment B raw3032 raw3032Labels = mixedMoment B raw3032step0 raw3032step0Labels := by
      have hz : ∀ j, raw3032 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3032step0 = (fun i j => raw3032 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3032step0 raw3032; decide +kernel
      have hl : raw3032step0Labels = raw3032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3032 raw3032Labels permutation520 hz
    mixedMoment B raw3032step0 raw3032step0Labels = mixedMoment B raw3032step1 raw3032step1Labels := by
      have hz : ∀ j, raw3032step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3032step1 = (fun i j => raw3032step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3032step1 raw3032step0; decide +kernel
      have hl : raw3032step1Labels = raw3032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3032step0 raw3032step0Labels permutation104 hz
    mixedMoment B raw3032step1 raw3032step1Labels = mixedMoment B raw3032step2 raw3032step2Labels := by
      have hz : ∀ j, raw3032step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3032step2 = (fun i j => raw3032step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3032step2 raw3032step1; decide +kernel
      have hl : raw3032step2Labels = raw3032step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3032step1 raw3032step1Labels permutation20 hz
    mixedMoment B raw3032step2 raw3032step2Labels = mixedMoment B raw3032step3 raw3032step3Labels := by
      have ha : raw3032step3 = (fun i j => raw3032step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3032step3 raw3032step2; decide +kernel
      have hl : raw3032step3Labels = raw3032step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3032step2 raw3032step2Labels permutation6 permutation6
    mixedMoment B raw3032step3 raw3032step3Labels = mixedMoment B raw3032step4 raw3032step4Labels := by
      have ha : raw3032step4 = raw3032step3 := by apply Matrix.ext; unfold raw3032step4 raw3032step3; decide +kernel
      have hl : raw3032step3Labels = labelEmbedding9 ∘ raw3032step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3032step3 raw3032step3Labels raw3032step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5495 node5495Labels := by rfl

def raw3033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2]]
def raw3033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3033step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3033step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3033step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3033step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3033step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3033 raw3033Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw3033 raw3033Labels = mixedMoment B raw3033step0 raw3033step0Labels := by
      have hz : ∀ j, raw3033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3033step0 = (fun i j => raw3033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3033step0 raw3033; decide +kernel
      have hl : raw3033step0Labels = raw3033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3033 raw3033Labels permutation434 hz
    mixedMoment B raw3033step0 raw3033step0Labels = mixedMoment B raw3033step1 raw3033step1Labels := by
      have hz : ∀ j, raw3033step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3033step1 = (fun i j => raw3033step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3033step1 raw3033step0; decide +kernel
      have hl : raw3033step1Labels = raw3033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3033step0 raw3033step0Labels permutation80 hz
    mixedMoment B raw3033step1 raw3033step1Labels = mixedMoment B raw3033step2 raw3033step2Labels := by
      have ha : raw3033step2 = (fun i j => raw3033step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3033step2 raw3033step1; decide +kernel
      have hl : raw3033step2Labels = raw3033step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3033step1 raw3033step1Labels permutation27 permutation4
    mixedMoment B raw3033step2 raw3033step2Labels = mixedMoment B raw3033step3 raw3033step3Labels := by
      have ha : raw3033step3 = -raw3033step2 := by apply Matrix.ext; change ∀ i j, raw3033step3 i j = -(raw3033step2 i j); unfold raw3033step3 raw3033step2; decide +kernel
      have hl : raw3033step3Labels = raw3033step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3033step3 raw3033step3Labels = mixedMoment B raw3033step4 raw3033step4Labels := by
      have ha : raw3033step4 = raw3033step3 := by apply Matrix.ext; unfold raw3033step4 raw3033step3; decide +kernel
      have hl : raw3033step3Labels = labelEmbedding7 ∘ raw3033step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3033step3 raw3033step3Labels raw3033step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw3034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3034step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3034step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3034step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3034 raw3034Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw3034 raw3034Labels = mixedMoment B raw3034step0 raw3034step0Labels := by
      have hz : ∀ j, raw3034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3034step0 = (fun i j => raw3034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3034step0 raw3034; decide +kernel
      have hl : raw3034step0Labels = raw3034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3034 raw3034Labels permutation434 hz
    mixedMoment B raw3034step0 raw3034step0Labels = mixedMoment B raw3034step1 raw3034step1Labels := by
      have hz : ∀ j, raw3034step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3034step1 = (fun i j => raw3034step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3034step1 raw3034step0; decide +kernel
      have hl : raw3034step1Labels = raw3034step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3034step0 raw3034step0Labels permutation80 hz
    mixedMoment B raw3034step1 raw3034step1Labels = mixedMoment B raw3034step2 raw3034step2Labels := by
      have ha : raw3034step2 = (fun i j => raw3034step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3034step2 raw3034step1; decide +kernel
      have hl : raw3034step2Labels = raw3034step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3034step1 raw3034step1Labels permutation13 permutation3
    mixedMoment B raw3034step2 raw3034step2Labels = mixedMoment B raw3034step3 raw3034step3Labels := by
      have ha : raw3034step3 = raw3034step2 := by apply Matrix.ext; unfold raw3034step3 raw3034step2; decide +kernel
      have hl : raw3034step2Labels = labelEmbedding6 ∘ raw3034step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3034step2 raw3034step2Labels raw3034step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw3035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3035step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3035step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3035step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3035 raw3035Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3035 raw3035Labels = mixedMoment B raw3035step0 raw3035step0Labels := by
      have hz : ∀ j, raw3035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3035step0 = (fun i j => raw3035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3035step0 raw3035; decide +kernel
      have hl : raw3035step0Labels = raw3035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3035 raw3035Labels permutation434 hz
    mixedMoment B raw3035step0 raw3035step0Labels = mixedMoment B raw3035step1 raw3035step1Labels := by
      have ha : raw3035step1 = (fun i j => raw3035step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3035step1 raw3035step0; decide +kernel
      have hl : raw3035step1Labels = raw3035step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3035step0 raw3035step0Labels permutation43 permutation3
    mixedMoment B raw3035step1 raw3035step1Labels = mixedMoment B raw3035step2 raw3035step2Labels := by
      have ha : raw3035step2 = raw3035step1 := by apply Matrix.ext; unfold raw3035step2 raw3035step1; decide +kernel
      have hl : raw3035step1Labels = labelEmbedding6 ∘ raw3035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3035step1 raw3035step1Labels raw3035step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw3036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3036step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3036 raw3036Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3036 raw3036Labels = mixedMoment B raw3036step0 raw3036step0Labels := by
      have hz : ∀ j, raw3036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3036step0 = (fun i j => raw3036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3036step0 raw3036; decide +kernel
      have hl : raw3036step0Labels = raw3036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3036 raw3036Labels permutation346 hz
    mixedMoment B raw3036step0 raw3036step0Labels = mixedMoment B raw3036step1 raw3036step1Labels := by
      have ha : raw3036step1 = (fun i j => raw3036step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3036step1 raw3036step0; decide +kernel
      have hl : raw3036step1Labels = raw3036step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3036step0 raw3036step0Labels permutation43 permutation3
    mixedMoment B raw3036step1 raw3036step1Labels = mixedMoment B raw3036step2 raw3036step2Labels := by
      have ha : raw3036step2 = raw3036step1 := by apply Matrix.ext; unfold raw3036step2 raw3036step1; decide +kernel
      have hl : raw3036step1Labels = labelEmbedding6 ∘ raw3036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3036step1 raw3036step1Labels raw3036step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw3037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw3037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3037step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw3037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3037 raw3037Labels = mixedMoment B node5494 node5494Labels := by
  calc
    mixedMoment B raw3037 raw3037Labels = mixedMoment B raw3037step0 raw3037step0Labels := by
      have hz : ∀ j, raw3037 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3037step0 = (fun i j => raw3037 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3037step0 raw3037; decide +kernel
      have hl : raw3037step0Labels = raw3037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3037 raw3037Labels permutation520 hz
    mixedMoment B raw3037step0 raw3037step0Labels = mixedMoment B raw3037step1 raw3037step1Labels := by
      have hz : ∀ j, raw3037step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3037step1 = (fun i j => raw3037step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3037step1 raw3037step0; decide +kernel
      have hl : raw3037step1Labels = raw3037step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3037step0 raw3037step0Labels permutation104 hz
    mixedMoment B raw3037step1 raw3037step1Labels = mixedMoment B raw3037step2 raw3037step2Labels := by
      have hz : ∀ j, raw3037step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3037step2 = (fun i j => raw3037step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3037step2 raw3037step1; decide +kernel
      have hl : raw3037step2Labels = raw3037step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3037step1 raw3037step1Labels permutation20 hz
    _ = mixedMoment B node5494 node5494Labels := by rfl

def raw3038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw3038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3038step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3038step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3038step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3038step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3038 raw3038Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw3038 raw3038Labels = mixedMoment B raw3038step0 raw3038step0Labels := by
      have hz : ∀ j, raw3038 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3038step0 = (fun i j => raw3038 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3038step0 raw3038; decide +kernel
      have hl : raw3038step0Labels = raw3038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3038 raw3038Labels permutation434 hz
    mixedMoment B raw3038step0 raw3038step0Labels = mixedMoment B raw3038step1 raw3038step1Labels := by
      have hz : ∀ j, raw3038step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3038step1 = (fun i j => raw3038step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3038step1 raw3038step0; decide +kernel
      have hl : raw3038step1Labels = raw3038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3038step0 raw3038step0Labels permutation80 hz
    mixedMoment B raw3038step1 raw3038step1Labels = mixedMoment B raw3038step2 raw3038step2Labels := by
      have ha : raw3038step2 = (fun i j => raw3038step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3038step2 raw3038step1; decide +kernel
      have hl : raw3038step2Labels = raw3038step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3038step1 raw3038step1Labels permutation27 permutation4
    mixedMoment B raw3038step2 raw3038step2Labels = mixedMoment B raw3038step3 raw3038step3Labels := by
      have ha : raw3038step3 = -raw3038step2 := by apply Matrix.ext; change ∀ i j, raw3038step3 i j = -(raw3038step2 i j); unfold raw3038step3 raw3038step2; decide +kernel
      have hl : raw3038step3Labels = raw3038step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3038step3 raw3038step3Labels = mixedMoment B raw3038step4 raw3038step4Labels := by
      have ha : raw3038step4 = raw3038step3 := by apply Matrix.ext; unfold raw3038step4 raw3038step3; decide +kernel
      have hl : raw3038step3Labels = labelEmbedding7 ∘ raw3038step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3038step3 raw3038step3Labels raw3038step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw3039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3039step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3039 raw3039Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw3039 raw3039Labels = mixedMoment B raw3039step0 raw3039step0Labels := by
      have hz : ∀ j, raw3039 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3039step0 = (fun i j => raw3039 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3039step0 raw3039; decide +kernel
      have hl : raw3039step0Labels = raw3039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3039 raw3039Labels permutation434 hz
    mixedMoment B raw3039step0 raw3039step0Labels = mixedMoment B raw3039step1 raw3039step1Labels := by
      have ha : raw3039step1 = (fun i j => raw3039step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3039step1 raw3039step0; decide +kernel
      have hl : raw3039step1Labels = raw3039step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3039step0 raw3039step0Labels permutation36 permutation3
    mixedMoment B raw3039step1 raw3039step1Labels = mixedMoment B raw3039step2 raw3039step2Labels := by
      have ha : raw3039step2 = raw3039step1 := by apply Matrix.ext; unfold raw3039step2 raw3039step1; decide +kernel
      have hl : raw3039step1Labels = labelEmbedding6 ∘ raw3039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3039step1 raw3039step1Labels raw3039step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw3040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3040 raw3040Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3040 raw3040Labels = mixedMoment B raw3040step0 raw3040step0Labels := by
      have hz : ∀ j, raw3040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3040step0 = (fun i j => raw3040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3040step0 raw3040; decide +kernel
      have hl : raw3040step0Labels = raw3040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3040 raw3040Labels permutation434 hz
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3041step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3041step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3041 raw3041Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw3041 raw3041Labels = mixedMoment B raw3041step0 raw3041step0Labels := by
      have ha : raw3041step0 = (fun i j => raw3041 (permutation204 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3041step0 raw3041; decide +kernel
      have hl : raw3041step0Labels = raw3041Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3041 raw3041Labels permutation204 permutation3
    mixedMoment B raw3041step0 raw3041step0Labels = mixedMoment B raw3041step1 raw3041step1Labels := by
      have ha : raw3041step1 = raw3041step0 := by apply Matrix.ext; unfold raw3041step1 raw3041step0; decide +kernel
      have hl : raw3041step0Labels = labelEmbedding6 ∘ raw3041step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3041step0 raw3041step0Labels raw3041step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw3042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3042step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3042 raw3042Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3042 raw3042Labels = mixedMoment B raw3042step0 raw3042step0Labels := by
      have hz : ∀ j, raw3042 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3042step0 = (fun i j => raw3042 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3042step0 raw3042; decide +kernel
      have hl : raw3042step0Labels = raw3042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3042 raw3042Labels permutation520 hz
    mixedMoment B raw3042step0 raw3042step0Labels = mixedMoment B raw3042step1 raw3042step1Labels := by
      have hz : ∀ j, raw3042step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3042step1 = (fun i j => raw3042step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3042step1 raw3042step0; decide +kernel
      have hl : raw3042step1Labels = raw3042step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3042step0 raw3042step0Labels permutation104 hz
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3043step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3043step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3043step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3043step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3043 raw3043Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw3043 raw3043Labels = mixedMoment B raw3043step0 raw3043step0Labels := by
      have hz : ∀ j, raw3043 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3043step0 = (fun i j => raw3043 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3043step0 raw3043; decide +kernel
      have hl : raw3043step0Labels = raw3043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3043 raw3043Labels permutation434 hz
    mixedMoment B raw3043step0 raw3043step0Labels = mixedMoment B raw3043step1 raw3043step1Labels := by
      have ha : raw3043step1 = (fun i j => raw3043step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3043step1 raw3043step0; decide +kernel
      have hl : raw3043step1Labels = raw3043step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3043step0 raw3043step0Labels permutation131 permutation4
    mixedMoment B raw3043step1 raw3043step1Labels = mixedMoment B raw3043step2 raw3043step2Labels := by
      have ha : raw3043step2 = -raw3043step1 := by apply Matrix.ext; change ∀ i j, raw3043step2 i j = -(raw3043step1 i j); unfold raw3043step2 raw3043step1; decide +kernel
      have hl : raw3043step2Labels = raw3043step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3043step2 raw3043step2Labels = mixedMoment B raw3043step3 raw3043step3Labels := by
      have ha : raw3043step3 = raw3043step2 := by apply Matrix.ext; unfold raw3043step3 raw3043step2; decide +kernel
      have hl : raw3043step2Labels = labelEmbedding7 ∘ raw3043step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3043step2 raw3043step2Labels raw3043step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw3044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3044step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3044 raw3044Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw3044 raw3044Labels = mixedMoment B raw3044step0 raw3044step0Labels := by
      have hz : ∀ j, raw3044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3044step0 = (fun i j => raw3044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3044step0 raw3044; decide +kernel
      have hl : raw3044step0Labels = raw3044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3044 raw3044Labels permutation346 hz
    mixedMoment B raw3044step0 raw3044step0Labels = mixedMoment B raw3044step1 raw3044step1Labels := by
      have ha : raw3044step1 = (fun i j => raw3044step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3044step1 raw3044step0; decide +kernel
      have hl : raw3044step1Labels = raw3044step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3044step0 raw3044step0Labels permutation36 permutation3
    mixedMoment B raw3044step1 raw3044step1Labels = mixedMoment B raw3044step2 raw3044step2Labels := by
      have ha : raw3044step2 = raw3044step1 := by apply Matrix.ext; unfold raw3044step2 raw3044step1; decide +kernel
      have hl : raw3044step1Labels = labelEmbedding6 ∘ raw3044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3044step1 raw3044step1Labels raw3044step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw3045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3045 raw3045Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3045 raw3045Labels = mixedMoment B raw3045step0 raw3045step0Labels := by
      have hz : ∀ j, raw3045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3045step0 = (fun i j => raw3045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3045step0 raw3045; decide +kernel
      have hl : raw3045step0Labels = raw3045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3045 raw3045Labels permutation346 hz
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3046step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3046 raw3046Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw3046 raw3046Labels = mixedMoment B raw3046step0 raw3046step0Labels := by
      have ha : raw3046step0 = (fun i j => raw3046 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3046step0 raw3046; decide +kernel
      have hl : raw3046step0Labels = raw3046Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3046 raw3046Labels permutation180 permutation3
    mixedMoment B raw3046step0 raw3046step0Labels = mixedMoment B raw3046step1 raw3046step1Labels := by
      have ha : raw3046step1 = raw3046step0 := by apply Matrix.ext; unfold raw3046step1 raw3046step0; decide +kernel
      have hl : raw3046step0Labels = labelEmbedding6 ∘ raw3046step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3046step0 raw3046step0Labels raw3046step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw3047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3047 raw3047Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3047 raw3047Labels = mixedMoment B raw3047step0 raw3047step0Labels := by
      have hz : ∀ j, raw3047 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3047step0 = (fun i j => raw3047 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3047step0 raw3047; decide +kernel
      have hl : raw3047step0Labels = raw3047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3047 raw3047Labels permutation520 hz
    mixedMoment B raw3047step0 raw3047step0Labels = mixedMoment B raw3047step1 raw3047step1Labels := by
      have hz : ∀ j, raw3047step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3047step1 = (fun i j => raw3047step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3047step1 raw3047step0; decide +kernel
      have hl : raw3047step1Labels = raw3047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3047step0 raw3047step0Labels permutation80 hz
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3048step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3048step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3048step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3048step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3048 raw3048Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw3048 raw3048Labels = mixedMoment B raw3048step0 raw3048step0Labels := by
      have hz : ∀ j, raw3048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3048step0 = (fun i j => raw3048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3048step0 raw3048; decide +kernel
      have hl : raw3048step0Labels = raw3048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3048 raw3048Labels permutation346 hz
    mixedMoment B raw3048step0 raw3048step0Labels = mixedMoment B raw3048step1 raw3048step1Labels := by
      have ha : raw3048step1 = (fun i j => raw3048step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3048step1 raw3048step0; decide +kernel
      have hl : raw3048step1Labels = raw3048step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3048step0 raw3048step0Labels permutation131 permutation4
    mixedMoment B raw3048step1 raw3048step1Labels = mixedMoment B raw3048step2 raw3048step2Labels := by
      have ha : raw3048step2 = -raw3048step1 := by apply Matrix.ext; change ∀ i j, raw3048step2 i j = -(raw3048step1 i j); unfold raw3048step2 raw3048step1; decide +kernel
      have hl : raw3048step2Labels = raw3048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3048step2 raw3048step2Labels = mixedMoment B raw3048step3 raw3048step3Labels := by
      have ha : raw3048step3 = raw3048step2 := by apply Matrix.ext; unfold raw3048step3 raw3048step2; decide +kernel
      have hl : raw3048step2Labels = labelEmbedding7 ∘ raw3048step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3048step2 raw3048step2Labels raw3048step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw3049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw3049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw3049step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3049step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw3049step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3049 raw3049Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw3049 raw3049Labels = mixedMoment B raw3049step0 raw3049step0Labels := by
      have hz : ∀ j, raw3049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3049step0 = (fun i j => raw3049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3049step0 raw3049; decide +kernel
      have hl : raw3049step0Labels = raw3049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3049 raw3049Labels permutation434 hz
    mixedMoment B raw3049step0 raw3049step0Labels = mixedMoment B raw3049step1 raw3049step1Labels := by
      have hz : ∀ j, raw3049step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3049step1 = (fun i j => raw3049step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3049step1 raw3049step0; decide +kernel
      have hl : raw3049step1Labels = raw3049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3049step0 raw3049step0Labels permutation80 hz
    mixedMoment B raw3049step1 raw3049step1Labels = mixedMoment B raw3049step2 raw3049step2Labels := by
      have ha : raw3049step2 = (fun i j => raw3049step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3049step2 raw3049step1; decide +kernel
      have hl : raw3049step2Labels = raw3049step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3049step1 raw3049step1Labels permutation9 permutation3
    mixedMoment B raw3049step2 raw3049step2Labels = mixedMoment B raw3049step3 raw3049step3Labels := by
      have ha : raw3049step3 = raw3049step2 := by apply Matrix.ext; unfold raw3049step3 raw3049step2; decide +kernel
      have hl : raw3049step2Labels = labelEmbedding6 ∘ raw3049step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3049step2 raw3049step2Labels raw3049step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw3050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2]]
def raw3050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3050step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3050step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3050step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3050step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3050step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3050step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3050 raw3050Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw3050 raw3050Labels = mixedMoment B raw3050step0 raw3050step0Labels := by
      have hz : ∀ j, raw3050 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3050step0 = (fun i j => raw3050 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3050step0 raw3050; decide +kernel
      have hl : raw3050step0Labels = raw3050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3050 raw3050Labels permutation434 hz
    mixedMoment B raw3050step0 raw3050step0Labels = mixedMoment B raw3050step1 raw3050step1Labels := by
      have hz : ∀ j, raw3050step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3050step1 = (fun i j => raw3050step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3050step1 raw3050step0; decide +kernel
      have hl : raw3050step1Labels = raw3050step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3050step0 raw3050step0Labels permutation80 hz
    mixedMoment B raw3050step1 raw3050step1Labels = mixedMoment B raw3050step2 raw3050step2Labels := by
      have ha : raw3050step2 = (fun i j => raw3050step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3050step2 raw3050step1; decide +kernel
      have hl : raw3050step2Labels = raw3050step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3050step1 raw3050step1Labels permutation25 permutation3
    mixedMoment B raw3050step2 raw3050step2Labels = mixedMoment B raw3050step3 raw3050step3Labels := by
      have ha : raw3050step3 = -raw3050step2 := by apply Matrix.ext; change ∀ i j, raw3050step3 i j = -(raw3050step2 i j); unfold raw3050step3 raw3050step2; decide +kernel
      have hl : raw3050step3Labels = raw3050step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3050step3 raw3050step3Labels = mixedMoment B raw3050step4 raw3050step4Labels := by
      have ha : raw3050step4 = raw3050step3 := by apply Matrix.ext; unfold raw3050step4 raw3050step3; decide +kernel
      have hl : raw3050step3Labels = labelEmbedding6 ∘ raw3050step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3050step3 raw3050step3Labels raw3050step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw3051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3051step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3051step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3051 raw3051Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw3051 raw3051Labels = mixedMoment B raw3051step0 raw3051step0Labels := by
      have hz : ∀ j, raw3051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3051step0 = (fun i j => raw3051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3051step0 raw3051; decide +kernel
      have hl : raw3051step0Labels = raw3051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3051 raw3051Labels permutation434 hz
    mixedMoment B raw3051step0 raw3051step0Labels = mixedMoment B raw3051step1 raw3051step1Labels := by
      have ha : raw3051step1 = (fun i j => raw3051step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3051step1 raw3051step0; decide +kernel
      have hl : raw3051step1Labels = raw3051step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3051step0 raw3051step0Labels permutation115 permutation5
    mixedMoment B raw3051step1 raw3051step1Labels = mixedMoment B raw3051step2 raw3051step2Labels := by
      have ha : raw3051step2 = raw3051step1 := by apply Matrix.ext; unfold raw3051step2 raw3051step1; decide +kernel
      have hl : raw3051step1Labels = labelEmbedding8 ∘ raw3051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3051step1 raw3051step1Labels raw3051step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw3052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw3052step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3052step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3052 raw3052Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw3052 raw3052Labels = mixedMoment B raw3052step0 raw3052step0Labels := by
      have hz : ∀ j, raw3052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3052step0 = (fun i j => raw3052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3052step0 raw3052; decide +kernel
      have hl : raw3052step0Labels = raw3052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3052 raw3052Labels permutation346 hz
    mixedMoment B raw3052step0 raw3052step0Labels = mixedMoment B raw3052step1 raw3052step1Labels := by
      have ha : raw3052step1 = (fun i j => raw3052step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3052step1 raw3052step0; decide +kernel
      have hl : raw3052step1Labels = raw3052step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3052step0 raw3052step0Labels permutation115 permutation5
    mixedMoment B raw3052step1 raw3052step1Labels = mixedMoment B raw3052step2 raw3052step2Labels := by
      have ha : raw3052step2 = raw3052step1 := by apply Matrix.ext; unfold raw3052step2 raw3052step1; decide +kernel
      have hl : raw3052step1Labels = labelEmbedding8 ∘ raw3052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3052step1 raw3052step1Labels raw3052step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw3053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2]]
def raw3053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2]]
def raw3053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![0, 2, -2]]
def raw3053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3053step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3053step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3053 raw3053Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw3053 raw3053Labels = mixedMoment B raw3053step0 raw3053step0Labels := by
      have hz : ∀ j, raw3053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3053step0 = (fun i j => raw3053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3053step0 raw3053; decide +kernel
      have hl : raw3053step0Labels = raw3053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3053 raw3053Labels permutation434 hz
    mixedMoment B raw3053step0 raw3053step0Labels = mixedMoment B raw3053step1 raw3053step1Labels := by
      have hz : ∀ j, raw3053step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3053step1 = (fun i j => raw3053step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3053step1 raw3053step0; decide +kernel
      have hl : raw3053step1Labels = raw3053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3053step0 raw3053step0Labels permutation80 hz
    mixedMoment B raw3053step1 raw3053step1Labels = mixedMoment B raw3053step2 raw3053step2Labels := by
      have ha : raw3053step2 = (fun i j => raw3053step1 (permutation22 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3053step2 raw3053step1; decide +kernel
      have hl : raw3053step2Labels = raw3053step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3053step1 raw3053step1Labels permutation22 permutation5
    mixedMoment B raw3053step2 raw3053step2Labels = mixedMoment B raw3053step3 raw3053step3Labels := by
      have ha : raw3053step3 = raw3053step2 := by apply Matrix.ext; unfold raw3053step3 raw3053step2; decide +kernel
      have hl : raw3053step2Labels = labelEmbedding8 ∘ raw3053step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3053step2 raw3053step2Labels raw3053step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw3054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw3054step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3054step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3054step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3054step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3054step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3054 raw3054Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw3054 raw3054Labels = mixedMoment B raw3054step0 raw3054step0Labels := by
      have hz : ∀ j, raw3054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3054step0 = (fun i j => raw3054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3054step0 raw3054; decide +kernel
      have hl : raw3054step0Labels = raw3054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3054 raw3054Labels permutation434 hz
    mixedMoment B raw3054step0 raw3054step0Labels = mixedMoment B raw3054step1 raw3054step1Labels := by
      have hz : ∀ j, raw3054step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3054step1 = (fun i j => raw3054step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3054step1 raw3054step0; decide +kernel
      have hl : raw3054step1Labels = raw3054step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3054step0 raw3054step0Labels permutation80 hz
    mixedMoment B raw3054step1 raw3054step1Labels = mixedMoment B raw3054step2 raw3054step2Labels := by
      have ha : raw3054step2 = (fun i j => raw3054step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3054step2 raw3054step1; decide +kernel
      have hl : raw3054step2Labels = raw3054step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3054step1 raw3054step1Labels permutation8 permutation3
    mixedMoment B raw3054step2 raw3054step2Labels = mixedMoment B raw3054step3 raw3054step3Labels := by
      have ha : raw3054step3 = raw3054step2 := by apply Matrix.ext; unfold raw3054step3 raw3054step2; decide +kernel
      have hl : raw3054step2Labels = labelEmbedding6 ∘ raw3054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3054step2 raw3054step2Labels raw3054step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw3055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3055step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw3055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3055step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw3055step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3055step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw3055step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3055 raw3055Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw3055 raw3055Labels = mixedMoment B raw3055step0 raw3055step0Labels := by
      have hz : ∀ j, raw3055 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3055step0 = (fun i j => raw3055 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3055step0 raw3055; decide +kernel
      have hl : raw3055step0Labels = raw3055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3055 raw3055Labels permutation434 hz
    mixedMoment B raw3055step0 raw3055step0Labels = mixedMoment B raw3055step1 raw3055step1Labels := by
      have hz : ∀ j, raw3055step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3055step1 = (fun i j => raw3055step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3055step1 raw3055step0; decide +kernel
      have hl : raw3055step1Labels = raw3055step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3055step0 raw3055step0Labels permutation80 hz
    mixedMoment B raw3055step1 raw3055step1Labels = mixedMoment B raw3055step2 raw3055step2Labels := by
      have ha : raw3055step2 = (fun i j => raw3055step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3055step2 raw3055step1; decide +kernel
      have hl : raw3055step2Labels = raw3055step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3055step1 raw3055step1Labels permutation31 permutation2
    mixedMoment B raw3055step2 raw3055step2Labels = mixedMoment B raw3055step3 raw3055step3Labels := by
      have ha : raw3055step3 = -raw3055step2 := by apply Matrix.ext; change ∀ i j, raw3055step3 i j = -(raw3055step2 i j); unfold raw3055step3 raw3055step2; decide +kernel
      have hl : raw3055step3Labels = raw3055step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw3056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3056step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3056step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3056 raw3056Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3056 raw3056Labels = mixedMoment B raw3056step0 raw3056step0Labels := by
      have hz : ∀ j, raw3056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3056step0 = (fun i j => raw3056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3056step0 raw3056; decide +kernel
      have hl : raw3056step0Labels = raw3056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3056 raw3056Labels permutation434 hz
    mixedMoment B raw3056step0 raw3056step0Labels = mixedMoment B raw3056step1 raw3056step1Labels := by
      have ha : raw3056step1 = (fun i j => raw3056step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3056step1 raw3056step0; decide +kernel
      have hl : raw3056step1Labels = raw3056step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3056step0 raw3056step0Labels permutation149 permutation2
    mixedMoment B raw3056step1 raw3056step1Labels = mixedMoment B raw3056step2 raw3056step2Labels := by
      have ha : raw3056step2 = -raw3056step1 := by apply Matrix.ext; change ∀ i j, raw3056step2 i j = -(raw3056step1 i j); unfold raw3056step2 raw3056step1; decide +kernel
      have hl : raw3056step2Labels = raw3056step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw3057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3057step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3057step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3057 raw3057Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3057 raw3057Labels = mixedMoment B raw3057step0 raw3057step0Labels := by
      have hz : ∀ j, raw3057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3057step0 = (fun i j => raw3057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3057step0 raw3057; decide +kernel
      have hl : raw3057step0Labels = raw3057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3057 raw3057Labels permutation346 hz
    mixedMoment B raw3057step0 raw3057step0Labels = mixedMoment B raw3057step1 raw3057step1Labels := by
      have ha : raw3057step1 = (fun i j => raw3057step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3057step1 raw3057step0; decide +kernel
      have hl : raw3057step1Labels = raw3057step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3057step0 raw3057step0Labels permutation149 permutation2
    mixedMoment B raw3057step1 raw3057step1Labels = mixedMoment B raw3057step2 raw3057step2Labels := by
      have ha : raw3057step2 = -raw3057step1 := by apply Matrix.ext; change ∀ i j, raw3057step2 i j = -(raw3057step1 i j); unfold raw3057step2 raw3057step1; decide +kernel
      have hl : raw3057step2Labels = raw3057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw3058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw3058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw3058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3058step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw3058step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3058step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw3058step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3058step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw3058step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3058 raw3058Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw3058 raw3058Labels = mixedMoment B raw3058step0 raw3058step0Labels := by
      have hz : ∀ j, raw3058 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3058step0 = (fun i j => raw3058 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3058step0 raw3058; decide +kernel
      have hl : raw3058step0Labels = raw3058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3058 raw3058Labels permutation520 hz
    mixedMoment B raw3058step0 raw3058step0Labels = mixedMoment B raw3058step1 raw3058step1Labels := by
      have hz : ∀ j, raw3058step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3058step1 = (fun i j => raw3058step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3058step1 raw3058step0; decide +kernel
      have hl : raw3058step1Labels = raw3058step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3058step0 raw3058step0Labels permutation104 hz
    mixedMoment B raw3058step1 raw3058step1Labels = mixedMoment B raw3058step2 raw3058step2Labels := by
      have hz : ∀ j, raw3058step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3058step2 = (fun i j => raw3058step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3058step2 raw3058step1; decide +kernel
      have hl : raw3058step2Labels = raw3058step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3058step1 raw3058step1Labels permutation20 hz
    mixedMoment B raw3058step2 raw3058step2Labels = mixedMoment B raw3058step3 raw3058step3Labels := by
      have ha : raw3058step3 = (fun i j => raw3058step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3058step3 raw3058step2; decide +kernel
      have hl : raw3058step3Labels = raw3058step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3058step2 raw3058step2Labels permutation7 permutation2
    mixedMoment B raw3058step3 raw3058step3Labels = mixedMoment B raw3058step4 raw3058step4Labels := by
      have ha : raw3058step4 = -raw3058step3 := by apply Matrix.ext; change ∀ i j, raw3058step4 i j = -(raw3058step3 i j); unfold raw3058step4 raw3058step3; decide +kernel
      have hl : raw3058step4Labels = raw3058step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw3059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3059step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3059step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3059step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3059 raw3059Labels = mixedMoment B node4018 node4018Labels := by
  calc
    mixedMoment B raw3059 raw3059Labels = mixedMoment B raw3059step0 raw3059step0Labels := by
      have hz : ∀ j, raw3059 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3059step0 = (fun i j => raw3059 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3059step0 raw3059; decide +kernel
      have hl : raw3059step0Labels = raw3059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3059 raw3059Labels permutation434 hz
    mixedMoment B raw3059step0 raw3059step0Labels = mixedMoment B raw3059step1 raw3059step1Labels := by
      have hz : ∀ j, raw3059step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3059step1 = (fun i j => raw3059step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3059step1 raw3059step0; decide +kernel
      have hl : raw3059step1Labels = raw3059step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3059step0 raw3059step0Labels permutation80 hz
    mixedMoment B raw3059step1 raw3059step1Labels = mixedMoment B raw3059step2 raw3059step2Labels := by
      have ha : raw3059step2 = (fun i j => raw3059step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3059step2 raw3059step1; decide +kernel
      have hl : raw3059step2Labels = raw3059step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3059step1 raw3059step1Labels permutation30 permutation6
    _ = mixedMoment B node4018 node4018Labels := by rfl

def raw3060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3060 raw3060Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw3060 raw3060Labels = mixedMoment B raw3060step0 raw3060step0Labels := by
      have hz : ∀ j, raw3060 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3060step0 = (fun i j => raw3060 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3060step0 raw3060; decide +kernel
      have hl : raw3060step0Labels = raw3060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3060 raw3060Labels permutation434 hz
    mixedMoment B raw3060step0 raw3060step0Labels = mixedMoment B raw3060step1 raw3060step1Labels := by
      have ha : raw3060step1 = (fun i j => raw3060step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3060step1 raw3060step0; decide +kernel
      have hl : raw3060step1Labels = raw3060step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3060step0 raw3060step0Labels permutation144 permutation6
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw3061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3061 raw3061Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw3061 raw3061Labels = mixedMoment B raw3061step0 raw3061step0Labels := by
      have hz : ∀ j, raw3061 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3061step0 = (fun i j => raw3061 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3061step0 raw3061; decide +kernel
      have hl : raw3061step0Labels = raw3061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3061 raw3061Labels permutation346 hz
    mixedMoment B raw3061step0 raw3061step0Labels = mixedMoment B raw3061step1 raw3061step1Labels := by
      have ha : raw3061step1 = (fun i j => raw3061step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3061step1 raw3061step0; decide +kernel
      have hl : raw3061step1Labels = raw3061step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3061step0 raw3061step0Labels permutation144 permutation6
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw3062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3062step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3062step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2]]
def raw3062step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3062step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, 1, -2]]
def raw3062step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3062step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3062step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3062 raw3062Labels = mixedMoment B node4021 node4021Labels := by
  calc
    mixedMoment B raw3062 raw3062Labels = mixedMoment B raw3062step0 raw3062step0Labels := by
      have hz : ∀ j, raw3062 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3062step0 = (fun i j => raw3062 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3062step0 raw3062; decide +kernel
      have hl : raw3062step0Labels = raw3062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3062 raw3062Labels permutation520 hz
    mixedMoment B raw3062step0 raw3062step0Labels = mixedMoment B raw3062step1 raw3062step1Labels := by
      have hz : ∀ j, raw3062step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3062step1 = (fun i j => raw3062step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3062step1 raw3062step0; decide +kernel
      have hl : raw3062step1Labels = raw3062step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3062step0 raw3062step0Labels permutation104 hz
    mixedMoment B raw3062step1 raw3062step1Labels = mixedMoment B raw3062step2 raw3062step2Labels := by
      have hz : ∀ j, raw3062step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3062step2 = (fun i j => raw3062step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3062step2 raw3062step1; decide +kernel
      have hl : raw3062step2Labels = raw3062step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3062step1 raw3062step1Labels permutation20 hz
    mixedMoment B raw3062step2 raw3062step2Labels = mixedMoment B raw3062step3 raw3062step3Labels := by
      have ha : raw3062step3 = (fun i j => raw3062step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3062step3 raw3062step2; decide +kernel
      have hl : raw3062step3Labels = raw3062step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3062step2 raw3062step2Labels permutation6 permutation6
    _ = mixedMoment B node4021 node4021Labels := by rfl

def raw3063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2]]
def raw3063step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3063 raw3063Labels = mixedMoment B node3914 node3914Labels := by
  calc
    mixedMoment B raw3063 raw3063Labels = mixedMoment B raw3063step0 raw3063step0Labels := by
      have hz : ∀ j, raw3063 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3063step0 = (fun i j => raw3063 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3063step0 raw3063; decide +kernel
      have hl : raw3063step0Labels = raw3063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3063 raw3063Labels permutation434 hz
    mixedMoment B raw3063step0 raw3063step0Labels = mixedMoment B raw3063step1 raw3063step1Labels := by
      have hz : ∀ j, raw3063step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3063step1 = (fun i j => raw3063step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3063step1 raw3063step0; decide +kernel
      have hl : raw3063step1Labels = raw3063step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3063step0 raw3063step0Labels permutation80 hz
    mixedMoment B raw3063step1 raw3063step1Labels = mixedMoment B raw3063step2 raw3063step2Labels := by
      have ha : raw3063step2 = (fun i j => raw3063step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3063step2 raw3063step1; decide +kernel
      have hl : raw3063step2Labels = raw3063step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3063step1 raw3063step1Labels permutation30 permutation6
    _ = mixedMoment B node3914 node3914Labels := by rfl

def raw3064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3064step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3064step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3064 raw3064Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw3064 raw3064Labels = mixedMoment B raw3064step0 raw3064step0Labels := by
      have hz : ∀ j, raw3064 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3064step0 = (fun i j => raw3064 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3064step0 raw3064; decide +kernel
      have hl : raw3064step0Labels = raw3064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3064 raw3064Labels permutation434 hz
    mixedMoment B raw3064step0 raw3064step0Labels = mixedMoment B raw3064step1 raw3064step1Labels := by
      have hz : ∀ j, raw3064step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3064step1 = (fun i j => raw3064step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3064step1 raw3064step0; decide +kernel
      have hl : raw3064step1Labels = raw3064step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3064step0 raw3064step0Labels permutation80 hz
    mixedMoment B raw3064step1 raw3064step1Labels = mixedMoment B raw3064step2 raw3064step2Labels := by
      have ha : raw3064step2 = (fun i j => raw3064step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3064step2 raw3064step1; decide +kernel
      have hl : raw3064step2Labels = raw3064step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3064step1 raw3064step1Labels permutation13 permutation3
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw3065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3065 raw3065Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw3065 raw3065Labels = mixedMoment B raw3065step0 raw3065step0Labels := by
      have hz : ∀ j, raw3065 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3065step0 = (fun i j => raw3065 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3065step0 raw3065; decide +kernel
      have hl : raw3065step0Labels = raw3065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3065 raw3065Labels permutation434 hz
    mixedMoment B raw3065step0 raw3065step0Labels = mixedMoment B raw3065step1 raw3065step1Labels := by
      have ha : raw3065step1 = (fun i j => raw3065step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3065step1 raw3065step0; decide +kernel
      have hl : raw3065step1Labels = raw3065step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3065step0 raw3065step0Labels permutation43 permutation3
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw3066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3066 raw3066Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw3066 raw3066Labels = mixedMoment B raw3066step0 raw3066step0Labels := by
      have hz : ∀ j, raw3066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3066step0 = (fun i j => raw3066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3066step0 raw3066; decide +kernel
      have hl : raw3066step0Labels = raw3066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3066 raw3066Labels permutation346 hz
    mixedMoment B raw3066step0 raw3066step0Labels = mixedMoment B raw3066step1 raw3066step1Labels := by
      have ha : raw3066step1 = (fun i j => raw3066step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3066step1 raw3066step0; decide +kernel
      have hl : raw3066step1Labels = raw3066step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3066step0 raw3066step0Labels permutation43 permutation3
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw3067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2]]
def raw3067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw3067step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3067step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw3067step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3067step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw3067step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3067 raw3067Labels = mixedMoment B node4020 node4020Labels := by
  calc
    mixedMoment B raw3067 raw3067Labels = mixedMoment B raw3067step0 raw3067step0Labels := by
      have hz : ∀ j, raw3067 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3067step0 = (fun i j => raw3067 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3067step0 raw3067; decide +kernel
      have hl : raw3067step0Labels = raw3067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3067 raw3067Labels permutation520 hz
    mixedMoment B raw3067step0 raw3067step0Labels = mixedMoment B raw3067step1 raw3067step1Labels := by
      have hz : ∀ j, raw3067step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3067step1 = (fun i j => raw3067step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3067step1 raw3067step0; decide +kernel
      have hl : raw3067step1Labels = raw3067step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3067step0 raw3067step0Labels permutation104 hz
    mixedMoment B raw3067step1 raw3067step1Labels = mixedMoment B raw3067step2 raw3067step2Labels := by
      have hz : ∀ j, raw3067step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3067step2 = (fun i j => raw3067step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3067step2 raw3067step1; decide +kernel
      have hl : raw3067step2Labels = raw3067step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3067step1 raw3067step1Labels permutation20 hz
    mixedMoment B raw3067step2 raw3067step2Labels = mixedMoment B raw3067step3 raw3067step3Labels := by
      have ha : raw3067step3 = (fun i j => raw3067step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3067step3 raw3067step2; decide +kernel
      have hl : raw3067step3Labels = raw3067step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3067step2 raw3067step2Labels permutation3 permutation3
    _ = mixedMoment B node4020 node4020Labels := by rfl

def raw3068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2]]
def raw3068step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw3068step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw3068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3068 raw3068Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw3068 raw3068Labels = mixedMoment B raw3068step0 raw3068step0Labels := by
      have hz : ∀ j, raw3068 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3068step0 = (fun i j => raw3068 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3068step0 raw3068; decide +kernel
      have hl : raw3068step0Labels = raw3068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3068 raw3068Labels permutation434 hz
    mixedMoment B raw3068step0 raw3068step0Labels = mixedMoment B raw3068step1 raw3068step1Labels := by
      have hz : ∀ j, raw3068step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3068step1 = (fun i j => raw3068step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3068step1 raw3068step0; decide +kernel
      have hl : raw3068step1Labels = raw3068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3068step0 raw3068step0Labels permutation80 hz
    mixedMoment B raw3068step1 raw3068step1Labels = mixedMoment B raw3068step2 raw3068step2Labels := by
      have ha : raw3068step2 = (fun i j => raw3068step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3068step2 raw3068step1; decide +kernel
      have hl : raw3068step2Labels = raw3068step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3068step1 raw3068step1Labels permutation30 permutation6
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw3069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3069 raw3069Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw3069 raw3069Labels = mixedMoment B raw3069step0 raw3069step0Labels := by
      have hz : ∀ j, raw3069 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3069step0 = (fun i j => raw3069 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3069step0 raw3069; decide +kernel
      have hl : raw3069step0Labels = raw3069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3069 raw3069Labels permutation434 hz
    mixedMoment B raw3069step0 raw3069step0Labels = mixedMoment B raw3069step1 raw3069step1Labels := by
      have ha : raw3069step1 = (fun i j => raw3069step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3069step1 raw3069step0; decide +kernel
      have hl : raw3069step1Labels = raw3069step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3069step0 raw3069step0Labels permutation36 permutation3
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw3070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3070step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3070 raw3070Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw3070 raw3070Labels = mixedMoment B raw3070step0 raw3070step0Labels := by
      have hz : ∀ j, raw3070 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3070step0 = (fun i j => raw3070 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3070step0 raw3070; decide +kernel
      have hl : raw3070step0Labels = raw3070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3070 raw3070Labels permutation434 hz
    mixedMoment B raw3070step0 raw3070step0Labels = mixedMoment B raw3070step1 raw3070step1Labels := by
      have ha : raw3070step1 = (fun i j => raw3070step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3070step1 raw3070step0; decide +kernel
      have hl : raw3070step1Labels = raw3070step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3070step0 raw3070step0Labels permutation36 permutation3
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw3071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3071 raw3071Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw3071 raw3071Labels = mixedMoment B raw3071step0 raw3071step0Labels := by
      have ha : raw3071step0 = (fun i j => raw3071 (permutation204 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3071step0 raw3071; decide +kernel
      have hl : raw3071step0Labels = raw3071Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3071 raw3071Labels permutation204 permutation3
    _ = mixedMoment B node3979 node3979Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
