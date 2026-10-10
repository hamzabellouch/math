import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15488 raw15488Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw15488 raw15488Labels = mixedMoment B raw15488step0 raw15488step0Labels := by
      have ha : raw15488step0 = (fun i j => raw15488 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15488step0 raw15488; decide +kernel
      have hl : raw15488step0Labels = raw15488Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15488 raw15488Labels permutation683 permutation3
    mixedMoment B raw15488step0 raw15488step0Labels = mixedMoment B raw15488step1 raw15488step1Labels := by
      have ha : raw15488step1 = -raw15488step0 := by apply Matrix.ext; change ∀ i j, raw15488step1 i j = -(raw15488step0 i j); unfold raw15488step1 raw15488step0; decide +kernel
      have hl : raw15488step1Labels = raw15488step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3955 node3955Labels := by rfl

def raw15489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15489 raw15489Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw15489 raw15489Labels = mixedMoment B raw15489step0 raw15489step0Labels := by
      have ha : raw15489step0 = (fun i j => raw15489 (permutation677 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15489step0 raw15489; decide +kernel
      have hl : raw15489step0Labels = raw15489Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15489 raw15489Labels permutation677 permutation3
    mixedMoment B raw15489step0 raw15489step0Labels = mixedMoment B raw15489step1 raw15489step1Labels := by
      have ha : raw15489step1 = -raw15489step0 := by apply Matrix.ext; change ∀ i j, raw15489step1 i j = -(raw15489step0 i j); unfold raw15489step1 raw15489step0; decide +kernel
      have hl : raw15489step1Labels = raw15489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3955 node3955Labels := by rfl

def raw15490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15490 raw15490Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw15490 raw15490Labels = mixedMoment B raw15490step0 raw15490step0Labels := by
      have ha : raw15490step0 = (fun i j => raw15490 (permutation228 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15490step0 raw15490; decide +kernel
      have hl : raw15490step0Labels = raw15490Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15490 raw15490Labels permutation228 permutation6
    mixedMoment B raw15490step0 raw15490step0Labels = mixedMoment B raw15490step1 raw15490step1Labels := by
      have ha : raw15490step1 = -raw15490step0 := by apply Matrix.ext; change ∀ i j, raw15490step1 i j = -(raw15490step0 i j); unfold raw15490step1 raw15490step0; decide +kernel
      have hl : raw15490step1Labels = raw15490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3979 node3979Labels := by rfl

def raw15491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15491 raw15491Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw15491 raw15491Labels = mixedMoment B raw15491step0 raw15491step0Labels := by
      have ha : raw15491step0 = (fun i j => raw15491 (permutation228 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15491step0 raw15491; decide +kernel
      have hl : raw15491step0Labels = raw15491Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15491 raw15491Labels permutation228 permutation6
    mixedMoment B raw15491step0 raw15491step0Labels = mixedMoment B raw15491step1 raw15491step1Labels := by
      have ha : raw15491step1 = -raw15491step0 := by apply Matrix.ext; change ∀ i j, raw15491step1 i j = -(raw15491step0 i j); unfold raw15491step1 raw15491step0; decide +kernel
      have hl : raw15491step1Labels = raw15491step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw15492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15492 raw15492Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw15492 raw15492Labels = mixedMoment B raw15492step0 raw15492step0Labels := by
      have hz : ∀ j, raw15492 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw15492step0 = (fun i j => raw15492 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw15492step0 raw15492; decide +kernel
      have hl : raw15492step0Labels = raw15492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15492 raw15492Labels permutation265 hz
    mixedMoment B raw15492step0 raw15492step0Labels = mixedMoment B raw15492step1 raw15492step1Labels := by
      have ha : raw15492step1 = (fun i j => raw15492step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15492step1 raw15492step0; decide +kernel
      have hl : raw15492step1Labels = raw15492step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15492step0 raw15492step0Labels permutation32 permutation3
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw15493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15493 raw15493Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw15493 raw15493Labels = mixedMoment B raw15493step0 raw15493step0Labels := by
      have ha : raw15493step0 = (fun i j => raw15493 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15493step0 raw15493; decide +kernel
      have hl : raw15493step0Labels = raw15493Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15493 raw15493Labels permutation271 permutation3
    _ = mixedMoment B node3720 node3720Labels := by rfl

def raw15494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15494 raw15494Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw15494 raw15494Labels = mixedMoment B raw15494step0 raw15494step0Labels := by
      have ha : raw15494step0 = (fun i j => raw15494 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15494step0 raw15494; decide +kernel
      have hl : raw15494step0Labels = raw15494Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15494 raw15494Labels permutation680 permutation3
    mixedMoment B raw15494step0 raw15494step0Labels = mixedMoment B raw15494step1 raw15494step1Labels := by
      have ha : raw15494step1 = -raw15494step0 := by apply Matrix.ext; change ∀ i j, raw15494step1 i j = -(raw15494step0 i j); unfold raw15494step1 raw15494step0; decide +kernel
      have hl : raw15494step1Labels = raw15494step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3946 node3946Labels := by rfl

def raw15495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15495 raw15495Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw15495 raw15495Labels = mixedMoment B raw15495step0 raw15495step0Labels := by
      have ha : raw15495step0 = (fun i j => raw15495 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15495step0 raw15495; decide +kernel
      have hl : raw15495step0Labels = raw15495Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15495 raw15495Labels permutation646 permutation3
    mixedMoment B raw15495step0 raw15495step0Labels = mixedMoment B raw15495step1 raw15495step1Labels := by
      have ha : raw15495step1 = -raw15495step0 := by apply Matrix.ext; change ∀ i j, raw15495step1 i j = -(raw15495step0 i j); unfold raw15495step1 raw15495step0; decide +kernel
      have hl : raw15495step1Labels = raw15495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw15496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15496 raw15496Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw15496 raw15496Labels = mixedMoment B raw15496step0 raw15496step0Labels := by
      have ha : raw15496step0 = (fun i j => raw15496 (permutation225 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15496step0 raw15496; decide +kernel
      have hl : raw15496step0Labels = raw15496Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15496 raw15496Labels permutation225 permutation6
    mixedMoment B raw15496step0 raw15496step0Labels = mixedMoment B raw15496step1 raw15496step1Labels := by
      have ha : raw15496step1 = -raw15496step0 := by apply Matrix.ext; change ∀ i j, raw15496step1 i j = -(raw15496step0 i j); unfold raw15496step1 raw15496step0; decide +kernel
      have hl : raw15496step1Labels = raw15496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw15497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15497 raw15497Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw15497 raw15497Labels = mixedMoment B raw15497step0 raw15497step0Labels := by
      have ha : raw15497step0 = (fun i j => raw15497 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15497step0 raw15497; decide +kernel
      have hl : raw15497step0Labels = raw15497Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15497 raw15497Labels permutation265 permutation3
    _ = mixedMoment B node3720 node3720Labels := by rfl

def raw15498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15498 raw15498Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw15498 raw15498Labels = mixedMoment B raw15498step0 raw15498step0Labels := by
      have ha : raw15498step0 = (fun i j => raw15498 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15498step0 raw15498; decide +kernel
      have hl : raw15498step0Labels = raw15498Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15498 raw15498Labels permutation686 permutation3
    mixedMoment B raw15498step0 raw15498step0Labels = mixedMoment B raw15498step1 raw15498step1Labels := by
      have ha : raw15498step1 = -raw15498step0 := by apply Matrix.ext; change ∀ i j, raw15498step1 i j = -(raw15498step0 i j); unfold raw15498step1 raw15498step0; decide +kernel
      have hl : raw15498step1Labels = raw15498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3946 node3946Labels := by rfl

def raw15499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15499 raw15499Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw15499 raw15499Labels = mixedMoment B raw15499step0 raw15499step0Labels := by
      have ha : raw15499step0 = (fun i j => raw15499 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15499step0 raw15499; decide +kernel
      have hl : raw15499step0Labels = raw15499Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15499 raw15499Labels permutation664 permutation3
    mixedMoment B raw15499step0 raw15499step0Labels = mixedMoment B raw15499step1 raw15499step1Labels := by
      have ha : raw15499step1 = -raw15499step0 := by apply Matrix.ext; change ∀ i j, raw15499step1 i j = -(raw15499step0 i j); unfold raw15499step1 raw15499step0; decide +kernel
      have hl : raw15499step1Labels = raw15499step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw15500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15500 raw15500Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw15500 raw15500Labels = mixedMoment B raw15500step0 raw15500step0Labels := by
      have ha : raw15500step0 = (fun i j => raw15500 (permutation227 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15500step0 raw15500; decide +kernel
      have hl : raw15500step0Labels = raw15500Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15500 raw15500Labels permutation227 permutation6
    mixedMoment B raw15500step0 raw15500step0Labels = mixedMoment B raw15500step1 raw15500step1Labels := by
      have ha : raw15500step1 = -raw15500step0 := by apply Matrix.ext; change ∀ i j, raw15500step1 i j = -(raw15500step0 i j); unfold raw15500step1 raw15500step0; decide +kernel
      have hl : raw15500step1Labels = raw15500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw15501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15501 raw15501Labels = mixedMoment B node3337 node3337Labels := by
  calc
    mixedMoment B raw15501 raw15501Labels = mixedMoment B raw15501step0 raw15501step0Labels := by
      have ha : raw15501step0 = (fun i j => raw15501 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15501step0 raw15501; decide +kernel
      have hl : raw15501step0Labels = raw15501Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15501 raw15501Labels permutation583 permutation3
    mixedMoment B raw15501step0 raw15501step0Labels = mixedMoment B raw15501step1 raw15501step1Labels := by
      have ha : raw15501step1 = -raw15501step0 := by apply Matrix.ext; change ∀ i j, raw15501step1 i j = -(raw15501step0 i j); unfold raw15501step1 raw15501step0; decide +kernel
      have hl : raw15501step1Labels = raw15501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3337 node3337Labels := by rfl

def raw15502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15502 raw15502Labels = mixedMoment B node3342 node3342Labels := by
  calc
    mixedMoment B raw15502 raw15502Labels = mixedMoment B raw15502step0 raw15502step0Labels := by
      have ha : raw15502step0 = (fun i j => raw15502 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15502step0 raw15502; decide +kernel
      have hl : raw15502step0Labels = raw15502Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15502 raw15502Labels permutation587 permutation3
    mixedMoment B raw15502step0 raw15502step0Labels = mixedMoment B raw15502step1 raw15502step1Labels := by
      have ha : raw15502step1 = -raw15502step0 := by apply Matrix.ext; change ∀ i j, raw15502step1 i j = -(raw15502step0 i j); unfold raw15502step1 raw15502step0; decide +kernel
      have hl : raw15502step1Labels = raw15502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3342 node3342Labels := by rfl

def raw15503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15503 raw15503Labels = mixedMoment B node3342 node3342Labels := by
  calc
    mixedMoment B raw15503 raw15503Labels = mixedMoment B raw15503step0 raw15503step0Labels := by
      have ha : raw15503step0 = (fun i j => raw15503 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15503step0 raw15503; decide +kernel
      have hl : raw15503step0Labels = raw15503Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15503 raw15503Labels permutation582 permutation3
    mixedMoment B raw15503step0 raw15503step0Labels = mixedMoment B raw15503step1 raw15503step1Labels := by
      have ha : raw15503step1 = -raw15503step0 := by apply Matrix.ext; change ∀ i j, raw15503step1 i j = -(raw15503step0 i j); unfold raw15503step1 raw15503step0; decide +kernel
      have hl : raw15503step1Labels = raw15503step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3342 node3342Labels := by rfl

def raw15504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw15504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15504 raw15504Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw15504 raw15504Labels = mixedMoment B raw15504step0 raw15504step0Labels := by
      have ha : raw15504step0 = (fun i j => raw15504 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15504step0 raw15504; decide +kernel
      have hl : raw15504step0Labels = raw15504Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15504 raw15504Labels permutation584 permutation3
    mixedMoment B raw15504step0 raw15504step0Labels = mixedMoment B raw15504step1 raw15504step1Labels := by
      have ha : raw15504step1 = -raw15504step0 := by apply Matrix.ext; change ∀ i j, raw15504step1 i j = -(raw15504step0 i j); unfold raw15504step1 raw15504step0; decide +kernel
      have hl : raw15504step1Labels = raw15504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw15505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15505 raw15505Labels = mixedMoment B node2379 node2379Labels := by
  calc
    mixedMoment B raw15505 raw15505Labels = mixedMoment B raw15505step0 raw15505step0Labels := by
      have ha : raw15505step0 = (fun i j => raw15505 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15505step0 raw15505; decide +kernel
      have hl : raw15505step0Labels = raw15505Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15505 raw15505Labels permutation681 permutation3
    mixedMoment B raw15505step0 raw15505step0Labels = mixedMoment B raw15505step1 raw15505step1Labels := by
      have ha : raw15505step1 = -raw15505step0 := by apply Matrix.ext; change ∀ i j, raw15505step1 i j = -(raw15505step0 i j); unfold raw15505step1 raw15505step0; decide +kernel
      have hl : raw15505step1Labels = raw15505step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2379 node2379Labels := by rfl

def raw15506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15506 raw15506Labels = mixedMoment B node2384 node2384Labels := by
  calc
    mixedMoment B raw15506 raw15506Labels = mixedMoment B raw15506step0 raw15506step0Labels := by
      have ha : raw15506step0 = (fun i j => raw15506 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15506step0 raw15506; decide +kernel
      have hl : raw15506step0Labels = raw15506Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15506 raw15506Labels permutation686 permutation3
    mixedMoment B raw15506step0 raw15506step0Labels = mixedMoment B raw15506step1 raw15506step1Labels := by
      have ha : raw15506step1 = -raw15506step0 := by apply Matrix.ext; change ∀ i j, raw15506step1 i j = -(raw15506step0 i j); unfold raw15506step1 raw15506step0; decide +kernel
      have hl : raw15506step1Labels = raw15506step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2384 node2384Labels := by rfl

def raw15507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15507 raw15507Labels = mixedMoment B node2384 node2384Labels := by
  calc
    mixedMoment B raw15507 raw15507Labels = mixedMoment B raw15507step0 raw15507step0Labels := by
      have ha : raw15507step0 = (fun i j => raw15507 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15507step0 raw15507; decide +kernel
      have hl : raw15507step0Labels = raw15507Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15507 raw15507Labels permutation680 permutation3
    mixedMoment B raw15507step0 raw15507step0Labels = mixedMoment B raw15507step1 raw15507step1Labels := by
      have ha : raw15507step1 = -raw15507step0 := by apply Matrix.ext; change ∀ i j, raw15507step1 i j = -(raw15507step0 i j); unfold raw15507step1 raw15507step0; decide +kernel
      have hl : raw15507step1Labels = raw15507step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2384 node2384Labels := by rfl

def raw15508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw15508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15508 raw15508Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw15508 raw15508Labels = mixedMoment B raw15508step0 raw15508step0Labels := by
      have ha : raw15508step0 = (fun i j => raw15508 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15508step0 raw15508; decide +kernel
      have hl : raw15508step0Labels = raw15508Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15508 raw15508Labels permutation682 permutation3
    mixedMoment B raw15508step0 raw15508step0Labels = mixedMoment B raw15508step1 raw15508step1Labels := by
      have ha : raw15508step1 = -raw15508step0 := by apply Matrix.ext; change ∀ i j, raw15508step1 i j = -(raw15508step0 i j); unfold raw15508step1 raw15508step0; decide +kernel
      have hl : raw15508step1Labels = raw15508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw15509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15509step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15509step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15509 raw15509Labels = mixedMoment B node3819 node3819Labels := by
  calc
    mixedMoment B raw15509 raw15509Labels = mixedMoment B raw15509step0 raw15509step0Labels := by
      have ha : raw15509step0 = (fun i j => raw15509 (permutation296 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15509step0 raw15509; decide +kernel
      have hl : raw15509step0Labels = raw15509Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15509 raw15509Labels permutation296 permutation5
    mixedMoment B raw15509step0 raw15509step0Labels = mixedMoment B raw15509step1 raw15509step1Labels := by
      have ha : raw15509step1 = -raw15509step0 := by apply Matrix.ext; change ∀ i j, raw15509step1 i j = -(raw15509step0 i j); unfold raw15509step1 raw15509step0; decide +kernel
      have hl : raw15509step1Labels = raw15509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15509step1 raw15509step1Labels = mixedMoment B raw15509step2 raw15509step2Labels := by
      have ha : raw15509step2 = raw15509step1 := by apply Matrix.ext; unfold raw15509step2 raw15509step1; decide +kernel
      have hl : raw15509step1Labels = labelEmbedding1 ∘ raw15509step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15509step1 raw15509step1Labels raw15509step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3819 node3819Labels := by rfl

def raw15510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15510 raw15510Labels = mixedMoment B node3947 node3947Labels := by
  calc
    mixedMoment B raw15510 raw15510Labels = mixedMoment B raw15510step0 raw15510step0Labels := by
      have ha : raw15510step0 = (fun i j => raw15510 (permutation573 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15510step0 raw15510; decide +kernel
      have hl : raw15510step0Labels = raw15510Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15510 raw15510Labels permutation573 permutation5
    mixedMoment B raw15510step0 raw15510step0Labels = mixedMoment B raw15510step1 raw15510step1Labels := by
      have ha : raw15510step1 = raw15510step0 := by apply Matrix.ext; unfold raw15510step1 raw15510step0; decide +kernel
      have hl : raw15510step0Labels = labelEmbedding1 ∘ raw15510step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15510step0 raw15510step0Labels raw15510step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3947 node3947Labels := by rfl

def raw15511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15511step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15511 raw15511Labels = mixedMoment B node3947 node3947Labels := by
  calc
    mixedMoment B raw15511 raw15511Labels = mixedMoment B raw15511step0 raw15511step0Labels := by
      have ha : raw15511step0 = (fun i j => raw15511 (permutation571 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15511step0 raw15511; decide +kernel
      have hl : raw15511step0Labels = raw15511Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15511 raw15511Labels permutation571 permutation5
    mixedMoment B raw15511step0 raw15511step0Labels = mixedMoment B raw15511step1 raw15511step1Labels := by
      have ha : raw15511step1 = raw15511step0 := by apply Matrix.ext; unfold raw15511step1 raw15511step0; decide +kernel
      have hl : raw15511step0Labels = labelEmbedding1 ∘ raw15511step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15511step0 raw15511step0Labels raw15511step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3947 node3947Labels := by rfl

def raw15512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15512 raw15512Labels = mixedMoment B node3991 node3991Labels := by
  calc
    mixedMoment B raw15512 raw15512Labels = mixedMoment B raw15512step0 raw15512step0Labels := by
      have ha : raw15512step0 = (fun i j => raw15512 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15512step0 raw15512; decide +kernel
      have hl : raw15512step0Labels = raw15512Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15512 raw15512Labels permutation224 permutation7
    mixedMoment B raw15512step0 raw15512step0Labels = mixedMoment B raw15512step1 raw15512step1Labels := by
      have ha : raw15512step1 = -raw15512step0 := by apply Matrix.ext; change ∀ i j, raw15512step1 i j = -(raw15512step0 i j); unfold raw15512step1 raw15512step0; decide +kernel
      have hl : raw15512step1Labels = raw15512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15512step1 raw15512step1Labels = mixedMoment B raw15512step2 raw15512step2Labels := by
      have ha : raw15512step2 = raw15512step1 := by apply Matrix.ext; unfold raw15512step2 raw15512step1; decide +kernel
      have hl : raw15512step1Labels = labelEmbedding1 ∘ raw15512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15512step1 raw15512step1Labels raw15512step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3991 node3991Labels := by rfl

def raw15513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15513step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15513 raw15513Labels = mixedMoment B node4002 node4002Labels := by
  calc
    mixedMoment B raw15513 raw15513Labels = mixedMoment B raw15513step0 raw15513step0Labels := by
      have ha : raw15513step0 = (fun i j => raw15513 (permutation528 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15513step0 raw15513; decide +kernel
      have hl : raw15513step0Labels = raw15513Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15513 raw15513Labels permutation528 permutation5
    mixedMoment B raw15513step0 raw15513step0Labels = mixedMoment B raw15513step1 raw15513step1Labels := by
      have ha : raw15513step1 = raw15513step0 := by apply Matrix.ext; unfold raw15513step1 raw15513step0; decide +kernel
      have hl : raw15513step0Labels = labelEmbedding1 ∘ raw15513step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15513step0 raw15513step0Labels raw15513step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4002 node4002Labels := by rfl

def raw15514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15514step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15514step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15514step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15514step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15514 raw15514Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw15514 raw15514Labels = mixedMoment B raw15514step0 raw15514step0Labels := by
      have hz : ∀ j, raw15514 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw15514step0 = (fun i j => raw15514 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw15514step0 raw15514; decide +kernel
      have hl : raw15514step0Labels = raw15514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15514 raw15514Labels permutation265 hz
    mixedMoment B raw15514step0 raw15514step0Labels = mixedMoment B raw15514step1 raw15514step1Labels := by
      have ha : raw15514step1 = (fun i j => raw15514step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15514step1 raw15514step0; decide +kernel
      have hl : raw15514step1Labels = raw15514step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15514step0 raw15514step0Labels permutation44 permutation7
    mixedMoment B raw15514step1 raw15514step1Labels = mixedMoment B raw15514step2 raw15514step2Labels := by
      have ha : raw15514step2 = -raw15514step1 := by apply Matrix.ext; change ∀ i j, raw15514step2 i j = -(raw15514step1 i j); unfold raw15514step2 raw15514step1; decide +kernel
      have hl : raw15514step2Labels = raw15514step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15514step2 raw15514step2Labels = mixedMoment B raw15514step3 raw15514step3Labels := by
      have ha : raw15514step3 = raw15514step2 := by apply Matrix.ext; unfold raw15514step3 raw15514step2; decide +kernel
      have hl : raw15514step2Labels = labelEmbedding1 ∘ raw15514step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15514step2 raw15514step2Labels raw15514step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw15515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15515step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15515step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15515step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15515 raw15515Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw15515 raw15515Labels = mixedMoment B raw15515step0 raw15515step0Labels := by
      have ha : raw15515step0 = (fun i j => raw15515 (permutation306 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15515step0 raw15515; decide +kernel
      have hl : raw15515step0Labels = raw15515Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15515 raw15515Labels permutation306 permutation5
    mixedMoment B raw15515step0 raw15515step0Labels = mixedMoment B raw15515step1 raw15515step1Labels := by
      have ha : raw15515step1 = -raw15515step0 := by apply Matrix.ext; change ∀ i j, raw15515step1 i j = -(raw15515step0 i j); unfold raw15515step1 raw15515step0; decide +kernel
      have hl : raw15515step1Labels = raw15515step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15515step1 raw15515step1Labels = mixedMoment B raw15515step2 raw15515step2Labels := by
      have ha : raw15515step2 = raw15515step1 := by apply Matrix.ext; unfold raw15515step2 raw15515step1; decide +kernel
      have hl : raw15515step1Labels = labelEmbedding1 ∘ raw15515step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15515step1 raw15515step1Labels raw15515step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw15516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15516step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15516 raw15516Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw15516 raw15516Labels = mixedMoment B raw15516step0 raw15516step0Labels := by
      have ha : raw15516step0 = (fun i j => raw15516 (permutation226 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15516step0 raw15516; decide +kernel
      have hl : raw15516step0Labels = raw15516Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15516 raw15516Labels permutation226 permutation7
    mixedMoment B raw15516step0 raw15516step0Labels = mixedMoment B raw15516step1 raw15516step1Labels := by
      have ha : raw15516step1 = -raw15516step0 := by apply Matrix.ext; change ∀ i j, raw15516step1 i j = -(raw15516step0 i j); unfold raw15516step1 raw15516step0; decide +kernel
      have hl : raw15516step1Labels = raw15516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15516step1 raw15516step1Labels = mixedMoment B raw15516step2 raw15516step2Labels := by
      have ha : raw15516step2 = raw15516step1 := by apply Matrix.ext; unfold raw15516step2 raw15516step1; decide +kernel
      have hl : raw15516step1Labels = labelEmbedding1 ∘ raw15516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15516step1 raw15516step1Labels raw15516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw15517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15517step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15517step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15517 raw15517Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw15517 raw15517Labels = mixedMoment B raw15517step0 raw15517step0Labels := by
      have ha : raw15517step0 = (fun i j => raw15517 (permutation226 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15517step0 raw15517; decide +kernel
      have hl : raw15517step0Labels = raw15517Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15517 raw15517Labels permutation226 permutation7
    mixedMoment B raw15517step0 raw15517step0Labels = mixedMoment B raw15517step1 raw15517step1Labels := by
      have ha : raw15517step1 = -raw15517step0 := by apply Matrix.ext; change ∀ i j, raw15517step1 i j = -(raw15517step0 i j); unfold raw15517step1 raw15517step0; decide +kernel
      have hl : raw15517step1Labels = raw15517step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15517step1 raw15517step1Labels = mixedMoment B raw15517step2 raw15517step2Labels := by
      have ha : raw15517step2 = raw15517step1 := by apply Matrix.ext; unfold raw15517step2 raw15517step1; decide +kernel
      have hl : raw15517step1Labels = labelEmbedding1 ∘ raw15517step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15517step1 raw15517step1Labels raw15517step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw15518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15518step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15518step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15518 raw15518Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw15518 raw15518Labels = mixedMoment B raw15518step0 raw15518step0Labels := by
      have ha : raw15518step0 = (fun i j => raw15518 (permutation226 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15518step0 raw15518; decide +kernel
      have hl : raw15518step0Labels = raw15518Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15518 raw15518Labels permutation226 permutation7
    mixedMoment B raw15518step0 raw15518step0Labels = mixedMoment B raw15518step1 raw15518step1Labels := by
      have ha : raw15518step1 = -raw15518step0 := by apply Matrix.ext; change ∀ i j, raw15518step1 i j = -(raw15518step0 i j); unfold raw15518step1 raw15518step0; decide +kernel
      have hl : raw15518step1Labels = raw15518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15518step1 raw15518step1Labels = mixedMoment B raw15518step2 raw15518step2Labels := by
      have ha : raw15518step2 = raw15518step1 := by apply Matrix.ext; unfold raw15518step2 raw15518step1; decide +kernel
      have hl : raw15518step1Labels = labelEmbedding1 ∘ raw15518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15518step1 raw15518step1Labels raw15518step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw15519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15519step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15519step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15519 raw15519Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw15519 raw15519Labels = mixedMoment B raw15519step0 raw15519step0Labels := by
      have ha : raw15519step0 = (fun i j => raw15519 (permutation290 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15519step0 raw15519; decide +kernel
      have hl : raw15519step0Labels = raw15519Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15519 raw15519Labels permutation290 permutation5
    mixedMoment B raw15519step0 raw15519step0Labels = mixedMoment B raw15519step1 raw15519step1Labels := by
      have ha : raw15519step1 = -raw15519step0 := by apply Matrix.ext; change ∀ i j, raw15519step1 i j = -(raw15519step0 i j); unfold raw15519step1 raw15519step0; decide +kernel
      have hl : raw15519step1Labels = raw15519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15519step1 raw15519step1Labels = mixedMoment B raw15519step2 raw15519step2Labels := by
      have ha : raw15519step2 = raw15519step1 := by apply Matrix.ext; unfold raw15519step2 raw15519step1; decide +kernel
      have hl : raw15519step1Labels = labelEmbedding1 ∘ raw15519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15519step1 raw15519step1Labels raw15519step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw15520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15520step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15520step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15520step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15520 raw15520Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw15520 raw15520Labels = mixedMoment B raw15520step0 raw15520step0Labels := by
      have ha : raw15520step0 = (fun i j => raw15520 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15520step0 raw15520; decide +kernel
      have hl : raw15520step0Labels = raw15520Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15520 raw15520Labels permutation224 permutation7
    mixedMoment B raw15520step0 raw15520step0Labels = mixedMoment B raw15520step1 raw15520step1Labels := by
      have ha : raw15520step1 = -raw15520step0 := by apply Matrix.ext; change ∀ i j, raw15520step1 i j = -(raw15520step0 i j); unfold raw15520step1 raw15520step0; decide +kernel
      have hl : raw15520step1Labels = raw15520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15520step1 raw15520step1Labels = mixedMoment B raw15520step2 raw15520step2Labels := by
      have ha : raw15520step2 = raw15520step1 := by apply Matrix.ext; unfold raw15520step2 raw15520step1; decide +kernel
      have hl : raw15520step1Labels = labelEmbedding1 ∘ raw15520step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15520step1 raw15520step1Labels raw15520step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw15521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15521step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15521step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15521step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15521 raw15521Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw15521 raw15521Labels = mixedMoment B raw15521step0 raw15521step0Labels := by
      have ha : raw15521step0 = (fun i j => raw15521 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15521step0 raw15521; decide +kernel
      have hl : raw15521step0Labels = raw15521Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15521 raw15521Labels permutation224 permutation7
    mixedMoment B raw15521step0 raw15521step0Labels = mixedMoment B raw15521step1 raw15521step1Labels := by
      have ha : raw15521step1 = -raw15521step0 := by apply Matrix.ext; change ∀ i j, raw15521step1 i j = -(raw15521step0 i j); unfold raw15521step1 raw15521step0; decide +kernel
      have hl : raw15521step1Labels = raw15521step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15521step1 raw15521step1Labels = mixedMoment B raw15521step2 raw15521step2Labels := by
      have ha : raw15521step2 = raw15521step1 := by apply Matrix.ext; unfold raw15521step2 raw15521step1; decide +kernel
      have hl : raw15521step1Labels = labelEmbedding1 ∘ raw15521step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15521step1 raw15521step1Labels raw15521step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw15522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15522 raw15522Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw15522 raw15522Labels = mixedMoment B raw15522step0 raw15522step0Labels := by
      have ha : raw15522step0 = (fun i j => raw15522 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15522step0 raw15522; decide +kernel
      have hl : raw15522step0Labels = raw15522Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15522 raw15522Labels permutation224 permutation7
    mixedMoment B raw15522step0 raw15522step0Labels = mixedMoment B raw15522step1 raw15522step1Labels := by
      have ha : raw15522step1 = -raw15522step0 := by apply Matrix.ext; change ∀ i j, raw15522step1 i j = -(raw15522step0 i j); unfold raw15522step1 raw15522step0; decide +kernel
      have hl : raw15522step1Labels = raw15522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15522step1 raw15522step1Labels = mixedMoment B raw15522step2 raw15522step2Labels := by
      have ha : raw15522step2 = raw15522step1 := by apply Matrix.ext; unfold raw15522step2 raw15522step1; decide +kernel
      have hl : raw15522step1Labels = labelEmbedding1 ∘ raw15522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15522step1 raw15522step1Labels raw15522step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw15523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15523step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15523 raw15523Labels = mixedMoment B node2389 node2389Labels := by
  calc
    mixedMoment B raw15523 raw15523Labels = mixedMoment B raw15523step0 raw15523step0Labels := by
      have ha : raw15523step0 = (fun i j => raw15523 (permutation572 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15523step0 raw15523; decide +kernel
      have hl : raw15523step0Labels = raw15523Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15523 raw15523Labels permutation572 permutation5
    mixedMoment B raw15523step0 raw15523step0Labels = mixedMoment B raw15523step1 raw15523step1Labels := by
      have ha : raw15523step1 = raw15523step0 := by apply Matrix.ext; unfold raw15523step1 raw15523step0; decide +kernel
      have hl : raw15523step0Labels = labelEmbedding1 ∘ raw15523step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15523step0 raw15523step0Labels raw15523step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2389 node2389Labels := by rfl

def raw15524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15524 raw15524Labels = mixedMoment B node2390 node2390Labels := by
  calc
    mixedMoment B raw15524 raw15524Labels = mixedMoment B raw15524step0 raw15524step0Labels := by
      have ha : raw15524step0 = (fun i j => raw15524 (permutation573 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15524step0 raw15524; decide +kernel
      have hl : raw15524step0Labels = raw15524Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15524 raw15524Labels permutation573 permutation5
    mixedMoment B raw15524step0 raw15524step0Labels = mixedMoment B raw15524step1 raw15524step1Labels := by
      have ha : raw15524step1 = raw15524step0 := by apply Matrix.ext; unfold raw15524step1 raw15524step0; decide +kernel
      have hl : raw15524step0Labels = labelEmbedding1 ∘ raw15524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15524step0 raw15524step0Labels raw15524step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2390 node2390Labels := by rfl

def raw15525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15525step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15525 raw15525Labels = mixedMoment B node2390 node2390Labels := by
  calc
    mixedMoment B raw15525 raw15525Labels = mixedMoment B raw15525step0 raw15525step0Labels := by
      have ha : raw15525step0 = (fun i j => raw15525 (permutation571 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15525step0 raw15525; decide +kernel
      have hl : raw15525step0Labels = raw15525Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15525 raw15525Labels permutation571 permutation5
    mixedMoment B raw15525step0 raw15525step0Labels = mixedMoment B raw15525step1 raw15525step1Labels := by
      have ha : raw15525step1 = raw15525step0 := by apply Matrix.ext; unfold raw15525step1 raw15525step0; decide +kernel
      have hl : raw15525step0Labels = labelEmbedding1 ∘ raw15525step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15525step0 raw15525step0Labels raw15525step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2390 node2390Labels := by rfl

def raw15526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw15526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15526step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15526 raw15526Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw15526 raw15526Labels = mixedMoment B raw15526step0 raw15526step0Labels := by
      have ha : raw15526step0 = (fun i j => raw15526 (permutation572 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15526step0 raw15526; decide +kernel
      have hl : raw15526step0Labels = raw15526Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15526 raw15526Labels permutation572 permutation5
    mixedMoment B raw15526step0 raw15526step0Labels = mixedMoment B raw15526step1 raw15526step1Labels := by
      have ha : raw15526step1 = raw15526step0 := by apply Matrix.ext; unfold raw15526step1 raw15526step0; decide +kernel
      have hl : raw15526step0Labels = labelEmbedding1 ∘ raw15526step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15526step0 raw15526step0Labels raw15526step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw15527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15527step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15527 raw15527Labels = mixedMoment B node3345 node3345Labels := by
  calc
    mixedMoment B raw15527 raw15527Labels = mixedMoment B raw15527step0 raw15527step0Labels := by
      have ha : raw15527step0 = (fun i j => raw15527 (permutation668 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15527step0 raw15527; decide +kernel
      have hl : raw15527step0Labels = raw15527Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15527 raw15527Labels permutation668 permutation5
    mixedMoment B raw15527step0 raw15527step0Labels = mixedMoment B raw15527step1 raw15527step1Labels := by
      have ha : raw15527step1 = raw15527step0 := by apply Matrix.ext; unfold raw15527step1 raw15527step0; decide +kernel
      have hl : raw15527step0Labels = labelEmbedding1 ∘ raw15527step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15527step0 raw15527step0Labels raw15527step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3345 node3345Labels := by rfl

def raw15528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15528 raw15528Labels = mixedMoment B node3346 node3346Labels := by
  calc
    mixedMoment B raw15528 raw15528Labels = mixedMoment B raw15528step0 raw15528step0Labels := by
      have ha : raw15528step0 = (fun i j => raw15528 (permutation669 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15528step0 raw15528; decide +kernel
      have hl : raw15528step0Labels = raw15528Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15528 raw15528Labels permutation669 permutation5
    mixedMoment B raw15528step0 raw15528step0Labels = mixedMoment B raw15528step1 raw15528step1Labels := by
      have ha : raw15528step1 = raw15528step0 := by apply Matrix.ext; unfold raw15528step1 raw15528step0; decide +kernel
      have hl : raw15528step0Labels = labelEmbedding1 ∘ raw15528step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15528step0 raw15528step0Labels raw15528step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3346 node3346Labels := by rfl

def raw15529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15529 raw15529Labels = mixedMoment B node3346 node3346Labels := by
  calc
    mixedMoment B raw15529 raw15529Labels = mixedMoment B raw15529step0 raw15529step0Labels := by
      have ha : raw15529step0 = (fun i j => raw15529 (permutation667 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15529step0 raw15529; decide +kernel
      have hl : raw15529step0Labels = raw15529Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15529 raw15529Labels permutation667 permutation5
    mixedMoment B raw15529step0 raw15529step0Labels = mixedMoment B raw15529step1 raw15529step1Labels := by
      have ha : raw15529step1 = raw15529step0 := by apply Matrix.ext; unfold raw15529step1 raw15529step0; decide +kernel
      have hl : raw15529step0Labels = labelEmbedding1 ∘ raw15529step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15529step0 raw15529step0Labels raw15529step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3346 node3346Labels := by rfl

def raw15530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw15530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15530step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15530 raw15530Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw15530 raw15530Labels = mixedMoment B raw15530step0 raw15530step0Labels := by
      have ha : raw15530step0 = (fun i j => raw15530 (permutation668 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15530step0 raw15530; decide +kernel
      have hl : raw15530step0Labels = raw15530Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15530 raw15530Labels permutation668 permutation5
    mixedMoment B raw15530step0 raw15530step0Labels = mixedMoment B raw15530step1 raw15530step1Labels := by
      have ha : raw15530step1 = raw15530step0 := by apply Matrix.ext; unfold raw15530step1 raw15530step0; decide +kernel
      have hl : raw15530step0Labels = labelEmbedding1 ∘ raw15530step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15530step0 raw15530step0Labels raw15530step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw15531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15531 raw15531Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw15531 raw15531Labels = mixedMoment B raw15531step0 raw15531step0Labels := by
      have ha : raw15531step0 = (fun i j => raw15531 (permutation528 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15531step0 raw15531; decide +kernel
      have hl : raw15531step0Labels = raw15531Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15531 raw15531Labels permutation528 permutation4
    _ = mixedMoment B node3949 node3949Labels := by rfl

def raw15532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15532 raw15532Labels = mixedMoment B node3947 node3947Labels := by
  calc
    mixedMoment B raw15532 raw15532Labels = mixedMoment B raw15532step0 raw15532step0Labels := by
      have ha : raw15532step0 = (fun i j => raw15532 (permutation527 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15532step0 raw15532; decide +kernel
      have hl : raw15532step0Labels = raw15532Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15532 raw15532Labels permutation527 permutation4
    _ = mixedMoment B node3947 node3947Labels := by rfl

def raw15533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15533 raw15533Labels = mixedMoment B node3947 node3947Labels := by
  calc
    mixedMoment B raw15533 raw15533Labels = mixedMoment B raw15533step0 raw15533step0Labels := by
      have ha : raw15533step0 = (fun i j => raw15533 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15533step0 raw15533; decide +kernel
      have hl : raw15533step0Labels = raw15533Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15533 raw15533Labels permutation526 permutation4
    _ = mixedMoment B node3947 node3947Labels := by rfl

def raw15534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw15534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15534 raw15534Labels = mixedMoment B node4008 node4008Labels := by
  calc
    mixedMoment B raw15534 raw15534Labels = mixedMoment B raw15534step0 raw15534step0Labels := by
      have ha : raw15534step0 = (fun i j => raw15534 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15534step0 raw15534; decide +kernel
      have hl : raw15534step0Labels = raw15534Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15534 raw15534Labels permutation640 permutation2
    mixedMoment B raw15534step0 raw15534step0Labels = mixedMoment B raw15534step1 raw15534step1Labels := by
      have ha : raw15534step1 = -raw15534step0 := by apply Matrix.ext; change ∀ i j, raw15534step1 i j = -(raw15534step0 i j); unfold raw15534step1 raw15534step0; decide +kernel
      have hl : raw15534step1Labels = raw15534step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4008 node4008Labels := by rfl

def raw15535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15535 raw15535Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw15535 raw15535Labels = mixedMoment B raw15535step0 raw15535step0Labels := by
      have ha : raw15535step0 = (fun i j => raw15535 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15535step0 raw15535; decide +kernel
      have hl : raw15535step0Labels = raw15535Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15535 raw15535Labels permutation526 permutation4
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw15536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15536 raw15536Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw15536 raw15536Labels = mixedMoment B raw15536step0 raw15536step0Labels := by
      have ha : raw15536step0 = (fun i j => raw15536 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15536step0 raw15536; decide +kernel
      have hl : raw15536step0Labels = raw15536Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15536 raw15536Labels permutation160 permutation2
    _ = mixedMoment B node3724 node3724Labels := by rfl

def raw15537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15537 raw15537Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw15537 raw15537Labels = mixedMoment B raw15537step0 raw15537step0Labels := by
      have ha : raw15537step0 = (fun i j => raw15537 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15537step0 raw15537; decide +kernel
      have hl : raw15537step0Labels = raw15537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15537 raw15537Labels permutation154 permutation2
    _ = mixedMoment B node3724 node3724Labels := by rfl

def raw15538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw15538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15538 raw15538Labels = mixedMoment B node3009 node3009Labels := by
  calc
    mixedMoment B raw15538 raw15538Labels = mixedMoment B raw15538step0 raw15538step0Labels := by
      have ha : raw15538step0 = (fun i j => raw15538 (permutation572 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15538step0 raw15538; decide +kernel
      have hl : raw15538step0Labels = raw15538Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15538 raw15538Labels permutation572 permutation4
    _ = mixedMoment B node3009 node3009Labels := by rfl

def raw15539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw15539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw15539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15539 raw15539Labels = mixedMoment B node3012 node3012Labels := by
  calc
    mixedMoment B raw15539 raw15539Labels = mixedMoment B raw15539step0 raw15539step0Labels := by
      have ha : raw15539step0 = (fun i j => raw15539 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15539step0 raw15539; decide +kernel
      have hl : raw15539step0Labels = raw15539Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15539 raw15539Labels permutation682 permutation2
    mixedMoment B raw15539step0 raw15539step0Labels = mixedMoment B raw15539step1 raw15539step1Labels := by
      have ha : raw15539step1 = -raw15539step0 := by apply Matrix.ext; change ∀ i j, raw15539step1 i j = -(raw15539step0 i j); unfold raw15539step1 raw15539step0; decide +kernel
      have hl : raw15539step1Labels = raw15539step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3012 node3012Labels := by rfl

def raw15540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15540 raw15540Labels = mixedMoment B node3827 node3827Labels := by
  calc
    mixedMoment B raw15540 raw15540Labels = mixedMoment B raw15540step0 raw15540step0Labels := by
      have ha : raw15540step0 = (fun i j => raw15540 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15540step0 raw15540; decide +kernel
      have hl : raw15540step0Labels = raw15540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15540 raw15540Labels permutation160 permutation2
    _ = mixedMoment B node3827 node3827Labels := by rfl

def raw15541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw15541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15541 raw15541Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw15541 raw15541Labels = mixedMoment B raw15541step0 raw15541step0Labels := by
      have ha : raw15541step0 = (fun i j => raw15541 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15541step0 raw15541; decide +kernel
      have hl : raw15541step0Labels = raw15541Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15541 raw15541Labels permutation166 permutation2
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw15542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15542 raw15542Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw15542 raw15542Labels = mixedMoment B raw15542step0 raw15542step0Labels := by
      have ha : raw15542step0 = (fun i j => raw15542 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15542step0 raw15542; decide +kernel
      have hl : raw15542step0Labels = raw15542Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15542 raw15542Labels permutation160 permutation2
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw15543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15543 raw15543Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw15543 raw15543Labels = mixedMoment B raw15543step0 raw15543step0Labels := by
      have ha : raw15543step0 = (fun i j => raw15543 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15543step0 raw15543; decide +kernel
      have hl : raw15543step0Labels = raw15543Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15543 raw15543Labels permutation681 permutation2
    mixedMoment B raw15543step0 raw15543step0Labels = mixedMoment B raw15543step1 raw15543step1Labels := by
      have ha : raw15543step1 = -raw15543step0 := by apply Matrix.ext; change ∀ i j, raw15543step1 i j = -(raw15543step0 i j); unfold raw15543step1 raw15543step0; decide +kernel
      have hl : raw15543step1Labels = raw15543step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw15544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15544 raw15544Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw15544 raw15544Labels = mixedMoment B raw15544step0 raw15544step0Labels := by
      have ha : raw15544step0 = (fun i j => raw15544 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15544step0 raw15544; decide +kernel
      have hl : raw15544step0Labels = raw15544Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15544 raw15544Labels permutation683 permutation2
    mixedMoment B raw15544step0 raw15544step0Labels = mixedMoment B raw15544step1 raw15544step1Labels := by
      have ha : raw15544step1 = -raw15544step0 := by apply Matrix.ext; change ∀ i j, raw15544step1 i j = -(raw15544step0 i j); unfold raw15544step1 raw15544step0; decide +kernel
      have hl : raw15544step1Labels = raw15544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw15545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15545 raw15545Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw15545 raw15545Labels = mixedMoment B raw15545step0 raw15545step0Labels := by
      have ha : raw15545step0 = (fun i j => raw15545 (permutation677 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15545step0 raw15545; decide +kernel
      have hl : raw15545step0Labels = raw15545Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15545 raw15545Labels permutation677 permutation2
    mixedMoment B raw15545step0 raw15545step0Labels = mixedMoment B raw15545step1 raw15545step1Labels := by
      have ha : raw15545step1 = -raw15545step0 := by apply Matrix.ext; change ∀ i j, raw15545step1 i j = -(raw15545step0 i j); unfold raw15545step1 raw15545step0; decide +kernel
      have hl : raw15545step1Labels = raw15545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw15546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15546step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15546step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15546step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15546step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15546 raw15546Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw15546 raw15546Labels = mixedMoment B raw15546step0 raw15546step0Labels := by
      have ha : raw15546step0 = (fun i j => raw15546 (permutation524 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15546step0 raw15546; decide +kernel
      have hl : raw15546step0Labels = raw15546Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15546 raw15546Labels permutation524 permutation4
    mixedMoment B raw15546step0 raw15546step0Labels = mixedMoment B raw15546step1 raw15546step1Labels := by
      have ha : raw15546step1 = -raw15546step0 := by apply Matrix.ext; change ∀ i j, raw15546step1 i j = -(raw15546step0 i j); unfold raw15546step1 raw15546step0; decide +kernel
      have hl : raw15546step1Labels = raw15546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15546step1 raw15546step1Labels = mixedMoment B raw15546step2 raw15546step2Labels := by
      have ha : raw15546step2 = raw15546step1 := by apply Matrix.ext; unfold raw15546step2 raw15546step1; decide +kernel
      have hl : raw15546step1Labels = labelEmbedding7 ∘ raw15546step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15546step1 raw15546step1Labels raw15546step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw15547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15547step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15547 raw15547Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw15547 raw15547Labels = mixedMoment B raw15547step0 raw15547step0Labels := by
      have ha : raw15547step0 = (fun i j => raw15547 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15547step0 raw15547; decide +kernel
      have hl : raw15547step0Labels = raw15547Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15547 raw15547Labels permutation572 permutation7
    mixedMoment B raw15547step0 raw15547step0Labels = mixedMoment B raw15547step1 raw15547step1Labels := by
      have ha : raw15547step1 = raw15547step0 := by apply Matrix.ext; unfold raw15547step1 raw15547step0; decide +kernel
      have hl : raw15547step0Labels = labelEmbedding10 ∘ raw15547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15547step0 raw15547step0Labels raw15547step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw15548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15548step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15548step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15548step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15548step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15548 raw15548Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw15548 raw15548Labels = mixedMoment B raw15548step0 raw15548step0Labels := by
      have ha : raw15548step0 = (fun i j => raw15548 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15548step0 raw15548; decide +kernel
      have hl : raw15548step0Labels = raw15548Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15548 raw15548Labels permutation224 permutation5
    mixedMoment B raw15548step0 raw15548step0Labels = mixedMoment B raw15548step1 raw15548step1Labels := by
      have ha : raw15548step1 = -raw15548step0 := by apply Matrix.ext; change ∀ i j, raw15548step1 i j = -(raw15548step0 i j); unfold raw15548step1 raw15548step0; decide +kernel
      have hl : raw15548step1Labels = raw15548step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15548step1 raw15548step1Labels = mixedMoment B raw15548step2 raw15548step2Labels := by
      have ha : raw15548step2 = raw15548step1 := by apply Matrix.ext; unfold raw15548step2 raw15548step1; decide +kernel
      have hl : raw15548step1Labels = labelEmbedding8 ∘ raw15548step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15548step1 raw15548step1Labels raw15548step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4863 node4863Labels := by rfl

def raw15549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15549step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15549 raw15549Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw15549 raw15549Labels = mixedMoment B raw15549step0 raw15549step0Labels := by
      have ha : raw15549step0 = (fun i j => raw15549 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15549step0 raw15549; decide +kernel
      have hl : raw15549step0Labels = raw15549Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15549 raw15549Labels permutation176 permutation3
    mixedMoment B raw15549step0 raw15549step0Labels = mixedMoment B raw15549step1 raw15549step1Labels := by
      have ha : raw15549step1 = raw15549step0 := by apply Matrix.ext; unfold raw15549step1 raw15549step0; decide +kernel
      have hl : raw15549step0Labels = labelEmbedding6 ∘ raw15549step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15549step0 raw15549step0Labels raw15549step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw15550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15550step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15550 raw15550Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw15550 raw15550Labels = mixedMoment B raw15550step0 raw15550step0Labels := by
      have ha : raw15550step0 = (fun i j => raw15550 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15550step0 raw15550; decide +kernel
      have hl : raw15550step0Labels = raw15550Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15550 raw15550Labels permutation200 permutation3
    mixedMoment B raw15550step0 raw15550step0Labels = mixedMoment B raw15550step1 raw15550step1Labels := by
      have ha : raw15550step1 = raw15550step0 := by apply Matrix.ext; unfold raw15550step1 raw15550step0; decide +kernel
      have hl : raw15550step0Labels = labelEmbedding6 ∘ raw15550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15550step0 raw15550step0Labels raw15550step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw15551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15551step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15551step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15551step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15551step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15551 raw15551Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw15551 raw15551Labels = mixedMoment B raw15551step0 raw15551step0Labels := by
      have ha : raw15551step0 = (fun i j => raw15551 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15551step0 raw15551; decide +kernel
      have hl : raw15551step0Labels = raw15551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15551 raw15551Labels permutation526 permutation4
    mixedMoment B raw15551step0 raw15551step0Labels = mixedMoment B raw15551step1 raw15551step1Labels := by
      have ha : raw15551step1 = -raw15551step0 := by apply Matrix.ext; change ∀ i j, raw15551step1 i j = -(raw15551step0 i j); unfold raw15551step1 raw15551step0; decide +kernel
      have hl : raw15551step1Labels = raw15551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15551step1 raw15551step1Labels = mixedMoment B raw15551step2 raw15551step2Labels := by
      have ha : raw15551step2 = raw15551step1 := by apply Matrix.ext; unfold raw15551step2 raw15551step1; decide +kernel
      have hl : raw15551step1Labels = labelEmbedding7 ∘ raw15551step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15551step1 raw15551step1Labels raw15551step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

def raw15552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw15552step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15552step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15552step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15552step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15552 raw15552Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw15552 raw15552Labels = mixedMoment B raw15552step0 raw15552step0Labels := by
      have ha : raw15552step0 = (fun i j => raw15552 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15552step0 raw15552; decide +kernel
      have hl : raw15552step0Labels = raw15552Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15552 raw15552Labels permutation240 permutation5
    mixedMoment B raw15552step0 raw15552step0Labels = mixedMoment B raw15552step1 raw15552step1Labels := by
      have ha : raw15552step1 = -raw15552step0 := by apply Matrix.ext; change ∀ i j, raw15552step1 i j = -(raw15552step0 i j); unfold raw15552step1 raw15552step0; decide +kernel
      have hl : raw15552step1Labels = raw15552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15552step1 raw15552step1Labels = mixedMoment B raw15552step2 raw15552step2Labels := by
      have ha : raw15552step2 = raw15552step1 := by apply Matrix.ext; unfold raw15552step2 raw15552step1; decide +kernel
      have hl : raw15552step1Labels = labelEmbedding8 ∘ raw15552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15552step1 raw15552step1Labels raw15552step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw15553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15553step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15553 raw15553Labels = mixedMoment B node4799 node4799Labels := by
  calc
    mixedMoment B raw15553 raw15553Labels = mixedMoment B raw15553step0 raw15553step0Labels := by
      have ha : raw15553step0 = (fun i j => raw15553 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15553step0 raw15553; decide +kernel
      have hl : raw15553step0Labels = raw15553Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15553 raw15553Labels permutation160 permutation3
    mixedMoment B raw15553step0 raw15553step0Labels = mixedMoment B raw15553step1 raw15553step1Labels := by
      have ha : raw15553step1 = raw15553step0 := by apply Matrix.ext; unfold raw15553step1 raw15553step0; decide +kernel
      have hl : raw15553step0Labels = labelEmbedding6 ∘ raw15553step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15553step0 raw15553step0Labels raw15553step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4799 node4799Labels := by rfl

def raw15554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15554step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15554 raw15554Labels = mixedMoment B node5350 node5350Labels := by
  calc
    mixedMoment B raw15554 raw15554Labels = mixedMoment B raw15554step0 raw15554step0Labels := by
      have ha : raw15554step0 = (fun i j => raw15554 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15554step0 raw15554; decide +kernel
      have hl : raw15554step0Labels = raw15554Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15554 raw15554Labels permutation160 permutation3
    mixedMoment B raw15554step0 raw15554step0Labels = mixedMoment B raw15554step1 raw15554step1Labels := by
      have ha : raw15554step1 = raw15554step0 := by apply Matrix.ext; unfold raw15554step1 raw15554step0; decide +kernel
      have hl : raw15554step0Labels = labelEmbedding6 ∘ raw15554step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15554step0 raw15554step0Labels raw15554step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5350 node5350Labels := by rfl

def raw15555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15555step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15555 raw15555Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw15555 raw15555Labels = mixedMoment B raw15555step0 raw15555step0Labels := by
      have ha : raw15555step0 = (fun i j => raw15555 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15555step0 raw15555; decide +kernel
      have hl : raw15555step0Labels = raw15555Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15555 raw15555Labels permutation160 permutation3
    mixedMoment B raw15555step0 raw15555step0Labels = mixedMoment B raw15555step1 raw15555step1Labels := by
      have ha : raw15555step1 = raw15555step0 := by apply Matrix.ext; unfold raw15555step1 raw15555step0; decide +kernel
      have hl : raw15555step0Labels = labelEmbedding6 ∘ raw15555step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15555step0 raw15555step0Labels raw15555step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw15556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15556step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15556step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15556step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15556step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15556 raw15556Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw15556 raw15556Labels = mixedMoment B raw15556step0 raw15556step0Labels := by
      have ha : raw15556step0 = (fun i j => raw15556 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15556step0 raw15556; decide +kernel
      have hl : raw15556step0Labels = raw15556Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15556 raw15556Labels permutation227 permutation5
    mixedMoment B raw15556step0 raw15556step0Labels = mixedMoment B raw15556step1 raw15556step1Labels := by
      have ha : raw15556step1 = -raw15556step0 := by apply Matrix.ext; change ∀ i j, raw15556step1 i j = -(raw15556step0 i j); unfold raw15556step1 raw15556step0; decide +kernel
      have hl : raw15556step1Labels = raw15556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15556step1 raw15556step1Labels = mixedMoment B raw15556step2 raw15556step2Labels := by
      have ha : raw15556step2 = raw15556step1 := by apply Matrix.ext; unfold raw15556step2 raw15556step1; decide +kernel
      have hl : raw15556step1Labels = labelEmbedding8 ∘ raw15556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15556step1 raw15556step1Labels raw15556step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw15557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15557step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15557 raw15557Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw15557 raw15557Labels = mixedMoment B raw15557step0 raw15557step0Labels := by
      have ha : raw15557step0 = (fun i j => raw15557 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15557step0 raw15557; decide +kernel
      have hl : raw15557step0Labels = raw15557Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15557 raw15557Labels permutation161 permutation3
    mixedMoment B raw15557step0 raw15557step0Labels = mixedMoment B raw15557step1 raw15557step1Labels := by
      have ha : raw15557step1 = raw15557step0 := by apply Matrix.ext; unfold raw15557step1 raw15557step0; decide +kernel
      have hl : raw15557step0Labels = labelEmbedding6 ∘ raw15557step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15557step0 raw15557step0Labels raw15557step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw15558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15558step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15558 raw15558Labels = mixedMoment B node4799 node4799Labels := by
  calc
    mixedMoment B raw15558 raw15558Labels = mixedMoment B raw15558step0 raw15558step0Labels := by
      have ha : raw15558step0 = (fun i j => raw15558 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15558step0 raw15558; decide +kernel
      have hl : raw15558step0Labels = raw15558Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15558 raw15558Labels permutation154 permutation3
    mixedMoment B raw15558step0 raw15558step0Labels = mixedMoment B raw15558step1 raw15558step1Labels := by
      have ha : raw15558step1 = raw15558step0 := by apply Matrix.ext; unfold raw15558step1 raw15558step0; decide +kernel
      have hl : raw15558step0Labels = labelEmbedding6 ∘ raw15558step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15558step0 raw15558step0Labels raw15558step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4799 node4799Labels := by rfl

def raw15559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15559step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15559 raw15559Labels = mixedMoment B node5350 node5350Labels := by
  calc
    mixedMoment B raw15559 raw15559Labels = mixedMoment B raw15559step0 raw15559step0Labels := by
      have ha : raw15559step0 = (fun i j => raw15559 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15559step0 raw15559; decide +kernel
      have hl : raw15559step0Labels = raw15559Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15559 raw15559Labels permutation154 permutation3
    mixedMoment B raw15559step0 raw15559step0Labels = mixedMoment B raw15559step1 raw15559step1Labels := by
      have ha : raw15559step1 = raw15559step0 := by apply Matrix.ext; unfold raw15559step1 raw15559step0; decide +kernel
      have hl : raw15559step0Labels = labelEmbedding6 ∘ raw15559step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15559step0 raw15559step0Labels raw15559step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5350 node5350Labels := by rfl

def raw15560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15560step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15560 raw15560Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw15560 raw15560Labels = mixedMoment B raw15560step0 raw15560step0Labels := by
      have ha : raw15560step0 = (fun i j => raw15560 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15560step0 raw15560; decide +kernel
      have hl : raw15560step0Labels = raw15560Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15560 raw15560Labels permutation154 permutation3
    mixedMoment B raw15560step0 raw15560step0Labels = mixedMoment B raw15560step1 raw15560step1Labels := by
      have ha : raw15560step1 = raw15560step0 := by apply Matrix.ext; unfold raw15560step1 raw15560step0; decide +kernel
      have hl : raw15560step0Labels = labelEmbedding6 ∘ raw15560step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15560step0 raw15560step0Labels raw15560step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw15561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15561step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15561step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15561step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15561step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15561step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15561 raw15561Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw15561 raw15561Labels = mixedMoment B raw15561step0 raw15561step0Labels := by
      have ha : raw15561step0 = (fun i j => raw15561 (permutation225 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15561step0 raw15561; decide +kernel
      have hl : raw15561step0Labels = raw15561Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15561 raw15561Labels permutation225 permutation5
    mixedMoment B raw15561step0 raw15561step0Labels = mixedMoment B raw15561step1 raw15561step1Labels := by
      have ha : raw15561step1 = -raw15561step0 := by apply Matrix.ext; change ∀ i j, raw15561step1 i j = -(raw15561step0 i j); unfold raw15561step1 raw15561step0; decide +kernel
      have hl : raw15561step1Labels = raw15561step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15561step1 raw15561step1Labels = mixedMoment B raw15561step2 raw15561step2Labels := by
      have ha : raw15561step2 = raw15561step1 := by apply Matrix.ext; unfold raw15561step2 raw15561step1; decide +kernel
      have hl : raw15561step1Labels = labelEmbedding8 ∘ raw15561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15561step1 raw15561step1Labels raw15561step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw15562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15562step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15562 raw15562Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw15562 raw15562Labels = mixedMoment B raw15562step0 raw15562step0Labels := by
      have ha : raw15562step0 = (fun i j => raw15562 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15562step0 raw15562; decide +kernel
      have hl : raw15562step0Labels = raw15562Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15562 raw15562Labels permutation155 permutation3
    mixedMoment B raw15562step0 raw15562step0Labels = mixedMoment B raw15562step1 raw15562step1Labels := by
      have ha : raw15562step1 = raw15562step0 := by apply Matrix.ext; unfold raw15562step1 raw15562step0; decide +kernel
      have hl : raw15562step0Labels = labelEmbedding6 ∘ raw15562step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15562step0 raw15562step0Labels raw15562step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw15563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15563step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15563 raw15563Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw15563 raw15563Labels = mixedMoment B raw15563step0 raw15563step0Labels := by
      have ha : raw15563step0 = (fun i j => raw15563 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15563step0 raw15563; decide +kernel
      have hl : raw15563step0Labels = raw15563Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15563 raw15563Labels permutation152 permutation3
    mixedMoment B raw15563step0 raw15563step0Labels = mixedMoment B raw15563step1 raw15563step1Labels := by
      have ha : raw15563step1 = raw15563step0 := by apply Matrix.ext; unfold raw15563step1 raw15563step0; decide +kernel
      have hl : raw15563step0Labels = labelEmbedding6 ∘ raw15563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15563step0 raw15563step0Labels raw15563step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw15564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15564 raw15564Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw15564 raw15564Labels = mixedMoment B raw15564step0 raw15564step0Labels := by
      have ha : raw15564step0 = (fun i j => raw15564 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15564step0 raw15564; decide +kernel
      have hl : raw15564step0Labels = raw15564Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15564 raw15564Labels permutation583 permutation2
    mixedMoment B raw15564step0 raw15564step0Labels = mixedMoment B raw15564step1 raw15564step1Labels := by
      have ha : raw15564step1 = -raw15564step0 := by apply Matrix.ext; change ∀ i j, raw15564step1 i j = -(raw15564step0 i j); unfold raw15564step1 raw15564step0; decide +kernel
      have hl : raw15564step1Labels = raw15564step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5348 node5348Labels := by rfl

def raw15565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15565 raw15565Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw15565 raw15565Labels = mixedMoment B raw15565step0 raw15565step0Labels := by
      have ha : raw15565step0 = (fun i j => raw15565 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15565step0 raw15565; decide +kernel
      have hl : raw15565step0Labels = raw15565Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15565 raw15565Labels permutation587 permutation2
    mixedMoment B raw15565step0 raw15565step0Labels = mixedMoment B raw15565step1 raw15565step1Labels := by
      have ha : raw15565step1 = -raw15565step0 := by apply Matrix.ext; change ∀ i j, raw15565step1 i j = -(raw15565step0 i j); unfold raw15565step1 raw15565step0; decide +kernel
      have hl : raw15565step1Labels = raw15565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw15566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15566 raw15566Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw15566 raw15566Labels = mixedMoment B raw15566step0 raw15566step0Labels := by
      have ha : raw15566step0 = (fun i j => raw15566 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15566step0 raw15566; decide +kernel
      have hl : raw15566step0Labels = raw15566Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15566 raw15566Labels permutation582 permutation2
    mixedMoment B raw15566step0 raw15566step0Labels = mixedMoment B raw15566step1 raw15566step1Labels := by
      have ha : raw15566step1 = -raw15566step0 := by apply Matrix.ext; change ∀ i j, raw15566step1 i j = -(raw15566step0 i j); unfold raw15566step1 raw15566step0; decide +kernel
      have hl : raw15566step1Labels = raw15566step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw15567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw15567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15567 raw15567Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw15567 raw15567Labels = mixedMoment B raw15567step0 raw15567step0Labels := by
      have ha : raw15567step0 = (fun i j => raw15567 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15567step0 raw15567; decide +kernel
      have hl : raw15567step0Labels = raw15567Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15567 raw15567Labels permutation584 permutation2
    mixedMoment B raw15567step0 raw15567step0Labels = mixedMoment B raw15567step1 raw15567step1Labels := by
      have ha : raw15567step1 = -raw15567step0 := by apply Matrix.ext; change ∀ i j, raw15567step1 i j = -(raw15567step0 i j); unfold raw15567step1 raw15567step0; decide +kernel
      have hl : raw15567step1Labels = raw15567step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw15568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw15568step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw15568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15568 raw15568Labels = mixedMoment B node4791 node4791Labels := by
  calc
    mixedMoment B raw15568 raw15568Labels = mixedMoment B raw15568step0 raw15568step0Labels := by
      have ha : raw15568step0 = (fun i j => raw15568 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15568step0 raw15568; decide +kernel
      have hl : raw15568step0Labels = raw15568Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15568 raw15568Labels permutation152 permutation3
    mixedMoment B raw15568step0 raw15568step0Labels = mixedMoment B raw15568step1 raw15568step1Labels := by
      have ha : raw15568step1 = raw15568step0 := by apply Matrix.ext; unfold raw15568step1 raw15568step0; decide +kernel
      have hl : raw15568step0Labels = labelEmbedding6 ∘ raw15568step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15568step0 raw15568step0Labels raw15568step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4791 node4791Labels := by rfl

def raw15569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw15569step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15569step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15569step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15569 raw15569Labels = mixedMoment B node5181 node5181Labels := by
  calc
    mixedMoment B raw15569 raw15569Labels = mixedMoment B raw15569step0 raw15569step0Labels := by
      have ha : raw15569step0 = (fun i j => raw15569 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15569step0 raw15569; decide +kernel
      have hl : raw15569step0Labels = raw15569Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15569 raw15569Labels permutation682 permutation3
    mixedMoment B raw15569step0 raw15569step0Labels = mixedMoment B raw15569step1 raw15569step1Labels := by
      have ha : raw15569step1 = -raw15569step0 := by apply Matrix.ext; change ∀ i j, raw15569step1 i j = -(raw15569step0 i j); unfold raw15569step1 raw15569step0; decide +kernel
      have hl : raw15569step1Labels = raw15569step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15569step1 raw15569step1Labels = mixedMoment B raw15569step2 raw15569step2Labels := by
      have ha : raw15569step2 = raw15569step1 := by apply Matrix.ext; unfold raw15569step2 raw15569step1; decide +kernel
      have hl : raw15569step1Labels = labelEmbedding6 ∘ raw15569step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15569step1 raw15569step1Labels raw15569step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5181 node5181Labels := by rfl

def raw15570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15570step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15570step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15570step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15570 raw15570Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw15570 raw15570Labels = mixedMoment B raw15570step0 raw15570step0Labels := by
      have ha : raw15570step0 = (fun i j => raw15570 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15570step0 raw15570; decide +kernel
      have hl : raw15570step0Labels = raw15570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15570 raw15570Labels permutation686 permutation3
    mixedMoment B raw15570step0 raw15570step0Labels = mixedMoment B raw15570step1 raw15570step1Labels := by
      have ha : raw15570step1 = -raw15570step0 := by apply Matrix.ext; change ∀ i j, raw15570step1 i j = -(raw15570step0 i j); unfold raw15570step1 raw15570step0; decide +kernel
      have hl : raw15570step1Labels = raw15570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15570step1 raw15570step1Labels = mixedMoment B raw15570step2 raw15570step2Labels := by
      have ha : raw15570step2 = raw15570step1 := by apply Matrix.ext; unfold raw15570step2 raw15570step1; decide +kernel
      have hl : raw15570step1Labels = labelEmbedding6 ∘ raw15570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15570step1 raw15570step1Labels raw15570step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5184 node5184Labels := by rfl

def raw15571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15571step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15571step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15571step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15571step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15571 raw15571Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw15571 raw15571Labels = mixedMoment B raw15571step0 raw15571step0Labels := by
      have ha : raw15571step0 = (fun i j => raw15571 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15571step0 raw15571; decide +kernel
      have hl : raw15571step0Labels = raw15571Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15571 raw15571Labels permutation680 permutation3
    mixedMoment B raw15571step0 raw15571step0Labels = mixedMoment B raw15571step1 raw15571step1Labels := by
      have ha : raw15571step1 = -raw15571step0 := by apply Matrix.ext; change ∀ i j, raw15571step1 i j = -(raw15571step0 i j); unfold raw15571step1 raw15571step0; decide +kernel
      have hl : raw15571step1Labels = raw15571step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15571step1 raw15571step1Labels = mixedMoment B raw15571step2 raw15571step2Labels := by
      have ha : raw15571step2 = raw15571step1 := by apply Matrix.ext; unfold raw15571step2 raw15571step1; decide +kernel
      have hl : raw15571step1Labels = labelEmbedding6 ∘ raw15571step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15571step1 raw15571step1Labels raw15571step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5184 node5184Labels := by rfl

def raw15572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw15572step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw15572step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15572step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw15572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15572 raw15572Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw15572 raw15572Labels = mixedMoment B raw15572step0 raw15572step0Labels := by
      have ha : raw15572step0 = (fun i j => raw15572 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15572step0 raw15572; decide +kernel
      have hl : raw15572step0Labels = raw15572Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15572 raw15572Labels permutation640 permutation3
    mixedMoment B raw15572step0 raw15572step0Labels = mixedMoment B raw15572step1 raw15572step1Labels := by
      have ha : raw15572step1 = -raw15572step0 := by apply Matrix.ext; change ∀ i j, raw15572step1 i j = -(raw15572step0 i j); unfold raw15572step1 raw15572step0; decide +kernel
      have hl : raw15572step1Labels = raw15572step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15572step1 raw15572step1Labels = mixedMoment B raw15572step2 raw15572step2Labels := by
      have ha : raw15572step2 = raw15572step1 := by apply Matrix.ext; unfold raw15572step2 raw15572step1; decide +kernel
      have hl : raw15572step1Labels = labelEmbedding6 ∘ raw15572step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15572step1 raw15572step1Labels raw15572step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw15573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15573 raw15573Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw15573 raw15573Labels = mixedMoment B raw15573step0 raw15573step0Labels := by
      have ha : raw15573step0 = (fun i j => raw15573 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15573step0 raw15573; decide +kernel
      have hl : raw15573step0Labels = raw15573Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15573 raw15573Labels permutation265 permutation3
    _ = mixedMoment B node3976 node3976Labels := by rfl

def raw15574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15574 raw15574Labels = mixedMoment B node4002 node4002Labels := by
  calc
    mixedMoment B raw15574 raw15574Labels = mixedMoment B raw15574step0 raw15574step0Labels := by
      have ha : raw15574step0 = (fun i j => raw15574 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15574step0 raw15574; decide +kernel
      have hl : raw15574step0Labels = raw15574Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15574 raw15574Labels permutation686 permutation3
    mixedMoment B raw15574step0 raw15574step0Labels = mixedMoment B raw15574step1 raw15574step1Labels := by
      have ha : raw15574step1 = -raw15574step0 := by apply Matrix.ext; change ∀ i j, raw15574step1 i j = -(raw15574step0 i j); unfold raw15574step1 raw15574step0; decide +kernel
      have hl : raw15574step1Labels = raw15574step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4002 node4002Labels := by rfl

def raw15575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15575 raw15575Labels = mixedMoment B node4002 node4002Labels := by
  calc
    mixedMoment B raw15575 raw15575Labels = mixedMoment B raw15575step0 raw15575step0Labels := by
      have ha : raw15575step0 = (fun i j => raw15575 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15575step0 raw15575; decide +kernel
      have hl : raw15575step0Labels = raw15575Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15575 raw15575Labels permutation680 permutation3
    mixedMoment B raw15575step0 raw15575step0Labels = mixedMoment B raw15575step1 raw15575step1Labels := by
      have ha : raw15575step1 = -raw15575step0 := by apply Matrix.ext; change ∀ i j, raw15575step1 i j = -(raw15575step0 i j); unfold raw15575step1 raw15575step0; decide +kernel
      have hl : raw15575step1Labels = raw15575step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4002 node4002Labels := by rfl

def raw15576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15576 raw15576Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw15576 raw15576Labels = mixedMoment B raw15576step0 raw15576step0Labels := by
      have ha : raw15576step0 = (fun i j => raw15576 (permutation569 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15576step0 raw15576; decide +kernel
      have hl : raw15576step0Labels = raw15576Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15576 raw15576Labels permutation569 permutation6
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw15577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15577 raw15577Labels = mixedMoment B node3992 node3992Labels := by
  calc
    mixedMoment B raw15577 raw15577Labels = mixedMoment B raw15577step0 raw15577step0Labels := by
      have ha : raw15577step0 = (fun i j => raw15577 (permutation569 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15577step0 raw15577; decide +kernel
      have hl : raw15577step0Labels = raw15577Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15577 raw15577Labels permutation569 permutation6
    _ = mixedMoment B node3992 node3992Labels := by rfl

def raw15578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15578 raw15578Labels = mixedMoment B node2232 node2232Labels := by
  calc
    mixedMoment B raw15578 raw15578Labels = mixedMoment B raw15578step0 raw15578step0Labels := by
      have ha : raw15578step0 = (fun i j => raw15578 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15578step0 raw15578; decide +kernel
      have hl : raw15578step0Labels = raw15578Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15578 raw15578Labels permutation152 permutation3
    _ = mixedMoment B node2232 node2232Labels := by rfl

def raw15579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15579 raw15579Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw15579 raw15579Labels = mixedMoment B raw15579step0 raw15579step0Labels := by
      have ha : raw15579step0 = (fun i j => raw15579 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15579step0 raw15579; decide +kernel
      have hl : raw15579step0Labels = raw15579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15579 raw15579Labels permutation176 permutation3
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw15580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15580 raw15580Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw15580 raw15580Labels = mixedMoment B raw15580step0 raw15580step0Labels := by
      have ha : raw15580step0 = (fun i j => raw15580 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15580step0 raw15580; decide +kernel
      have hl : raw15580step0Labels = raw15580Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15580 raw15580Labels permutation200 permutation3
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw15581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15581 raw15581Labels = mixedMoment B node3867 node3867Labels := by
  calc
    mixedMoment B raw15581 raw15581Labels = mixedMoment B raw15581step0 raw15581step0Labels := by
      have ha : raw15581step0 = (fun i j => raw15581 (permutation569 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15581step0 raw15581; decide +kernel
      have hl : raw15581step0Labels = raw15581Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15581 raw15581Labels permutation569 permutation6
    _ = mixedMoment B node3867 node3867Labels := by rfl

def raw15582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw15582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15582 raw15582Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw15582 raw15582Labels = mixedMoment B raw15582step0 raw15582step0Labels := by
      have ha : raw15582step0 = (fun i j => raw15582 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15582step0 raw15582; decide +kernel
      have hl : raw15582step0Labels = raw15582Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15582 raw15582Labels permutation152 permutation3
    _ = mixedMoment B node3909 node3909Labels := by rfl

def raw15583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15583 raw15583Labels = mixedMoment B node2017 node2017Labels := by
  calc
    mixedMoment B raw15583 raw15583Labels = mixedMoment B raw15583step0 raw15583step0Labels := by
      have ha : raw15583step0 = (fun i j => raw15583 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15583step0 raw15583; decide +kernel
      have hl : raw15583step0Labels = raw15583Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15583 raw15583Labels permutation160 permutation3
    _ = mixedMoment B node2017 node2017Labels := by rfl

def raw15584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15584 raw15584Labels = mixedMoment B node3688 node3688Labels := by
  calc
    mixedMoment B raw15584 raw15584Labels = mixedMoment B raw15584step0 raw15584step0Labels := by
      have ha : raw15584step0 = (fun i j => raw15584 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15584step0 raw15584; decide +kernel
      have hl : raw15584step0Labels = raw15584Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15584 raw15584Labels permutation160 permutation3
    _ = mixedMoment B node3688 node3688Labels := by rfl

def raw15585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15585 raw15585Labels = mixedMoment B node3819 node3819Labels := by
  calc
    mixedMoment B raw15585 raw15585Labels = mixedMoment B raw15585step0 raw15585step0Labels := by
      have ha : raw15585step0 = (fun i j => raw15585 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15585step0 raw15585; decide +kernel
      have hl : raw15585step0Labels = raw15585Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15585 raw15585Labels permutation160 permutation3
    _ = mixedMoment B node3819 node3819Labels := by rfl

def raw15586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15586step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15586 raw15586Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw15586 raw15586Labels = mixedMoment B raw15586step0 raw15586step0Labels := by
      have ha : raw15586step0 = (fun i j => raw15586 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15586step0 raw15586; decide +kernel
      have hl : raw15586step0Labels = raw15586Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15586 raw15586Labels permutation166 permutation3
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw15587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15587 raw15587Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw15587 raw15587Labels = mixedMoment B raw15587step0 raw15587step0Labels := by
      have ha : raw15587step0 = (fun i j => raw15587 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15587step0 raw15587; decide +kernel
      have hl : raw15587step0Labels = raw15587Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15587 raw15587Labels permutation161 permutation3
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw15588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15588 raw15588Labels = mixedMoment B node2017 node2017Labels := by
  calc
    mixedMoment B raw15588 raw15588Labels = mixedMoment B raw15588step0 raw15588step0Labels := by
      have ha : raw15588step0 = (fun i j => raw15588 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15588step0 raw15588; decide +kernel
      have hl : raw15588step0Labels = raw15588Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15588 raw15588Labels permutation154 permutation3
    _ = mixedMoment B node2017 node2017Labels := by rfl

def raw15589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15589 raw15589Labels = mixedMoment B node3688 node3688Labels := by
  calc
    mixedMoment B raw15589 raw15589Labels = mixedMoment B raw15589step0 raw15589step0Labels := by
      have ha : raw15589step0 = (fun i j => raw15589 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15589step0 raw15589; decide +kernel
      have hl : raw15589step0Labels = raw15589Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15589 raw15589Labels permutation154 permutation3
    _ = mixedMoment B node3688 node3688Labels := by rfl

def raw15590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15590 raw15590Labels = mixedMoment B node3819 node3819Labels := by
  calc
    mixedMoment B raw15590 raw15590Labels = mixedMoment B raw15590step0 raw15590step0Labels := by
      have ha : raw15590step0 = (fun i j => raw15590 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15590step0 raw15590; decide +kernel
      have hl : raw15590step0Labels = raw15590Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15590 raw15590Labels permutation154 permutation3
    _ = mixedMoment B node3819 node3819Labels := by rfl

def raw15591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15591 raw15591Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw15591 raw15591Labels = mixedMoment B raw15591step0 raw15591step0Labels := by
      have ha : raw15591step0 = (fun i j => raw15591 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15591step0 raw15591; decide +kernel
      have hl : raw15591step0Labels = raw15591Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15591 raw15591Labels permutation164 permutation3
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw15592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15592step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15592 raw15592Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw15592 raw15592Labels = mixedMoment B raw15592step0 raw15592step0Labels := by
      have ha : raw15592step0 = (fun i j => raw15592 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15592step0 raw15592; decide +kernel
      have hl : raw15592step0Labels = raw15592Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15592 raw15592Labels permutation155 permutation3
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw15593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15593 raw15593Labels = mixedMoment B node2012 node2012Labels := by
  calc
    mixedMoment B raw15593 raw15593Labels = mixedMoment B raw15593step0 raw15593step0Labels := by
      have ha : raw15593step0 = (fun i j => raw15593 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15593step0 raw15593; decide +kernel
      have hl : raw15593step0Labels = raw15593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15593 raw15593Labels permutation152 permutation3
    _ = mixedMoment B node2012 node2012Labels := by rfl

def raw15594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15594 raw15594Labels = mixedMoment B node3685 node3685Labels := by
  calc
    mixedMoment B raw15594 raw15594Labels = mixedMoment B raw15594step0 raw15594step0Labels := by
      have ha : raw15594step0 = (fun i j => raw15594 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15594step0 raw15594; decide +kernel
      have hl : raw15594step0Labels = raw15594Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15594 raw15594Labels permutation152 permutation3
    _ = mixedMoment B node3685 node3685Labels := by rfl

def raw15595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15595step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15595 raw15595Labels = mixedMoment B node3818 node3818Labels := by
  calc
    mixedMoment B raw15595 raw15595Labels = mixedMoment B raw15595step0 raw15595step0Labels := by
      have ha : raw15595step0 = (fun i j => raw15595 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15595step0 raw15595; decide +kernel
      have hl : raw15595step0Labels = raw15595Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15595 raw15595Labels permutation152 permutation3
    _ = mixedMoment B node3818 node3818Labels := by rfl

def raw15596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15596 raw15596Labels = mixedMoment B node3818 node3818Labels := by
  calc
    mixedMoment B raw15596 raw15596Labels = mixedMoment B raw15596step0 raw15596step0Labels := by
      have ha : raw15596step0 = (fun i j => raw15596 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15596step0 raw15596; decide +kernel
      have hl : raw15596step0Labels = raw15596Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15596 raw15596Labels permutation158 permutation3
    _ = mixedMoment B node3818 node3818Labels := by rfl

def raw15597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw15597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15597 raw15597Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw15597 raw15597Labels = mixedMoment B raw15597step0 raw15597step0Labels := by
      have ha : raw15597step0 = (fun i j => raw15597 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15597step0 raw15597; decide +kernel
      have hl : raw15597step0Labels = raw15597Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15597 raw15597Labels permutation153 permutation3
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw15598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw15598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15598 raw15598Labels = mixedMoment B node2008 node2008Labels := by
  calc
    mixedMoment B raw15598 raw15598Labels = mixedMoment B raw15598step0 raw15598step0Labels := by
      have ha : raw15598step0 = (fun i j => raw15598 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15598step0 raw15598; decide +kernel
      have hl : raw15598step0Labels = raw15598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15598 raw15598Labels permutation152 permutation3
    _ = mixedMoment B node2008 node2008Labels := by rfl

def raw15599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw15599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15599 raw15599Labels = mixedMoment B node2609 node2609Labels := by
  calc
    mixedMoment B raw15599 raw15599Labels = mixedMoment B raw15599step0 raw15599step0Labels := by
      have ha : raw15599step0 = (fun i j => raw15599 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15599step0 raw15599; decide +kernel
      have hl : raw15599step0Labels = raw15599Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15599 raw15599Labels permutation682 permutation3
    mixedMoment B raw15599step0 raw15599step0Labels = mixedMoment B raw15599step1 raw15599step1Labels := by
      have ha : raw15599step1 = -raw15599step0 := by apply Matrix.ext; change ∀ i j, raw15599step1 i j = -(raw15599step0 i j); unfold raw15599step1 raw15599step0; decide +kernel
      have hl : raw15599step1Labels = raw15599step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2609 node2609Labels := by rfl

def raw15600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15600 raw15600Labels = mixedMoment B node2614 node2614Labels := by
  calc
    mixedMoment B raw15600 raw15600Labels = mixedMoment B raw15600step0 raw15600step0Labels := by
      have ha : raw15600step0 = (fun i j => raw15600 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15600step0 raw15600; decide +kernel
      have hl : raw15600step0Labels = raw15600Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15600 raw15600Labels permutation686 permutation3
    mixedMoment B raw15600step0 raw15600step0Labels = mixedMoment B raw15600step1 raw15600step1Labels := by
      have ha : raw15600step1 = -raw15600step0 := by apply Matrix.ext; change ∀ i j, raw15600step1 i j = -(raw15600step0 i j); unfold raw15600step1 raw15600step0; decide +kernel
      have hl : raw15600step1Labels = raw15600step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2614 node2614Labels := by rfl

def raw15601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15601 raw15601Labels = mixedMoment B node2614 node2614Labels := by
  calc
    mixedMoment B raw15601 raw15601Labels = mixedMoment B raw15601step0 raw15601step0Labels := by
      have ha : raw15601step0 = (fun i j => raw15601 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15601step0 raw15601; decide +kernel
      have hl : raw15601step0Labels = raw15601Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15601 raw15601Labels permutation680 permutation3
    mixedMoment B raw15601step0 raw15601step0Labels = mixedMoment B raw15601step1 raw15601step1Labels := by
      have ha : raw15601step1 = -raw15601step0 := by apply Matrix.ext; change ∀ i j, raw15601step1 i j = -(raw15601step0 i j); unfold raw15601step1 raw15601step0; decide +kernel
      have hl : raw15601step1Labels = raw15601step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2614 node2614Labels := by rfl

def raw15602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw15602step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw15602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15602 raw15602Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw15602 raw15602Labels = mixedMoment B raw15602step0 raw15602step0Labels := by
      have ha : raw15602step0 = (fun i j => raw15602 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15602step0 raw15602; decide +kernel
      have hl : raw15602step0Labels = raw15602Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15602 raw15602Labels permutation640 permutation3
    mixedMoment B raw15602step0 raw15602step0Labels = mixedMoment B raw15602step1 raw15602step1Labels := by
      have ha : raw15602step1 = -raw15602step0 := by apply Matrix.ext; change ∀ i j, raw15602step1 i j = -(raw15602step0 i j); unfold raw15602step1 raw15602step0; decide +kernel
      have hl : raw15602step1Labels = raw15602step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw15603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15603step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15603step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15603 raw15603Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw15603 raw15603Labels = mixedMoment B raw15603step0 raw15603step0Labels := by
      have ha : raw15603step0 = (fun i j => raw15603 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15603step0 raw15603; decide +kernel
      have hl : raw15603step0Labels = raw15603Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15603 raw15603Labels permutation572 permutation7
    mixedMoment B raw15603step0 raw15603step0Labels = mixedMoment B raw15603step1 raw15603step1Labels := by
      have ha : raw15603step1 = raw15603step0 := by apply Matrix.ext; unfold raw15603step1 raw15603step0; decide +kernel
      have hl : raw15603step0Labels = labelEmbedding1 ∘ raw15603step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15603step0 raw15603step0Labels raw15603step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3956 node3956Labels := by rfl

def raw15604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15604 raw15604Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw15604 raw15604Labels = mixedMoment B raw15604step0 raw15604step0Labels := by
      have ha : raw15604step0 = (fun i j => raw15604 (permutation573 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15604step0 raw15604; decide +kernel
      have hl : raw15604step0Labels = raw15604Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15604 raw15604Labels permutation573 permutation7
    mixedMoment B raw15604step0 raw15604step0Labels = mixedMoment B raw15604step1 raw15604step1Labels := by
      have ha : raw15604step1 = raw15604step0 := by apply Matrix.ext; unfold raw15604step1 raw15604step0; decide +kernel
      have hl : raw15604step0Labels = labelEmbedding1 ∘ raw15604step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15604step0 raw15604step0Labels raw15604step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw15605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15605step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15605 raw15605Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw15605 raw15605Labels = mixedMoment B raw15605step0 raw15605step0Labels := by
      have ha : raw15605step0 = (fun i j => raw15605 (permutation571 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15605step0 raw15605; decide +kernel
      have hl : raw15605step0Labels = raw15605Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15605 raw15605Labels permutation571 permutation7
    mixedMoment B raw15605step0 raw15605step0Labels = mixedMoment B raw15605step1 raw15605step1Labels := by
      have ha : raw15605step1 = raw15605step0 := by apply Matrix.ext; unfold raw15605step1 raw15605step0; decide +kernel
      have hl : raw15605step0Labels = labelEmbedding1 ∘ raw15605step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15605step0 raw15605step0Labels raw15605step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw15606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15606 raw15606Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw15606 raw15606Labels = mixedMoment B raw15606step0 raw15606step0Labels := by
      have ha : raw15606step0 = (fun i j => raw15606 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15606step0 raw15606; decide +kernel
      have hl : raw15606step0Labels = raw15606Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15606 raw15606Labels permutation572 permutation7
    mixedMoment B raw15606step0 raw15606step0Labels = mixedMoment B raw15606step1 raw15606step1Labels := by
      have ha : raw15606step1 = raw15606step0 := by apply Matrix.ext; unfold raw15606step1 raw15606step0; decide +kernel
      have hl : raw15606step0Labels = labelEmbedding1 ∘ raw15606step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15606step0 raw15606step0Labels raw15606step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw15607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15607step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15607 raw15607Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw15607 raw15607Labels = mixedMoment B raw15607step0 raw15607step0Labels := by
      have ha : raw15607step0 = (fun i j => raw15607 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15607step0 raw15607; decide +kernel
      have hl : raw15607step0Labels = raw15607Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15607 raw15607Labels permutation572 permutation7
    mixedMoment B raw15607step0 raw15607step0Labels = mixedMoment B raw15607step1 raw15607step1Labels := by
      have ha : raw15607step1 = raw15607step0 := by apply Matrix.ext; unfold raw15607step1 raw15607step0; decide +kernel
      have hl : raw15607step0Labels = labelEmbedding1 ∘ raw15607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15607step0 raw15607step0Labels raw15607step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw15608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15608step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15608 raw15608Labels = mixedMoment B node2104 node2104Labels := by
  calc
    mixedMoment B raw15608 raw15608Labels = mixedMoment B raw15608step0 raw15608step0Labels := by
      have ha : raw15608step0 = (fun i j => raw15608 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15608step0 raw15608; decide +kernel
      have hl : raw15608step0Labels = raw15608Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15608 raw15608Labels permutation224 permutation5
    mixedMoment B raw15608step0 raw15608step0Labels = mixedMoment B raw15608step1 raw15608step1Labels := by
      have ha : raw15608step1 = -raw15608step0 := by apply Matrix.ext; change ∀ i j, raw15608step1 i j = -(raw15608step0 i j); unfold raw15608step1 raw15608step0; decide +kernel
      have hl : raw15608step1Labels = raw15608step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15608step1 raw15608step1Labels = mixedMoment B raw15608step2 raw15608step2Labels := by
      have ha : raw15608step2 = raw15608step1 := by apply Matrix.ext; unfold raw15608step2 raw15608step1; decide +kernel
      have hl : raw15608step1Labels = labelEmbedding1 ∘ raw15608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15608step1 raw15608step1Labels raw15608step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2104 node2104Labels := by rfl

def raw15609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15609step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15609step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15609 raw15609Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw15609 raw15609Labels = mixedMoment B raw15609step0 raw15609step0Labels := by
      have ha : raw15609step0 = (fun i j => raw15609 (permutation230 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15609step0 raw15609; decide +kernel
      have hl : raw15609step0Labels = raw15609Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15609 raw15609Labels permutation230 permutation5
    mixedMoment B raw15609step0 raw15609step0Labels = mixedMoment B raw15609step1 raw15609step1Labels := by
      have ha : raw15609step1 = -raw15609step0 := by apply Matrix.ext; change ∀ i j, raw15609step1 i j = -(raw15609step0 i j); unfold raw15609step1 raw15609step0; decide +kernel
      have hl : raw15609step1Labels = raw15609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15609step1 raw15609step1Labels = mixedMoment B raw15609step2 raw15609step2Labels := by
      have ha : raw15609step2 = raw15609step1 := by apply Matrix.ext; unfold raw15609step2 raw15609step1; decide +kernel
      have hl : raw15609step1Labels = labelEmbedding1 ∘ raw15609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15609step1 raw15609step1Labels raw15609step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw15610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15610 raw15610Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw15610 raw15610Labels = mixedMoment B raw15610step0 raw15610step0Labels := by
      have ha : raw15610step0 = (fun i j => raw15610 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15610step0 raw15610; decide +kernel
      have hl : raw15610step0Labels = raw15610Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15610 raw15610Labels permutation234 permutation5
    mixedMoment B raw15610step0 raw15610step0Labels = mixedMoment B raw15610step1 raw15610step1Labels := by
      have ha : raw15610step1 = -raw15610step0 := by apply Matrix.ext; change ∀ i j, raw15610step1 i j = -(raw15610step0 i j); unfold raw15610step1 raw15610step0; decide +kernel
      have hl : raw15610step1Labels = raw15610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15610step1 raw15610step1Labels = mixedMoment B raw15610step2 raw15610step2Labels := by
      have ha : raw15610step2 = raw15610step1 := by apply Matrix.ext; unfold raw15610step2 raw15610step1; decide +kernel
      have hl : raw15610step1Labels = labelEmbedding1 ∘ raw15610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15610step1 raw15610step1Labels raw15610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw15611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15611step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15611step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15611 raw15611Labels = mixedMoment B node3734 node3734Labels := by
  calc
    mixedMoment B raw15611 raw15611Labels = mixedMoment B raw15611step0 raw15611step0Labels := by
      have ha : raw15611step0 = (fun i j => raw15611 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15611step0 raw15611; decide +kernel
      have hl : raw15611step0Labels = raw15611Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15611 raw15611Labels permutation224 permutation5
    mixedMoment B raw15611step0 raw15611step0Labels = mixedMoment B raw15611step1 raw15611step1Labels := by
      have ha : raw15611step1 = -raw15611step0 := by apply Matrix.ext; change ∀ i j, raw15611step1 i j = -(raw15611step0 i j); unfold raw15611step1 raw15611step0; decide +kernel
      have hl : raw15611step1Labels = raw15611step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15611step1 raw15611step1Labels = mixedMoment B raw15611step2 raw15611step2Labels := by
      have ha : raw15611step2 = raw15611step1 := by apply Matrix.ext; unfold raw15611step2 raw15611step1; decide +kernel
      have hl : raw15611step1Labels = labelEmbedding1 ∘ raw15611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15611step1 raw15611step1Labels raw15611step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3734 node3734Labels := by rfl

def raw15612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw15612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15612step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15612step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw15612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15612 raw15612Labels = mixedMoment B node3882 node3882Labels := by
  calc
    mixedMoment B raw15612 raw15612Labels = mixedMoment B raw15612step0 raw15612step0Labels := by
      have ha : raw15612step0 = (fun i j => raw15612 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15612step0 raw15612; decide +kernel
      have hl : raw15612step0Labels = raw15612Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15612 raw15612Labels permutation240 permutation5
    mixedMoment B raw15612step0 raw15612step0Labels = mixedMoment B raw15612step1 raw15612step1Labels := by
      have ha : raw15612step1 = -raw15612step0 := by apply Matrix.ext; change ∀ i j, raw15612step1 i j = -(raw15612step0 i j); unfold raw15612step1 raw15612step0; decide +kernel
      have hl : raw15612step1Labels = raw15612step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15612step1 raw15612step1Labels = mixedMoment B raw15612step2 raw15612step2Labels := by
      have ha : raw15612step2 = raw15612step1 := by apply Matrix.ext; unfold raw15612step2 raw15612step1; decide +kernel
      have hl : raw15612step1Labels = labelEmbedding1 ∘ raw15612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15612step1 raw15612step1Labels raw15612step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3882 node3882Labels := by rfl

def raw15613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15613step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15613step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15613 raw15613Labels = mixedMoment B node2076 node2076Labels := by
  calc
    mixedMoment B raw15613 raw15613Labels = mixedMoment B raw15613step0 raw15613step0Labels := by
      have ha : raw15613step0 = (fun i j => raw15613 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15613step0 raw15613; decide +kernel
      have hl : raw15613step0Labels = raw15613Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15613 raw15613Labels permutation227 permutation5
    mixedMoment B raw15613step0 raw15613step0Labels = mixedMoment B raw15613step1 raw15613step1Labels := by
      have ha : raw15613step1 = -raw15613step0 := by apply Matrix.ext; change ∀ i j, raw15613step1 i j = -(raw15613step0 i j); unfold raw15613step1 raw15613step0; decide +kernel
      have hl : raw15613step1Labels = raw15613step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15613step1 raw15613step1Labels = mixedMoment B raw15613step2 raw15613step2Labels := by
      have ha : raw15613step2 = raw15613step1 := by apply Matrix.ext; unfold raw15613step2 raw15613step1; decide +kernel
      have hl : raw15613step1Labels = labelEmbedding1 ∘ raw15613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15613step1 raw15613step1Labels raw15613step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2076 node2076Labels := by rfl

def raw15614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15614 raw15614Labels = mixedMoment B node3750 node3750Labels := by
  calc
    mixedMoment B raw15614 raw15614Labels = mixedMoment B raw15614step0 raw15614step0Labels := by
      have ha : raw15614step0 = (fun i j => raw15614 (permutation167 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15614step0 raw15614; decide +kernel
      have hl : raw15614step0Labels = raw15614Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15614 raw15614Labels permutation167 permutation5
    mixedMoment B raw15614step0 raw15614step0Labels = mixedMoment B raw15614step1 raw15614step1Labels := by
      have ha : raw15614step1 = -raw15614step0 := by apply Matrix.ext; change ∀ i j, raw15614step1 i j = -(raw15614step0 i j); unfold raw15614step1 raw15614step0; decide +kernel
      have hl : raw15614step1Labels = raw15614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15614step1 raw15614step1Labels = mixedMoment B raw15614step2 raw15614step2Labels := by
      have ha : raw15614step2 = raw15614step1 := by apply Matrix.ext; unfold raw15614step2 raw15614step1; decide +kernel
      have hl : raw15614step1Labels = labelEmbedding1 ∘ raw15614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15614step1 raw15614step1Labels raw15614step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3750 node3750Labels := by rfl

def raw15615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15615step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15615step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15615step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15615 raw15615Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw15615 raw15615Labels = mixedMoment B raw15615step0 raw15615step0Labels := by
      have ha : raw15615step0 = (fun i j => raw15615 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15615step0 raw15615; decide +kernel
      have hl : raw15615step0Labels = raw15615Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15615 raw15615Labels permutation227 permutation5
    mixedMoment B raw15615step0 raw15615step0Labels = mixedMoment B raw15615step1 raw15615step1Labels := by
      have ha : raw15615step1 = -raw15615step0 := by apply Matrix.ext; change ∀ i j, raw15615step1 i j = -(raw15615step0 i j); unfold raw15615step1 raw15615step0; decide +kernel
      have hl : raw15615step1Labels = raw15615step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15615step1 raw15615step1Labels = mixedMoment B raw15615step2 raw15615step2Labels := by
      have ha : raw15615step2 = raw15615step1 := by apply Matrix.ext; unfold raw15615step2 raw15615step1; decide +kernel
      have hl : raw15615step1Labels = labelEmbedding1 ∘ raw15615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15615step1 raw15615step1Labels raw15615step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
