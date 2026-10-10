import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26368 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw26368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw26368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw26368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26368 raw26368Labels = mixedMoment B node3072 node3072Labels := by
  calc
    mixedMoment B raw26368 raw26368Labels = mixedMoment B raw26368step0 raw26368step0Labels := by
      have hz : ∀ j, raw26368 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26368step0 = (fun i j => raw26368 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26368step0 raw26368; decide +kernel
      have hl : raw26368step0Labels = raw26368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26368 raw26368Labels permutation265 hz
    mixedMoment B raw26368step0 raw26368step0Labels = mixedMoment B raw26368step1 raw26368step1Labels := by
      have ha : raw26368step1 = (fun i j => raw26368step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26368step1 raw26368step0; decide +kernel
      have hl : raw26368step1Labels = raw26368step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26368step0 raw26368step0Labels permutation137 permutation4
    _ = mixedMoment B node3072 node3072Labels := by rfl

def raw26369 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26369 raw26369Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw26369 raw26369Labels = mixedMoment B raw26369step0 raw26369step0Labels := by
      have hz : ∀ j, raw26369 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26369step0 = (fun i j => raw26369 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26369step0 raw26369; decide +kernel
      have hl : raw26369step0Labels = raw26369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26369 raw26369Labels permutation265 hz
    mixedMoment B raw26369step0 raw26369step0Labels = mixedMoment B raw26369step1 raw26369step1Labels := by
      have ha : raw26369step1 = (fun i j => raw26369step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26369step1 raw26369step0; decide +kernel
      have hl : raw26369step1Labels = raw26369step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26369step0 raw26369step0Labels permutation50 permutation2
    mixedMoment B raw26369step1 raw26369step1Labels = mixedMoment B raw26369step2 raw26369step2Labels := by
      have ha : raw26369step2 = -raw26369step1 := by apply Matrix.ext; change ∀ i j, raw26369step2 i j = -(raw26369step1 i j); unfold raw26369step2 raw26369step1; decide +kernel
      have hl : raw26369step2Labels = raw26369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3304 node3304Labels := by rfl

def raw26370 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw26370Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26370step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw26370step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26370step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26370step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26370 raw26370Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw26370 raw26370Labels = mixedMoment B raw26370step0 raw26370step0Labels := by
      have hz : ∀ j, raw26370 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26370step0 = (fun i j => raw26370 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26370step0 raw26370; decide +kernel
      have hl : raw26370step0Labels = raw26370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26370 raw26370Labels permutation265 hz
    mixedMoment B raw26370step0 raw26370step0Labels = mixedMoment B raw26370step1 raw26370step1Labels := by
      have ha : raw26370step1 = -raw26370step0 := by apply Matrix.ext; change ∀ i j, raw26370step1 i j = -(raw26370step0 i j); unfold raw26370step1 raw26370step0; decide +kernel
      have hl : raw26370step1Labels = raw26370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw26371 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw26371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26371 raw26371Labels = mixedMoment B node1698 node1698Labels := by
  calc
    mixedMoment B raw26371 raw26371Labels = mixedMoment B raw26371step0 raw26371step0Labels := by
      have ha : raw26371step0 = (fun i j => raw26371 (permutation184 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26371step0 raw26371; decide +kernel
      have hl : raw26371step0Labels = raw26371Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26371 raw26371Labels permutation184 permutation4
    mixedMoment B raw26371step0 raw26371step0Labels = mixedMoment B raw26371step1 raw26371step1Labels := by
      have ha : raw26371step1 = -raw26371step0 := by apply Matrix.ext; change ∀ i j, raw26371step1 i j = -(raw26371step0 i j); unfold raw26371step1 raw26371step0; decide +kernel
      have hl : raw26371step1Labels = raw26371step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1698 node1698Labels := by rfl

def raw26372 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26372 raw26372Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw26372 raw26372Labels = mixedMoment B raw26372step0 raw26372step0Labels := by
      have hz : ∀ j, raw26372 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26372step0 = (fun i j => raw26372 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26372step0 raw26372; decide +kernel
      have hl : raw26372step0Labels = raw26372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26372 raw26372Labels permutation265 hz
    mixedMoment B raw26372step0 raw26372step0Labels = mixedMoment B raw26372step1 raw26372step1Labels := by
      have ha : raw26372step1 = (fun i j => raw26372step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26372step1 raw26372step0; decide +kernel
      have hl : raw26372step1Labels = raw26372step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26372step0 raw26372step0Labels permutation40 permutation4
    mixedMoment B raw26372step1 raw26372step1Labels = mixedMoment B raw26372step2 raw26372step2Labels := by
      have ha : raw26372step2 = -raw26372step1 := by apply Matrix.ext; change ∀ i j, raw26372step2 i j = -(raw26372step1 i j); unfold raw26372step2 raw26372step1; decide +kernel
      have hl : raw26372step2Labels = raw26372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw26373 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26373 raw26373Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw26373 raw26373Labels = mixedMoment B raw26373step0 raw26373step0Labels := by
      have hz : ∀ j, raw26373 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26373step0 = (fun i j => raw26373 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26373step0 raw26373; decide +kernel
      have hl : raw26373step0Labels = raw26373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26373 raw26373Labels permutation265 hz
    mixedMoment B raw26373step0 raw26373step0Labels = mixedMoment B raw26373step1 raw26373step1Labels := by
      have ha : raw26373step1 = (fun i j => raw26373step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26373step1 raw26373step0; decide +kernel
      have hl : raw26373step1Labels = raw26373step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26373step0 raw26373step0Labels permutation34 permutation4
    mixedMoment B raw26373step1 raw26373step1Labels = mixedMoment B raw26373step2 raw26373step2Labels := by
      have ha : raw26373step2 = -raw26373step1 := by apply Matrix.ext; change ∀ i j, raw26373step2 i j = -(raw26373step1 i j); unfold raw26373step2 raw26373step1; decide +kernel
      have hl : raw26373step2Labels = raw26373step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw26374 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26374 raw26374Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw26374 raw26374Labels = mixedMoment B raw26374step0 raw26374step0Labels := by
      have hz : ∀ j, raw26374 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26374step0 = (fun i j => raw26374 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26374step0 raw26374; decide +kernel
      have hl : raw26374step0Labels = raw26374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26374 raw26374Labels permutation265 hz
    mixedMoment B raw26374step0 raw26374step0Labels = mixedMoment B raw26374step1 raw26374step1Labels := by
      have ha : raw26374step1 = (fun i j => raw26374step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26374step1 raw26374step0; decide +kernel
      have hl : raw26374step1Labels = raw26374step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26374step0 raw26374step0Labels permutation32 permutation4
    mixedMoment B raw26374step1 raw26374step1Labels = mixedMoment B raw26374step2 raw26374step2Labels := by
      have ha : raw26374step2 = -raw26374step1 := by apply Matrix.ext; change ∀ i j, raw26374step2 i j = -(raw26374step1 i j); unfold raw26374step2 raw26374step1; decide +kernel
      have hl : raw26374step2Labels = raw26374step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw26375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26375 raw26375Labels = mixedMoment B node597 node597Labels := by
  calc
    mixedMoment B raw26375 raw26375Labels = mixedMoment B raw26375step0 raw26375step0Labels := by
      have ha : raw26375step0 = (fun i j => raw26375 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26375step0 raw26375; decide +kernel
      have hl : raw26375step0Labels = raw26375Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26375 raw26375Labels permutation184 permutation2
    _ = mixedMoment B node597 node597Labels := by rfl

def raw26376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26376 raw26376Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw26376 raw26376Labels = mixedMoment B raw26376step0 raw26376step0Labels := by
      have hz : ∀ j, raw26376 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26376step0 = (fun i j => raw26376 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26376step0 raw26376; decide +kernel
      have hl : raw26376step0Labels = raw26376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26376 raw26376Labels permutation434 hz
    mixedMoment B raw26376step0 raw26376step0Labels = mixedMoment B raw26376step1 raw26376step1Labels := by
      have ha : raw26376step1 = (fun i j => raw26376step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26376step1 raw26376step0; decide +kernel
      have hl : raw26376step1Labels = raw26376step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26376step0 raw26376step0Labels permutation40 permutation2
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw26377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26377 raw26377Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw26377 raw26377Labels = mixedMoment B raw26377step0 raw26377step0Labels := by
      have hz : ∀ j, raw26377 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26377step0 = (fun i j => raw26377 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26377step0 raw26377; decide +kernel
      have hl : raw26377step0Labels = raw26377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26377 raw26377Labels permutation520 hz
    mixedMoment B raw26377step0 raw26377step0Labels = mixedMoment B raw26377step1 raw26377step1Labels := by
      have ha : raw26377step1 = (fun i j => raw26377step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26377step1 raw26377step0; decide +kernel
      have hl : raw26377step1Labels = raw26377step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26377step0 raw26377step0Labels permutation40 permutation2
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw26378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26378 raw26378Labels = mixedMoment B node1056 node1056Labels := by
  calc
    mixedMoment B raw26378 raw26378Labels = mixedMoment B raw26378step0 raw26378step0Labels := by
      have ha : raw26378step0 = (fun i j => raw26378 (permutation255 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26378step0 raw26378; decide +kernel
      have hl : raw26378step0Labels = raw26378Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26378 raw26378Labels permutation255 permutation2
    _ = mixedMoment B node1056 node1056Labels := by rfl

def raw26379 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26379 raw26379Labels = mixedMoment B node3286 node3286Labels := by
  calc
    mixedMoment B raw26379 raw26379Labels = mixedMoment B raw26379step0 raw26379step0Labels := by
      have ha : raw26379step0 = (fun i j => raw26379 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26379step0 raw26379; decide +kernel
      have hl : raw26379step0Labels = raw26379Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26379 raw26379Labels permutation173 permutation2
    mixedMoment B raw26379step0 raw26379step0Labels = mixedMoment B raw26379step1 raw26379step1Labels := by
      have ha : raw26379step1 = -raw26379step0 := by apply Matrix.ext; change ∀ i j, raw26379step1 i j = -(raw26379step0 i j); unfold raw26379step1 raw26379step0; decide +kernel
      have hl : raw26379step1Labels = raw26379step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3286 node3286Labels := by rfl

def raw26380 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26380 raw26380Labels = mixedMoment B node3286 node3286Labels := by
  calc
    mixedMoment B raw26380 raw26380Labels = mixedMoment B raw26380step0 raw26380step0Labels := by
      have ha : raw26380step0 = (fun i j => raw26380 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26380step0 raw26380; decide +kernel
      have hl : raw26380step0Labels = raw26380Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26380 raw26380Labels permutation171 permutation2
    mixedMoment B raw26380step0 raw26380step0Labels = mixedMoment B raw26380step1 raw26380step1Labels := by
      have ha : raw26380step1 = -raw26380step0 := by apply Matrix.ext; change ∀ i j, raw26380step1 i j = -(raw26380step0 i j); unfold raw26380step1 raw26380step0; decide +kernel
      have hl : raw26380step1Labels = raw26380step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3286 node3286Labels := by rfl

def raw26381 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw26381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26381 raw26381Labels = mixedMoment B node3286 node3286Labels := by
  calc
    mixedMoment B raw26381 raw26381Labels = mixedMoment B raw26381step0 raw26381step0Labels := by
      have ha : raw26381step0 = (fun i j => raw26381 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26381step0 raw26381; decide +kernel
      have hl : raw26381step0Labels = raw26381Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26381 raw26381Labels permutation170 permutation2
    mixedMoment B raw26381step0 raw26381step0Labels = mixedMoment B raw26381step1 raw26381step1Labels := by
      have ha : raw26381step1 = -raw26381step0 := by apply Matrix.ext; change ∀ i j, raw26381step1 i j = -(raw26381step0 i j); unfold raw26381step1 raw26381step0; decide +kernel
      have hl : raw26381step1Labels = raw26381step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3286 node3286Labels := by rfl

def raw26382 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26382 raw26382Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw26382 raw26382Labels = mixedMoment B raw26382step0 raw26382step0Labels := by
      have ha : raw26382step0 = (fun i j => raw26382 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26382step0 raw26382; decide +kernel
      have hl : raw26382step0Labels = raw26382Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26382 raw26382Labels permutation170 permutation2
    mixedMoment B raw26382step0 raw26382step0Labels = mixedMoment B raw26382step1 raw26382step1Labels := by
      have ha : raw26382step1 = -raw26382step0 := by apply Matrix.ext; change ∀ i j, raw26382step1 i j = -(raw26382step0 i j); unfold raw26382step1 raw26382step0; decide +kernel
      have hl : raw26382step1Labels = raw26382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3292 node3292Labels := by rfl

def raw26383 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw26383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26383 raw26383Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw26383 raw26383Labels = mixedMoment B raw26383step0 raw26383step0Labels := by
      have ha : raw26383step0 = (fun i j => raw26383 (permutation185 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26383step0 raw26383; decide +kernel
      have hl : raw26383step0Labels = raw26383Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26383 raw26383Labels permutation185 permutation4
    mixedMoment B raw26383step0 raw26383step0Labels = mixedMoment B raw26383step1 raw26383step1Labels := by
      have ha : raw26383step1 = -raw26383step0 := by apply Matrix.ext; change ∀ i j, raw26383step1 i j = -(raw26383step0 i j); unfold raw26383step1 raw26383step0; decide +kernel
      have hl : raw26383step1Labels = raw26383step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1699 node1699Labels := by rfl

def raw26384 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26384 raw26384Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26384 raw26384Labels = mixedMoment B raw26384step0 raw26384step0Labels := by
      have ha : raw26384step0 = (fun i j => raw26384 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26384step0 raw26384; decide +kernel
      have hl : raw26384step0Labels = raw26384Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26384 raw26384Labels permutation212 permutation4
    mixedMoment B raw26384step0 raw26384step0Labels = mixedMoment B raw26384step1 raw26384step1Labels := by
      have ha : raw26384step1 = -raw26384step0 := by apply Matrix.ext; change ∀ i j, raw26384step1 i j = -(raw26384step0 i j); unfold raw26384step1 raw26384step0; decide +kernel
      have hl : raw26384step1Labels = raw26384step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1706 node1706Labels := by rfl

def raw26385 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26385step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26385 raw26385Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26385 raw26385Labels = mixedMoment B raw26385step0 raw26385step0Labels := by
      have ha : raw26385step0 = (fun i j => raw26385 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26385step0 raw26385; decide +kernel
      have hl : raw26385step0Labels = raw26385Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26385 raw26385Labels permutation188 permutation4
    mixedMoment B raw26385step0 raw26385step0Labels = mixedMoment B raw26385step1 raw26385step1Labels := by
      have ha : raw26385step1 = -raw26385step0 := by apply Matrix.ext; change ∀ i j, raw26385step1 i j = -(raw26385step0 i j); unfold raw26385step1 raw26385step0; decide +kernel
      have hl : raw26385step1Labels = raw26385step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1706 node1706Labels := by rfl

def raw26386 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26386 raw26386Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26386 raw26386Labels = mixedMoment B raw26386step0 raw26386step0Labels := by
      have ha : raw26386step0 = (fun i j => raw26386 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26386step0 raw26386; decide +kernel
      have hl : raw26386step0Labels = raw26386Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26386 raw26386Labels permutation182 permutation4
    mixedMoment B raw26386step0 raw26386step0Labels = mixedMoment B raw26386step1 raw26386step1Labels := by
      have ha : raw26386step1 = -raw26386step0 := by apply Matrix.ext; change ∀ i j, raw26386step1 i j = -(raw26386step0 i j); unfold raw26386step1 raw26386step0; decide +kernel
      have hl : raw26386step1Labels = raw26386step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1706 node1706Labels := by rfl

def raw26387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26387 raw26387Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw26387 raw26387Labels = mixedMoment B raw26387step0 raw26387step0Labels := by
      have ha : raw26387step0 = (fun i j => raw26387 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26387step0 raw26387; decide +kernel
      have hl : raw26387step0Labels = raw26387Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26387 raw26387Labels permutation170 permutation2
    _ = mixedMoment B node2880 node2880Labels := by rfl

def raw26388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26388 raw26388Labels = mixedMoment B node1366 node1366Labels := by
  calc
    mixedMoment B raw26388 raw26388Labels = mixedMoment B raw26388step0 raw26388step0Labels := by
      have ha : raw26388step0 = (fun i j => raw26388 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26388step0 raw26388; decide +kernel
      have hl : raw26388step0Labels = raw26388Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26388 raw26388Labels permutation170 permutation2
    _ = mixedMoment B node1366 node1366Labels := by rfl

def raw26389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26389 raw26389Labels = mixedMoment B node1316 node1316Labels := by
  calc
    mixedMoment B raw26389 raw26389Labels = mixedMoment B raw26389step0 raw26389step0Labels := by
      have ha : raw26389step0 = (fun i j => raw26389 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26389step0 raw26389; decide +kernel
      have hl : raw26389step0Labels = raw26389Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26389 raw26389Labels permutation173 permutation2
    _ = mixedMoment B node1316 node1316Labels := by rfl

def raw26390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26390step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26390 raw26390Labels = mixedMoment B node1316 node1316Labels := by
  calc
    mixedMoment B raw26390 raw26390Labels = mixedMoment B raw26390step0 raw26390step0Labels := by
      have ha : raw26390step0 = (fun i j => raw26390 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26390step0 raw26390; decide +kernel
      have hl : raw26390step0Labels = raw26390Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26390 raw26390Labels permutation171 permutation2
    _ = mixedMoment B node1316 node1316Labels := by rfl

def raw26391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26391 raw26391Labels = mixedMoment B node1316 node1316Labels := by
  calc
    mixedMoment B raw26391 raw26391Labels = mixedMoment B raw26391step0 raw26391step0Labels := by
      have ha : raw26391step0 = (fun i j => raw26391 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26391step0 raw26391; decide +kernel
      have hl : raw26391step0Labels = raw26391Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26391 raw26391Labels permutation170 permutation2
    _ = mixedMoment B node1316 node1316Labels := by rfl

def raw26392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26392 raw26392Labels = mixedMoment B node1319 node1319Labels := by
  calc
    _ = mixedMoment B node1319 node1319Labels := by rfl

def raw26393 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw26393Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26393step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw26393step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26393step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw26393step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26393 raw26393Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw26393 raw26393Labels = mixedMoment B raw26393step0 raw26393step0Labels := by
      have hz : ∀ j, raw26393 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26393step0 = (fun i j => raw26393 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26393step0 raw26393; decide +kernel
      have hl : raw26393step0Labels = raw26393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26393 raw26393Labels permutation590 hz
    mixedMoment B raw26393step0 raw26393step0Labels = mixedMoment B raw26393step1 raw26393step1Labels := by
      have ha : raw26393step1 = (fun i j => raw26393step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26393step1 raw26393step0; decide +kernel
      have hl : raw26393step1Labels = raw26393step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26393step0 raw26393step0Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw26394 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26394 raw26394Labels = mixedMoment B node3239 node3239Labels := by
  calc
    mixedMoment B raw26394 raw26394Labels = mixedMoment B raw26394step0 raw26394step0Labels := by
      have ha : raw26394step0 = (fun i j => raw26394 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26394step0 raw26394; decide +kernel
      have hl : raw26394step0Labels = raw26394Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26394 raw26394Labels permutation173 permutation2
    mixedMoment B raw26394step0 raw26394step0Labels = mixedMoment B raw26394step1 raw26394step1Labels := by
      have ha : raw26394step1 = -raw26394step0 := by apply Matrix.ext; change ∀ i j, raw26394step1 i j = -(raw26394step0 i j); unfold raw26394step1 raw26394step0; decide +kernel
      have hl : raw26394step1Labels = raw26394step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3239 node3239Labels := by rfl

def raw26395 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw26395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26395 raw26395Labels = mixedMoment B node3239 node3239Labels := by
  calc
    mixedMoment B raw26395 raw26395Labels = mixedMoment B raw26395step0 raw26395step0Labels := by
      have ha : raw26395step0 = (fun i j => raw26395 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26395step0 raw26395; decide +kernel
      have hl : raw26395step0Labels = raw26395Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26395 raw26395Labels permutation171 permutation2
    mixedMoment B raw26395step0 raw26395step0Labels = mixedMoment B raw26395step1 raw26395step1Labels := by
      have ha : raw26395step1 = -raw26395step0 := by apply Matrix.ext; change ∀ i j, raw26395step1 i j = -(raw26395step0 i j); unfold raw26395step1 raw26395step0; decide +kernel
      have hl : raw26395step1Labels = raw26395step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3239 node3239Labels := by rfl

def raw26396 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw26396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26396 raw26396Labels = mixedMoment B node3239 node3239Labels := by
  calc
    mixedMoment B raw26396 raw26396Labels = mixedMoment B raw26396step0 raw26396step0Labels := by
      have ha : raw26396step0 = (fun i j => raw26396 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26396step0 raw26396; decide +kernel
      have hl : raw26396step0Labels = raw26396Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26396 raw26396Labels permutation170 permutation2
    mixedMoment B raw26396step0 raw26396step0Labels = mixedMoment B raw26396step1 raw26396step1Labels := by
      have ha : raw26396step1 = -raw26396step0 := by apply Matrix.ext; change ∀ i j, raw26396step1 i j = -(raw26396step0 i j); unfold raw26396step1 raw26396step0; decide +kernel
      have hl : raw26396step1Labels = raw26396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3239 node3239Labels := by rfl

def raw26397 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26397 raw26397Labels = mixedMoment B node3244 node3244Labels := by
  calc
    mixedMoment B raw26397 raw26397Labels = mixedMoment B raw26397step0 raw26397step0Labels := by
      have ha : raw26397step0 = -raw26397 := by apply Matrix.ext; change ∀ i j, raw26397step0 i j = -(raw26397 i j); unfold raw26397step0 raw26397; decide +kernel
      have hl : raw26397step0Labels = raw26397Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3244 node3244Labels := by rfl

def raw26398 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw26398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw26398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26398 raw26398Labels = mixedMoment B node1696 node1696Labels := by
  calc
    mixedMoment B raw26398 raw26398Labels = mixedMoment B raw26398step0 raw26398step0Labels := by
      have ha : raw26398step0 = (fun i j => raw26398 (permutation185 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26398step0 raw26398; decide +kernel
      have hl : raw26398step0Labels = raw26398Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26398 raw26398Labels permutation185 permutation4
    mixedMoment B raw26398step0 raw26398step0Labels = mixedMoment B raw26398step1 raw26398step1Labels := by
      have ha : raw26398step1 = -raw26398step0 := by apply Matrix.ext; change ∀ i j, raw26398step1 i j = -(raw26398step0 i j); unfold raw26398step1 raw26398step0; decide +kernel
      have hl : raw26398step1Labels = raw26398step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1696 node1696Labels := by rfl

def raw26399 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw26399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26399 raw26399Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw26399 raw26399Labels = mixedMoment B raw26399step0 raw26399step0Labels := by
      have ha : raw26399step0 = (fun i j => raw26399 (permutation217 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26399step0 raw26399; decide +kernel
      have hl : raw26399step0Labels = raw26399Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26399 raw26399Labels permutation217 permutation4
    mixedMoment B raw26399step0 raw26399step0Labels = mixedMoment B raw26399step1 raw26399step1Labels := by
      have ha : raw26399step1 = -raw26399step0 := by apply Matrix.ext; change ∀ i j, raw26399step1 i j = -(raw26399step0 i j); unfold raw26399step1 raw26399step0; decide +kernel
      have hl : raw26399step1Labels = raw26399step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1699 node1699Labels := by rfl

def raw26400 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw26400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26400 raw26400Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw26400 raw26400Labels = mixedMoment B raw26400step0 raw26400step0Labels := by
      have ha : raw26400step0 = (fun i j => raw26400 (permutation193 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26400step0 raw26400; decide +kernel
      have hl : raw26400step0Labels = raw26400Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26400 raw26400Labels permutation193 permutation4
    mixedMoment B raw26400step0 raw26400step0Labels = mixedMoment B raw26400step1 raw26400step1Labels := by
      have ha : raw26400step1 = -raw26400step0 := by apply Matrix.ext; change ∀ i j, raw26400step1 i j = -(raw26400step0 i j); unfold raw26400step1 raw26400step0; decide +kernel
      have hl : raw26400step1Labels = raw26400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1699 node1699Labels := by rfl

def raw26401 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw26401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26401 raw26401Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw26401 raw26401Labels = mixedMoment B raw26401step0 raw26401step0Labels := by
      have ha : raw26401step0 = (fun i j => raw26401 (permutation187 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26401step0 raw26401; decide +kernel
      have hl : raw26401step0Labels = raw26401Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26401 raw26401Labels permutation187 permutation4
    mixedMoment B raw26401step0 raw26401step0Labels = mixedMoment B raw26401step1 raw26401step1Labels := by
      have ha : raw26401step1 = -raw26401step0 := by apply Matrix.ext; change ∀ i j, raw26401step1 i j = -(raw26401step0 i j); unfold raw26401step1 raw26401step0; decide +kernel
      have hl : raw26401step1Labels = raw26401step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1699 node1699Labels := by rfl

def raw26402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26402 raw26402Labels = mixedMoment B node1350 node1350Labels := by
  calc
    _ = mixedMoment B node1350 node1350Labels := by rfl

def raw26403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26403 raw26403Labels = mixedMoment B node2839 node2839Labels := by
  calc
    _ = mixedMoment B node2839 node2839Labels := by rfl

def raw26404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26404 raw26404Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw26404 raw26404Labels = mixedMoment B raw26404step0 raw26404step0Labels := by
      have ha : raw26404step0 = (fun i j => raw26404 (permutation317 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26404step0 raw26404; decide +kernel
      have hl : raw26404step0Labels = raw26404Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26404 raw26404Labels permutation317 permutation4
    _ = mixedMoment B node2234 node2234Labels := by rfl

def raw26405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26405 raw26405Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw26405 raw26405Labels = mixedMoment B raw26405step0 raw26405step0Labels := by
      have ha : raw26405step0 = (fun i j => raw26405 (permutation302 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26405step0 raw26405; decide +kernel
      have hl : raw26405step0Labels = raw26405Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26405 raw26405Labels permutation302 permutation4
    _ = mixedMoment B node2234 node2234Labels := by rfl

def raw26406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw26406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26406 raw26406Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw26406 raw26406Labels = mixedMoment B raw26406step0 raw26406step0Labels := by
      have ha : raw26406step0 = (fun i j => raw26406 (permutation298 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26406step0 raw26406; decide +kernel
      have hl : raw26406step0Labels = raw26406Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26406 raw26406Labels permutation298 permutation4
    _ = mixedMoment B node2234 node2234Labels := by rfl

def raw26407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw26407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26407 raw26407Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw26407 raw26407Labels = mixedMoment B raw26407step0 raw26407step0Labels := by
      have ha : raw26407step0 = (fun i j => raw26407 (permutation297 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26407step0 raw26407; decide +kernel
      have hl : raw26407step0Labels = raw26407Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26407 raw26407Labels permutation297 permutation4
    _ = mixedMoment B node2234 node2234Labels := by rfl

def raw26408 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26408Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26408step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26408step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26408 raw26408Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw26408 raw26408Labels = mixedMoment B raw26408step0 raw26408step0Labels := by
      have ha : raw26408step0 = (fun i j => raw26408 (permutation265 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26408step0 raw26408; decide +kernel
      have hl : raw26408step0Labels = raw26408Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26408 raw26408Labels permutation265 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

def raw26409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26409 raw26409Labels = mixedMoment B node1256 node1256Labels := by
  calc
    mixedMoment B raw26409 raw26409Labels = mixedMoment B raw26409step0 raw26409step0Labels := by
      have ha : raw26409step0 = (fun i j => raw26409 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26409step0 raw26409; decide +kernel
      have hl : raw26409step0Labels = raw26409Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26409 raw26409Labels permutation170 permutation2
    _ = mixedMoment B node1256 node1256Labels := by rfl

def raw26410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26410 raw26410Labels = mixedMoment B node2628 node2628Labels := by
  calc
    mixedMoment B raw26410 raw26410Labels = mixedMoment B raw26410step0 raw26410step0Labels := by
      have ha : raw26410step0 = (fun i j => raw26410 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26410step0 raw26410; decide +kernel
      have hl : raw26410step0Labels = raw26410Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26410 raw26410Labels permutation170 permutation2
    _ = mixedMoment B node2628 node2628Labels := by rfl

def raw26411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw26411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26411 raw26411Labels = mixedMoment B node2747 node2747Labels := by
  calc
    mixedMoment B raw26411 raw26411Labels = mixedMoment B raw26411step0 raw26411step0Labels := by
      have ha : raw26411step0 = (fun i j => raw26411 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26411step0 raw26411; decide +kernel
      have hl : raw26411step0Labels = raw26411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26411 raw26411Labels permutation156 permutation2
    _ = mixedMoment B node2747 node2747Labels := by rfl

def raw26412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw26412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26412 raw26412Labels = mixedMoment B node2747 node2747Labels := by
  calc
    mixedMoment B raw26412 raw26412Labels = mixedMoment B raw26412step0 raw26412step0Labels := by
      have ha : raw26412step0 = (fun i j => raw26412 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26412step0 raw26412; decide +kernel
      have hl : raw26412step0Labels = raw26412Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26412 raw26412Labels permutation162 permutation2
    _ = mixedMoment B node2747 node2747Labels := by rfl

def raw26413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -3, 2]]
def raw26413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw26413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26413 raw26413Labels = mixedMoment B node2747 node2747Labels := by
  calc
    mixedMoment B raw26413 raw26413Labels = mixedMoment B raw26413step0 raw26413step0Labels := by
      have ha : raw26413step0 = (fun i j => raw26413 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26413step0 raw26413; decide +kernel
      have hl : raw26413step0Labels = raw26413Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26413 raw26413Labels permutation168 permutation2
    _ = mixedMoment B node2747 node2747Labels := by rfl

def raw26414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2]]
def raw26414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26414 raw26414Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw26414 raw26414Labels = mixedMoment B raw26414step0 raw26414step0Labels := by
      have ha : raw26414step0 = (fun i j => raw26414 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26414step0 raw26414; decide +kernel
      have hl : raw26414step0Labels = raw26414Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26414 raw26414Labels permutation246 permutation2
    _ = mixedMoment B node2671 node2671Labels := by rfl

def raw26415 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![-2, 2]]
def raw26415Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26415step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26415step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26415 raw26415Labels = mixedMoment B node4087 node4087Labels := by
  calc
    mixedMoment B raw26415 raw26415Labels = mixedMoment B raw26415step0 raw26415step0Labels := by
      have ha : raw26415step0 = (fun i j => raw26415 (permutation246 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26415step0 raw26415; decide +kernel
      have hl : raw26415step0Labels = raw26415Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26415 raw26415Labels permutation246 permutation0
    _ = mixedMoment B node4087 node4087Labels := by rfl

def raw26416 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26416 raw26416Labels = mixedMoment B node1644 node1644Labels := by
  calc
    mixedMoment B raw26416 raw26416Labels = mixedMoment B raw26416step0 raw26416step0Labels := by
      have ha : raw26416step0 = (fun i j => raw26416 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26416step0 raw26416; decide +kernel
      have hl : raw26416step0Labels = raw26416Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26416 raw26416Labels permutation246 permutation2
    mixedMoment B raw26416step0 raw26416step0Labels = mixedMoment B raw26416step1 raw26416step1Labels := by
      have ha : raw26416step1 = -raw26416step0 := by apply Matrix.ext; change ∀ i j, raw26416step1 i j = -(raw26416step0 i j); unfold raw26416step1 raw26416step0; decide +kernel
      have hl : raw26416step1Labels = raw26416step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1644 node1644Labels := by rfl

def raw26417 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26417 raw26417Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26417 raw26417Labels = mixedMoment B raw26417step0 raw26417step0Labels := by
      have ha : raw26417step0 = (fun i j => raw26417 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26417step0 raw26417; decide +kernel
      have hl : raw26417step0Labels = raw26417Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26417 raw26417Labels permutation160 permutation4
    mixedMoment B raw26417step0 raw26417step0Labels = mixedMoment B raw26417step1 raw26417step1Labels := by
      have ha : raw26417step1 = -raw26417step0 := by apply Matrix.ext; change ∀ i j, raw26417step1 i j = -(raw26417step0 i j); unfold raw26417step1 raw26417step0; decide +kernel
      have hl : raw26417step1Labels = raw26417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw26418 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26418 raw26418Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26418 raw26418Labels = mixedMoment B raw26418step0 raw26418step0Labels := by
      have ha : raw26418step0 = (fun i j => raw26418 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26418step0 raw26418; decide +kernel
      have hl : raw26418step0Labels = raw26418Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26418 raw26418Labels permutation154 permutation4
    mixedMoment B raw26418step0 raw26418step0Labels = mixedMoment B raw26418step1 raw26418step1Labels := by
      have ha : raw26418step1 = -raw26418step0 := by apply Matrix.ext; change ∀ i j, raw26418step1 i j = -(raw26418step0 i j); unfold raw26418step1 raw26418step0; decide +kernel
      have hl : raw26418step1Labels = raw26418step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw26419 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26419 raw26419Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26419 raw26419Labels = mixedMoment B raw26419step0 raw26419step0Labels := by
      have ha : raw26419step0 = (fun i j => raw26419 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26419step0 raw26419; decide +kernel
      have hl : raw26419step0Labels = raw26419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26419 raw26419Labels permutation152 permutation4
    mixedMoment B raw26419step0 raw26419step0Labels = mixedMoment B raw26419step1 raw26419step1Labels := by
      have ha : raw26419step1 = -raw26419step0 := by apply Matrix.ext; change ∀ i j, raw26419step1 i j = -(raw26419step0 i j); unfold raw26419step1 raw26419step0; decide +kernel
      have hl : raw26419step1Labels = raw26419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw26420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26420 raw26420Labels = mixedMoment B node2508 node2508Labels := by
  calc
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw26421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26421 raw26421Labels = mixedMoment B node1233 node1233Labels := by
  calc
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw26422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26422 raw26422Labels = mixedMoment B node1130 node1130Labels := by
  calc
    mixedMoment B raw26422 raw26422Labels = mixedMoment B raw26422step0 raw26422step0Labels := by
      have ha : raw26422step0 = (fun i j => raw26422 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26422step0 raw26422; decide +kernel
      have hl : raw26422step0Labels = raw26422Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26422 raw26422Labels permutation161 permutation2
    _ = mixedMoment B node1130 node1130Labels := by rfl

def raw26423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26423 raw26423Labels = mixedMoment B node1130 node1130Labels := by
  calc
    mixedMoment B raw26423 raw26423Labels = mixedMoment B raw26423step0 raw26423step0Labels := by
      have ha : raw26423step0 = (fun i j => raw26423 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26423step0 raw26423; decide +kernel
      have hl : raw26423step0Labels = raw26423Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26423 raw26423Labels permutation155 permutation2
    _ = mixedMoment B node1130 node1130Labels := by rfl

def raw26424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 1, -2]]
def raw26424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26424 raw26424Labels = mixedMoment B node1127 node1127Labels := by
  calc
    mixedMoment B raw26424 raw26424Labels = mixedMoment B raw26424step0 raw26424step0Labels := by
      have ha : raw26424step0 = (fun i j => raw26424 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26424step0 raw26424; decide +kernel
      have hl : raw26424step0Labels = raw26424Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26424 raw26424Labels permutation153 permutation2
    _ = mixedMoment B node1127 node1127Labels := by rfl

def raw26425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26425 raw26425Labels = mixedMoment B node1126 node1126Labels := by
  calc
    _ = mixedMoment B node1126 node1126Labels := by rfl

def raw26426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26426 raw26426Labels = mixedMoment B node637 node637Labels := by
  calc
    mixedMoment B raw26426 raw26426Labels = mixedMoment B raw26426step0 raw26426step0Labels := by
      have ha : raw26426step0 = (fun i j => raw26426 (permutation260 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26426step0 raw26426; decide +kernel
      have hl : raw26426step0Labels = raw26426Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26426 raw26426Labels permutation260 permutation2
    _ = mixedMoment B node637 node637Labels := by rfl

def raw26427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26427 raw26427Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw26427 raw26427Labels = mixedMoment B raw26427step0 raw26427step0Labels := by
      have ha : raw26427step0 = (fun i j => raw26427 (permutation174 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26427step0 raw26427; decide +kernel
      have hl : raw26427step0Labels = raw26427Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26427 raw26427Labels permutation174 permutation2
    _ = mixedMoment B node1260 node1260Labels := by rfl

def raw26428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26428 raw26428Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw26428 raw26428Labels = mixedMoment B raw26428step0 raw26428step0Labels := by
      have ha : raw26428step0 = (fun i j => raw26428 (permutation198 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26428step0 raw26428; decide +kernel
      have hl : raw26428step0Labels = raw26428Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26428 raw26428Labels permutation198 permutation2
    _ = mixedMoment B node1260 node1260Labels := by rfl

def raw26429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26429 raw26429Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw26429 raw26429Labels = mixedMoment B raw26429step0 raw26429step0Labels := by
      have ha : raw26429step0 = (fun i j => raw26429 (permutation222 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26429step0 raw26429; decide +kernel
      have hl : raw26429step0Labels = raw26429Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26429 raw26429Labels permutation222 permutation2
    _ = mixedMoment B node1260 node1260Labels := by rfl

def raw26430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1]]
def raw26430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26430 raw26430Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw26430 raw26430Labels = mixedMoment B raw26430step0 raw26430step0Labels := by
      have hz : ∀ j, raw26430 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26430step0 = (fun i j => raw26430 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26430step0 raw26430; decide +kernel
      have hl : raw26430step0Labels = raw26430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26430 raw26430Labels permutation520 hz
    mixedMoment B raw26430step0 raw26430step0Labels = mixedMoment B raw26430step1 raw26430step1Labels := by
      have ha : raw26430step1 = (fun i j => raw26430step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26430step1 raw26430step0; decide +kernel
      have hl : raw26430step1Labels = raw26430step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26430step0 raw26430step0Labels permutation50 permutation2
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw26431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1]]
def raw26431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26431 raw26431Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw26431 raw26431Labels = mixedMoment B raw26431step0 raw26431step0Labels := by
      have ha : raw26431step0 = (fun i j => raw26431 (permutation260 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26431step0 raw26431; decide +kernel
      have hl : raw26431step0Labels = raw26431Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26431 raw26431Labels permutation260 permutation2
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw26432 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]
def raw26432Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26432step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]
def raw26432step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26432step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw26432step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26432 raw26432Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw26432 raw26432Labels = mixedMoment B raw26432step0 raw26432step0Labels := by
      have hz : ∀ j, raw26432 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26432step0 = (fun i j => raw26432 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26432step0 raw26432; decide +kernel
      have hl : raw26432step0Labels = raw26432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26432 raw26432Labels permutation520 hz
    mixedMoment B raw26432step0 raw26432step0Labels = mixedMoment B raw26432step1 raw26432step1Labels := by
      have ha : raw26432step1 = (fun i j => raw26432step0 (permutation50 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26432step1 raw26432step0; decide +kernel
      have hl : raw26432step1Labels = raw26432step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26432step0 raw26432step0Labels permutation50 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw26433 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw26433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26433 raw26433Labels = mixedMoment B node1638 node1638Labels := by
  calc
    mixedMoment B raw26433 raw26433Labels = mixedMoment B raw26433step0 raw26433step0Labels := by
      have ha : raw26433step0 = (fun i j => raw26433 (permutation263 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26433step0 raw26433; decide +kernel
      have hl : raw26433step0Labels = raw26433Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26433 raw26433Labels permutation263 permutation2
    mixedMoment B raw26433step0 raw26433step0Labels = mixedMoment B raw26433step1 raw26433step1Labels := by
      have ha : raw26433step1 = -raw26433step0 := by apply Matrix.ext; change ∀ i j, raw26433step1 i j = -(raw26433step0 i j); unfold raw26433step1 raw26433step0; decide +kernel
      have hl : raw26433step1Labels = raw26433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1638 node1638Labels := by rfl

def raw26434 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw26434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26434 raw26434Labels = mixedMoment B node1636 node1636Labels := by
  calc
    mixedMoment B raw26434 raw26434Labels = mixedMoment B raw26434step0 raw26434step0Labels := by
      have ha : raw26434step0 = (fun i j => raw26434 (permutation261 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26434step0 raw26434; decide +kernel
      have hl : raw26434step0Labels = raw26434Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26434 raw26434Labels permutation261 permutation2
    mixedMoment B raw26434step0 raw26434step0Labels = mixedMoment B raw26434step1 raw26434step1Labels := by
      have ha : raw26434step1 = -raw26434step0 := by apply Matrix.ext; change ∀ i j, raw26434step1 i j = -(raw26434step0 i j); unfold raw26434step1 raw26434step0; decide +kernel
      have hl : raw26434step1Labels = raw26434step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1636 node1636Labels := by rfl

def raw26435 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw26435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26435 raw26435Labels = mixedMoment B node1636 node1636Labels := by
  calc
    mixedMoment B raw26435 raw26435Labels = mixedMoment B raw26435step0 raw26435step0Labels := by
      have ha : raw26435step0 = (fun i j => raw26435 (permutation260 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26435step0 raw26435; decide +kernel
      have hl : raw26435step0Labels = raw26435Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26435 raw26435Labels permutation260 permutation2
    mixedMoment B raw26435step0 raw26435step0Labels = mixedMoment B raw26435step1 raw26435step1Labels := by
      have ha : raw26435step1 = -raw26435step0 := by apply Matrix.ext; change ∀ i j, raw26435step1 i j = -(raw26435step0 i j); unfold raw26435step1 raw26435step0; decide +kernel
      have hl : raw26435step1Labels = raw26435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1636 node1636Labels := by rfl

def raw26436 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26436 raw26436Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26436 raw26436Labels = mixedMoment B raw26436step0 raw26436step0Labels := by
      have ha : raw26436step0 = (fun i j => raw26436 (permutation240 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26436step0 raw26436; decide +kernel
      have hl : raw26436step0Labels = raw26436Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26436 raw26436Labels permutation240 permutation2
    mixedMoment B raw26436step0 raw26436step0Labels = mixedMoment B raw26436step1 raw26436step1Labels := by
      have ha : raw26436step1 = -raw26436step0 := by apply Matrix.ext; change ∀ i j, raw26436step1 i j = -(raw26436step0 i j); unfold raw26436step1 raw26436step0; decide +kernel
      have hl : raw26436step1Labels = raw26436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1706 node1706Labels := by rfl

def raw26437 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26437 raw26437Labels = mixedMoment B node1600 node1600Labels := by
  calc
    mixedMoment B raw26437 raw26437Labels = mixedMoment B raw26437step0 raw26437step0Labels := by
      have ha : raw26437step0 = (fun i j => raw26437 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26437step0 raw26437; decide +kernel
      have hl : raw26437step0Labels = raw26437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26437 raw26437Labels permutation158 permutation4
    mixedMoment B raw26437step0 raw26437step0Labels = mixedMoment B raw26437step1 raw26437step1Labels := by
      have ha : raw26437step1 = -raw26437step0 := by apply Matrix.ext; change ∀ i j, raw26437step1 i j = -(raw26437step0 i j); unfold raw26437step1 raw26437step0; decide +kernel
      have hl : raw26437step1Labels = raw26437step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1600 node1600Labels := by rfl

def raw26438 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26438 raw26438Labels = mixedMoment B node1600 node1600Labels := by
  calc
    mixedMoment B raw26438 raw26438Labels = mixedMoment B raw26438step0 raw26438step0Labels := by
      have ha : raw26438step0 = (fun i j => raw26438 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26438step0 raw26438; decide +kernel
      have hl : raw26438step0Labels = raw26438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26438 raw26438Labels permutation152 permutation4
    mixedMoment B raw26438step0 raw26438step0Labels = mixedMoment B raw26438step1 raw26438step1Labels := by
      have ha : raw26438step1 = -raw26438step0 := by apply Matrix.ext; change ∀ i j, raw26438step1 i j = -(raw26438step0 i j); unfold raw26438step1 raw26438step0; decide +kernel
      have hl : raw26438step1Labels = raw26438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1600 node1600Labels := by rfl

def raw26439 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -2, 1]]
def raw26439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw26439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26439step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26439 raw26439Labels = mixedMoment B node1595 node1595Labels := by
  calc
    mixedMoment B raw26439 raw26439Labels = mixedMoment B raw26439step0 raw26439step0Labels := by
      have ha : raw26439step0 = (fun i j => raw26439 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26439step0 raw26439; decide +kernel
      have hl : raw26439step0Labels = raw26439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26439 raw26439Labels permutation152 permutation4
    mixedMoment B raw26439step0 raw26439step0Labels = mixedMoment B raw26439step1 raw26439step1Labels := by
      have ha : raw26439step1 = -raw26439step0 := by apply Matrix.ext; change ∀ i j, raw26439step1 i j = -(raw26439step0 i j); unfold raw26439step1 raw26439step0; decide +kernel
      have hl : raw26439step1Labels = raw26439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1595 node1595Labels := by rfl

def raw26440 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -3, 1]]
def raw26440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw26440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26440 raw26440Labels = mixedMoment B node1593 node1593Labels := by
  calc
    mixedMoment B raw26440 raw26440Labels = mixedMoment B raw26440step0 raw26440step0Labels := by
      have ha : raw26440step0 = (fun i j => raw26440 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26440step0 raw26440; decide +kernel
      have hl : raw26440step0Labels = raw26440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26440 raw26440Labels permutation152 permutation4
    mixedMoment B raw26440step0 raw26440step0Labels = mixedMoment B raw26440step1 raw26440step1Labels := by
      have ha : raw26440step1 = -raw26440step0 := by apply Matrix.ext; change ∀ i j, raw26440step1 i j = -(raw26440step0 i j); unfold raw26440step1 raw26440step0; decide +kernel
      have hl : raw26440step1Labels = raw26440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1593 node1593Labels := by rfl

def raw26441 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26441 raw26441Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw26441 raw26441Labels = mixedMoment B raw26441step0 raw26441step0Labels := by
      have hz : ∀ j, raw26441 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26441step0 = (fun i j => raw26441 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26441step0 raw26441; decide +kernel
      have hl : raw26441step0Labels = raw26441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26441 raw26441Labels permutation265 hz
    mixedMoment B raw26441step0 raw26441step0Labels = mixedMoment B raw26441step1 raw26441step1Labels := by
      have ha : raw26441step1 = (fun i j => raw26441step0 (permutation55 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26441step1 raw26441step0; decide +kernel
      have hl : raw26441step1Labels = raw26441step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26441step0 raw26441step0Labels permutation55 permutation2
    mixedMoment B raw26441step1 raw26441step1Labels = mixedMoment B raw26441step2 raw26441step2Labels := by
      have ha : raw26441step2 = -raw26441step1 := by apply Matrix.ext; change ∀ i j, raw26441step2 i j = -(raw26441step1 i j); unfold raw26441step2 raw26441step1; decide +kernel
      have hl : raw26441step2Labels = raw26441step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3303 node3303Labels := by rfl

def raw26442 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26442 raw26442Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw26442 raw26442Labels = mixedMoment B raw26442step0 raw26442step0Labels := by
      have hz : ∀ j, raw26442 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26442step0 = (fun i j => raw26442 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26442step0 raw26442; decide +kernel
      have hl : raw26442step0Labels = raw26442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26442 raw26442Labels permutation265 hz
    mixedMoment B raw26442step0 raw26442step0Labels = mixedMoment B raw26442step1 raw26442step1Labels := by
      have ha : raw26442step1 = (fun i j => raw26442step0 (permutation54 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26442step1 raw26442step0; decide +kernel
      have hl : raw26442step1Labels = raw26442step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26442step0 raw26442step0Labels permutation54 permutation2
    mixedMoment B raw26442step1 raw26442step1Labels = mixedMoment B raw26442step2 raw26442step2Labels := by
      have ha : raw26442step2 = -raw26442step1 := by apply Matrix.ext; change ∀ i j, raw26442step2 i j = -(raw26442step1 i j); unfold raw26442step2 raw26442step1; decide +kernel
      have hl : raw26442step2Labels = raw26442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3303 node3303Labels := by rfl

def raw26443 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26443step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26443 raw26443Labels = mixedMoment B node3307 node3307Labels := by
  calc
    mixedMoment B raw26443 raw26443Labels = mixedMoment B raw26443step0 raw26443step0Labels := by
      have hz : ∀ j, raw26443 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26443step0 = (fun i j => raw26443 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26443step0 raw26443; decide +kernel
      have hl : raw26443step0Labels = raw26443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26443 raw26443Labels permutation265 hz
    mixedMoment B raw26443step0 raw26443step0Labels = mixedMoment B raw26443step1 raw26443step1Labels := by
      have ha : raw26443step1 = (fun i j => raw26443step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26443step1 raw26443step0; decide +kernel
      have hl : raw26443step1Labels = raw26443step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26443step0 raw26443step0Labels permutation48 permutation2
    mixedMoment B raw26443step1 raw26443step1Labels = mixedMoment B raw26443step2 raw26443step2Labels := by
      have ha : raw26443step2 = -raw26443step1 := by apply Matrix.ext; change ∀ i j, raw26443step2 i j = -(raw26443step1 i j); unfold raw26443step2 raw26443step1; decide +kernel
      have hl : raw26443step2Labels = raw26443step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3307 node3307Labels := by rfl

def raw26444 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26444 raw26444Labels = mixedMoment B node3239 node3239Labels := by
  calc
    mixedMoment B raw26444 raw26444Labels = mixedMoment B raw26444step0 raw26444step0Labels := by
      have ha : raw26444step0 = (fun i j => raw26444 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26444step0 raw26444; decide +kernel
      have hl : raw26444step0Labels = raw26444Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26444 raw26444Labels permutation158 permutation4
    mixedMoment B raw26444step0 raw26444step0Labels = mixedMoment B raw26444step1 raw26444step1Labels := by
      have ha : raw26444step1 = -raw26444step0 := by apply Matrix.ext; change ∀ i j, raw26444step1 i j = -(raw26444step0 i j); unfold raw26444step1 raw26444step0; decide +kernel
      have hl : raw26444step1Labels = raw26444step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3239 node3239Labels := by rfl

def raw26445 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26445step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26445 raw26445Labels = mixedMoment B node3286 node3286Labels := by
  calc
    mixedMoment B raw26445 raw26445Labels = mixedMoment B raw26445step0 raw26445step0Labels := by
      have ha : raw26445step0 = (fun i j => raw26445 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26445step0 raw26445; decide +kernel
      have hl : raw26445step0Labels = raw26445Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26445 raw26445Labels permutation158 permutation4
    mixedMoment B raw26445step0 raw26445step0Labels = mixedMoment B raw26445step1 raw26445step1Labels := by
      have ha : raw26445step1 = -raw26445step0 := by apply Matrix.ext; change ∀ i j, raw26445step1 i j = -(raw26445step0 i j); unfold raw26445step1 raw26445step0; decide +kernel
      have hl : raw26445step1Labels = raw26445step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3286 node3286Labels := by rfl

def raw26446 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26446 raw26446Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw26446 raw26446Labels = mixedMoment B raw26446step0 raw26446step0Labels := by
      have ha : raw26446step0 = (fun i j => raw26446 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26446step0 raw26446; decide +kernel
      have hl : raw26446step0Labels = raw26446Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26446 raw26446Labels permutation158 permutation4
    mixedMoment B raw26446step0 raw26446step0Labels = mixedMoment B raw26446step1 raw26446step1Labels := by
      have ha : raw26446step1 = -raw26446step0 := by apply Matrix.ext; change ∀ i j, raw26446step1 i j = -(raw26446step0 i j); unfold raw26446step1 raw26446step0; decide +kernel
      have hl : raw26446step1Labels = raw26446step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3292 node3292Labels := by rfl

def raw26447 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26447 raw26447Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw26447 raw26447Labels = mixedMoment B raw26447step0 raw26447step0Labels := by
      have ha : raw26447step0 = (fun i j => raw26447 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26447step0 raw26447; decide +kernel
      have hl : raw26447step0Labels = raw26447Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26447 raw26447Labels permutation152 permutation4
    mixedMoment B raw26447step0 raw26447step0Labels = mixedMoment B raw26447step1 raw26447step1Labels := by
      have ha : raw26447step1 = -raw26447step0 := by apply Matrix.ext; change ∀ i j, raw26447step1 i j = -(raw26447step0 i j); unfold raw26447step1 raw26447step0; decide +kernel
      have hl : raw26447step1Labels = raw26447step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3292 node3292Labels := by rfl

def raw26448 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw26448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26448 raw26448Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26448 raw26448Labels = mixedMoment B raw26448step0 raw26448step0Labels := by
      have ha : raw26448step0 = (fun i j => raw26448 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26448step0 raw26448; decide +kernel
      have hl : raw26448step0Labels = raw26448Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26448 raw26448Labels permutation153 permutation4
    mixedMoment B raw26448step0 raw26448step0Labels = mixedMoment B raw26448step1 raw26448step1Labels := by
      have ha : raw26448step1 = -raw26448step0 := by apply Matrix.ext; change ∀ i j, raw26448step1 i j = -(raw26448step0 i j); unfold raw26448step1 raw26448step0; decide +kernel
      have hl : raw26448step1Labels = raw26448step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw26449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26449 raw26449Labels = mixedMoment B node1286 node1286Labels := by
  calc
    mixedMoment B raw26449 raw26449Labels = mixedMoment B raw26449step0 raw26449step0Labels := by
      have hz : ∀ j, raw26449 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26449step0 = (fun i j => raw26449 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26449step0 raw26449; decide +kernel
      have hl : raw26449step0Labels = raw26449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26449 raw26449Labels permutation265 hz
    mixedMoment B raw26449step0 raw26449step0Labels = mixedMoment B raw26449step1 raw26449step1Labels := by
      have ha : raw26449step1 = (fun i j => raw26449step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26449step1 raw26449step0; decide +kernel
      have hl : raw26449step1Labels = raw26449step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26449step0 raw26449step0Labels permutation53 permutation2
    _ = mixedMoment B node1286 node1286Labels := by rfl

def raw26450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26450 raw26450Labels = mixedMoment B node2583 node2583Labels := by
  calc
    mixedMoment B raw26450 raw26450Labels = mixedMoment B raw26450step0 raw26450step0Labels := by
      have ha : raw26450step0 = (fun i j => raw26450 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26450step0 raw26450; decide +kernel
      have hl : raw26450step0Labels = raw26450Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26450 raw26450Labels permutation173 permutation2
    _ = mixedMoment B node2583 node2583Labels := by rfl

def raw26451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw26451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26451 raw26451Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw26451 raw26451Labels = mixedMoment B raw26451step0 raw26451step0Labels := by
      have hz : ∀ j, raw26451 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26451step0 = (fun i j => raw26451 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26451step0 raw26451; decide +kernel
      have hl : raw26451step0Labels = raw26451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26451 raw26451Labels permutation265 hz
    mixedMoment B raw26451step0 raw26451step0Labels = mixedMoment B raw26451step1 raw26451step1Labels := by
      have ha : raw26451step1 = (fun i j => raw26451step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26451step1 raw26451step0; decide +kernel
      have hl : raw26451step1Labels = raw26451step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26451step0 raw26451step0Labels permutation144 permutation4
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw26452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2]]
def raw26452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw26452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26452 raw26452Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw26452 raw26452Labels = mixedMoment B raw26452step0 raw26452step0Labels := by
      have hz : ∀ j, raw26452 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26452step0 = (fun i j => raw26452 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26452step0 raw26452; decide +kernel
      have hl : raw26452step0Labels = raw26452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26452 raw26452Labels permutation265 hz
    mixedMoment B raw26452step0 raw26452step0Labels = mixedMoment B raw26452step1 raw26452step1Labels := by
      have ha : raw26452step1 = (fun i j => raw26452step0 (permutation43 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26452step1 raw26452step0; decide +kernel
      have hl : raw26452step1Labels = raw26452step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26452step0 raw26452step0Labels permutation43 permutation2
    _ = mixedMoment B node2760 node2760Labels := by rfl

def raw26453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, 1, -1], ![1, -3, 2]]
def raw26453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, 0, -1], ![0, 1, -1], ![1, -3, 2]]
def raw26453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw26453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26453 raw26453Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw26453 raw26453Labels = mixedMoment B raw26453step0 raw26453step0Labels := by
      have hz : ∀ j, raw26453 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26453step0 = (fun i j => raw26453 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26453step0 raw26453; decide +kernel
      have hl : raw26453step0Labels = raw26453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26453 raw26453Labels permutation265 hz
    mixedMoment B raw26453step0 raw26453step0Labels = mixedMoment B raw26453step1 raw26453step1Labels := by
      have ha : raw26453step1 = (fun i j => raw26453step0 (permutation49 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26453step1 raw26453step0; decide +kernel
      have hl : raw26453step1Labels = raw26453step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26453step0 raw26453step0Labels permutation49 permutation2
    _ = mixedMoment B node2760 node2760Labels := by rfl

def raw26454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2]]
def raw26454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2]]
def raw26454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26454 raw26454Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw26454 raw26454Labels = mixedMoment B raw26454step0 raw26454step0Labels := by
      have hz : ∀ j, raw26454 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26454step0 = (fun i j => raw26454 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26454step0 raw26454; decide +kernel
      have hl : raw26454step0Labels = raw26454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26454 raw26454Labels permutation265 hz
    mixedMoment B raw26454step0 raw26454step0Labels = mixedMoment B raw26454step1 raw26454step1Labels := by
      have ha : raw26454step1 = (fun i j => raw26454step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26454step1 raw26454step0; decide +kernel
      have hl : raw26454step1Labels = raw26454step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26454step0 raw26454step0Labels permutation53 permutation2
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw26455 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![1, -1], ![1, -1], ![-2, 2]]
def raw26455Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26455step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![1, -1], ![1, -1], ![-2, 2]]
def raw26455step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26455step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw26455step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26455 raw26455Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw26455 raw26455Labels = mixedMoment B raw26455step0 raw26455step0Labels := by
      have hz : ∀ j, raw26455 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26455step0 = (fun i j => raw26455 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26455step0 raw26455; decide +kernel
      have hl : raw26455step0Labels = raw26455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26455 raw26455Labels permutation265 hz
    mixedMoment B raw26455step0 raw26455step0Labels = mixedMoment B raw26455step1 raw26455step1Labels := by
      have ha : raw26455step1 = (fun i j => raw26455step0 (permutation53 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26455step1 raw26455step0; decide +kernel
      have hl : raw26455step1Labels = raw26455step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26455step0 raw26455step0Labels permutation53 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw26456 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26456 raw26456Labels = mixedMoment B node1648 node1648Labels := by
  calc
    mixedMoment B raw26456 raw26456Labels = mixedMoment B raw26456step0 raw26456step0Labels := by
      have hz : ∀ j, raw26456 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26456step0 = (fun i j => raw26456 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26456step0 raw26456; decide +kernel
      have hl : raw26456step0Labels = raw26456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26456 raw26456Labels permutation265 hz
    mixedMoment B raw26456step0 raw26456step0Labels = mixedMoment B raw26456step1 raw26456step1Labels := by
      have ha : raw26456step1 = (fun i j => raw26456step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26456step1 raw26456step0; decide +kernel
      have hl : raw26456step1Labels = raw26456step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26456step0 raw26456step0Labels permutation53 permutation2
    mixedMoment B raw26456step1 raw26456step1Labels = mixedMoment B raw26456step2 raw26456step2Labels := by
      have ha : raw26456step2 = -raw26456step1 := by apply Matrix.ext; change ∀ i j, raw26456step2 i j = -(raw26456step1 i j); unfold raw26456step2 raw26456step1; decide +kernel
      have hl : raw26456step2Labels = raw26456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1648 node1648Labels := by rfl

def raw26457 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw26457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26457 raw26457Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw26457 raw26457Labels = mixedMoment B raw26457step0 raw26457step0Labels := by
      have hz : ∀ j, raw26457 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26457step0 = (fun i j => raw26457 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26457step0 raw26457; decide +kernel
      have hl : raw26457step0Labels = raw26457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26457 raw26457Labels permutation265 hz
    mixedMoment B raw26457step0 raw26457step0Labels = mixedMoment B raw26457step1 raw26457step1Labels := by
      have ha : raw26457step1 = (fun i j => raw26457step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26457step1 raw26457step0; decide +kernel
      have hl : raw26457step1Labels = raw26457step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26457step0 raw26457step0Labels permutation53 permutation2
    mixedMoment B raw26457step1 raw26457step1Labels = mixedMoment B raw26457step2 raw26457step2Labels := by
      have ha : raw26457step2 = -raw26457step1 := by apply Matrix.ext; change ∀ i j, raw26457step2 i j = -(raw26457step1 i j); unfold raw26457step2 raw26457step1; decide +kernel
      have hl : raw26457step2Labels = raw26457step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3303 node3303Labels := by rfl

def raw26458 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw26458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26458 raw26458Labels = mixedMoment B node1639 node1639Labels := by
  calc
    mixedMoment B raw26458 raw26458Labels = mixedMoment B raw26458step0 raw26458step0Labels := by
      have hz : ∀ j, raw26458 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26458step0 = (fun i j => raw26458 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26458step0 raw26458; decide +kernel
      have hl : raw26458step0Labels = raw26458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26458 raw26458Labels permutation265 hz
    mixedMoment B raw26458step0 raw26458step0Labels = mixedMoment B raw26458step1 raw26458step1Labels := by
      have ha : raw26458step1 = (fun i j => raw26458step0 (permutation55 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26458step1 raw26458step0; decide +kernel
      have hl : raw26458step1Labels = raw26458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26458step0 raw26458step0Labels permutation55 permutation2
    mixedMoment B raw26458step1 raw26458step1Labels = mixedMoment B raw26458step2 raw26458step2Labels := by
      have ha : raw26458step2 = -raw26458step1 := by apply Matrix.ext; change ∀ i j, raw26458step2 i j = -(raw26458step1 i j); unfold raw26458step2 raw26458step1; decide +kernel
      have hl : raw26458step2Labels = raw26458step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1639 node1639Labels := by rfl

def raw26459 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw26459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw26459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26459step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26459step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26459 raw26459Labels = mixedMoment B node1641 node1641Labels := by
  calc
    mixedMoment B raw26459 raw26459Labels = mixedMoment B raw26459step0 raw26459step0Labels := by
      have hz : ∀ j, raw26459 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26459step0 = (fun i j => raw26459 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26459step0 raw26459; decide +kernel
      have hl : raw26459step0Labels = raw26459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26459 raw26459Labels permutation265 hz
    mixedMoment B raw26459step0 raw26459step0Labels = mixedMoment B raw26459step1 raw26459step1Labels := by
      have ha : raw26459step1 = (fun i j => raw26459step0 (permutation54 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26459step1 raw26459step0; decide +kernel
      have hl : raw26459step1Labels = raw26459step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26459step0 raw26459step0Labels permutation54 permutation2
    mixedMoment B raw26459step1 raw26459step1Labels = mixedMoment B raw26459step2 raw26459step2Labels := by
      have ha : raw26459step2 = -raw26459step1 := by apply Matrix.ext; change ∀ i j, raw26459step2 i j = -(raw26459step1 i j); unfold raw26459step2 raw26459step1; decide +kernel
      have hl : raw26459step2Labels = raw26459step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1641 node1641Labels := by rfl

def raw26460 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw26460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26460 raw26460Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw26460 raw26460Labels = mixedMoment B raw26460step0 raw26460step0Labels := by
      have hz : ∀ j, raw26460 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26460step0 = (fun i j => raw26460 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26460step0 raw26460; decide +kernel
      have hl : raw26460step0Labels = raw26460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26460 raw26460Labels permutation265 hz
    mixedMoment B raw26460step0 raw26460step0Labels = mixedMoment B raw26460step1 raw26460step1Labels := by
      have ha : raw26460step1 = (fun i j => raw26460step0 (permutation49 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26460step1 raw26460step0; decide +kernel
      have hl : raw26460step1Labels = raw26460step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26460step0 raw26460step0Labels permutation49 permutation2
    mixedMoment B raw26460step1 raw26460step1Labels = mixedMoment B raw26460step2 raw26460step2Labels := by
      have ha : raw26460step2 = -raw26460step1 := by apply Matrix.ext; change ∀ i j, raw26460step2 i j = -(raw26460step1 i j); unfold raw26460step2 raw26460step1; decide +kernel
      have hl : raw26460step2Labels = raw26460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw26461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26461step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26461step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26461 raw26461Labels = mixedMoment B node4164 node4164Labels := by
  calc
    mixedMoment B raw26461 raw26461Labels = mixedMoment B raw26461step0 raw26461step0Labels := by
      have ha : raw26461step0 = (fun i j => raw26461 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26461step0 raw26461; decide +kernel
      have hl : raw26461step0Labels = raw26461Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26461 raw26461Labels permutation246 permutation3
    mixedMoment B raw26461step0 raw26461step0Labels = mixedMoment B raw26461step1 raw26461step1Labels := by
      have ha : raw26461step1 = raw26461step0 := by apply Matrix.ext; unfold raw26461step1 raw26461step0; decide +kernel
      have hl : raw26461step0Labels = labelEmbedding6 ∘ raw26461step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26461step0 raw26461step0Labels raw26461step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4164 node4164Labels := by rfl

def raw26462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26462step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26462step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26462 raw26462Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw26462 raw26462Labels = mixedMoment B raw26462step0 raw26462step0Labels := by
      have hz : ∀ j, raw26462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26462step0 = (fun i j => raw26462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26462step0 raw26462; decide +kernel
      have hl : raw26462step0Labels = raw26462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26462 raw26462Labels permutation434 hz
    mixedMoment B raw26462step0 raw26462step0Labels = mixedMoment B raw26462step1 raw26462step1Labels := by
      have ha : raw26462step1 = (fun i j => raw26462step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26462step1 raw26462step0; decide +kernel
      have hl : raw26462step1Labels = raw26462step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26462step0 raw26462step0Labels permutation50 permutation3
    mixedMoment B raw26462step1 raw26462step1Labels = mixedMoment B raw26462step2 raw26462step2Labels := by
      have ha : raw26462step2 = raw26462step1 := by apply Matrix.ext; unfold raw26462step2 raw26462step1; decide +kernel
      have hl : raw26462step1Labels = labelEmbedding6 ∘ raw26462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26462step1 raw26462step1Labels raw26462step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw26463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26463step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26463step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26463 raw26463Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw26463 raw26463Labels = mixedMoment B raw26463step0 raw26463step0Labels := by
      have hz : ∀ j, raw26463 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26463step0 = (fun i j => raw26463 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26463step0 raw26463; decide +kernel
      have hl : raw26463step0Labels = raw26463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26463 raw26463Labels permutation520 hz
    mixedMoment B raw26463step0 raw26463step0Labels = mixedMoment B raw26463step1 raw26463step1Labels := by
      have ha : raw26463step1 = (fun i j => raw26463step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26463step1 raw26463step0; decide +kernel
      have hl : raw26463step1Labels = raw26463step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26463step0 raw26463step0Labels permutation50 permutation3
    mixedMoment B raw26463step1 raw26463step1Labels = mixedMoment B raw26463step2 raw26463step2Labels := by
      have ha : raw26463step2 = raw26463step1 := by apply Matrix.ext; unfold raw26463step2 raw26463step1; decide +kernel
      have hl : raw26463step1Labels = labelEmbedding6 ∘ raw26463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26463step1 raw26463step1Labels raw26463step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw26464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26464step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26464 raw26464Labels = mixedMoment B node4569 node4569Labels := by
  calc
    mixedMoment B raw26464 raw26464Labels = mixedMoment B raw26464step0 raw26464step0Labels := by
      have ha : raw26464step0 = (fun i j => raw26464 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26464step0 raw26464; decide +kernel
      have hl : raw26464step0Labels = raw26464Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26464 raw26464Labels permutation246 permutation3
    mixedMoment B raw26464step0 raw26464step0Labels = mixedMoment B raw26464step1 raw26464step1Labels := by
      have ha : raw26464step1 = raw26464step0 := by apply Matrix.ext; unfold raw26464step1 raw26464step0; decide +kernel
      have hl : raw26464step0Labels = labelEmbedding6 ∘ raw26464step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26464step0 raw26464step0Labels raw26464step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4569 node4569Labels := by rfl

def raw26465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26465step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26465step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26465 raw26465Labels = mixedMoment B node4165 node4165Labels := by
  calc
    mixedMoment B raw26465 raw26465Labels = mixedMoment B raw26465step0 raw26465step0Labels := by
      have hz : ∀ j, raw26465 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26465step0 = (fun i j => raw26465 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26465step0 raw26465; decide +kernel
      have hl : raw26465step0Labels = raw26465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26465 raw26465Labels permutation265 hz
    mixedMoment B raw26465step0 raw26465step0Labels = mixedMoment B raw26465step1 raw26465step1Labels := by
      have ha : raw26465step1 = (fun i j => raw26465step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26465step1 raw26465step0; decide +kernel
      have hl : raw26465step1Labels = raw26465step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26465step0 raw26465step0Labels permutation53 permutation3
    mixedMoment B raw26465step1 raw26465step1Labels = mixedMoment B raw26465step2 raw26465step2Labels := by
      have ha : raw26465step2 = raw26465step1 := by apply Matrix.ext; unfold raw26465step2 raw26465step1; decide +kernel
      have hl : raw26465step1Labels = labelEmbedding6 ∘ raw26465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26465step1 raw26465step1Labels raw26465step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4165 node4165Labels := by rfl

def raw26466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26466step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26466 raw26466Labels = mixedMoment B node4537 node4537Labels := by
  calc
    mixedMoment B raw26466 raw26466Labels = mixedMoment B raw26466step0 raw26466step0Labels := by
      have ha : raw26466step0 = (fun i j => raw26466 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26466step0 raw26466; decide +kernel
      have hl : raw26466step0Labels = raw26466Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26466 raw26466Labels permutation173 permutation3
    mixedMoment B raw26466step0 raw26466step0Labels = mixedMoment B raw26466step1 raw26466step1Labels := by
      have ha : raw26466step1 = raw26466step0 := by apply Matrix.ext; unfold raw26466step1 raw26466step0; decide +kernel
      have hl : raw26466step0Labels = labelEmbedding6 ∘ raw26466step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26466step0 raw26466step0Labels raw26466step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4537 node4537Labels := by rfl

def raw26467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26467step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26467step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26467step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26467 raw26467Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw26467 raw26467Labels = mixedMoment B raw26467step0 raw26467step0Labels := by
      have hz : ∀ j, raw26467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26467step0 = (fun i j => raw26467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26467step0 raw26467; decide +kernel
      have hl : raw26467step0Labels = raw26467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26467 raw26467Labels permutation434 hz
    mixedMoment B raw26467step0 raw26467step0Labels = mixedMoment B raw26467step1 raw26467step1Labels := by
      have hz : ∀ j, raw26467step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26467step1 = (fun i j => raw26467step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26467step1 raw26467step0; decide +kernel
      have hl : raw26467step1Labels = raw26467step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26467step0 raw26467step0Labels permutation56 hz
    mixedMoment B raw26467step1 raw26467step1Labels = mixedMoment B raw26467step2 raw26467step2Labels := by
      have ha : raw26467step2 = (fun i j => raw26467step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26467step2 raw26467step1; decide +kernel
      have hl : raw26467step2Labels = raw26467step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26467step1 raw26467step1Labels permutation13 permutation3
    mixedMoment B raw26467step2 raw26467step2Labels = mixedMoment B raw26467step3 raw26467step3Labels := by
      have ha : raw26467step3 = raw26467step2 := by apply Matrix.ext; unfold raw26467step3 raw26467step2; decide +kernel
      have hl : raw26467step2Labels = labelEmbedding6 ∘ raw26467step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26467step2 raw26467step2Labels raw26467step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw26468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26468step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26468step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26468step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26468step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26468 raw26468Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw26468 raw26468Labels = mixedMoment B raw26468step0 raw26468step0Labels := by
      have hz : ∀ j, raw26468 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26468step0 = (fun i j => raw26468 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26468step0 raw26468; decide +kernel
      have hl : raw26468step0Labels = raw26468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26468 raw26468Labels permutation520 hz
    mixedMoment B raw26468step0 raw26468step0Labels = mixedMoment B raw26468step1 raw26468step1Labels := by
      have hz : ∀ j, raw26468step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26468step1 = (fun i j => raw26468step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26468step1 raw26468step0; decide +kernel
      have hl : raw26468step1Labels = raw26468step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26468step0 raw26468step0Labels permutation56 hz
    mixedMoment B raw26468step1 raw26468step1Labels = mixedMoment B raw26468step2 raw26468step2Labels := by
      have ha : raw26468step2 = (fun i j => raw26468step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26468step2 raw26468step1; decide +kernel
      have hl : raw26468step2Labels = raw26468step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26468step1 raw26468step1Labels permutation13 permutation3
    mixedMoment B raw26468step2 raw26468step2Labels = mixedMoment B raw26468step3 raw26468step3Labels := by
      have ha : raw26468step3 = raw26468step2 := by apply Matrix.ext; unfold raw26468step3 raw26468step2; decide +kernel
      have hl : raw26468step2Labels = labelEmbedding6 ∘ raw26468step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26468step2 raw26468step2Labels raw26468step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw26469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26469step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26469step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26469 raw26469Labels = mixedMoment B node4570 node4570Labels := by
  calc
    mixedMoment B raw26469 raw26469Labels = mixedMoment B raw26469step0 raw26469step0Labels := by
      have hz : ∀ j, raw26469 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26469step0 = (fun i j => raw26469 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26469step0 raw26469; decide +kernel
      have hl : raw26469step0Labels = raw26469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26469 raw26469Labels permutation265 hz
    mixedMoment B raw26469step0 raw26469step0Labels = mixedMoment B raw26469step1 raw26469step1Labels := by
      have ha : raw26469step1 = (fun i j => raw26469step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26469step1 raw26469step0; decide +kernel
      have hl : raw26469step1Labels = raw26469step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26469step0 raw26469step0Labels permutation53 permutation3
    mixedMoment B raw26469step1 raw26469step1Labels = mixedMoment B raw26469step2 raw26469step2Labels := by
      have ha : raw26469step2 = raw26469step1 := by apply Matrix.ext; unfold raw26469step2 raw26469step1; decide +kernel
      have hl : raw26469step1Labels = labelEmbedding6 ∘ raw26469step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26469step1 raw26469step1Labels raw26469step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4570 node4570Labels := by rfl

def raw26470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26470step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26470step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26470 raw26470Labels = mixedMoment B node4165 node4165Labels := by
  calc
    mixedMoment B raw26470 raw26470Labels = mixedMoment B raw26470step0 raw26470step0Labels := by
      have hz : ∀ j, raw26470 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26470step0 = (fun i j => raw26470 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26470step0 raw26470; decide +kernel
      have hl : raw26470step0Labels = raw26470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26470 raw26470Labels permutation265 hz
    mixedMoment B raw26470step0 raw26470step0Labels = mixedMoment B raw26470step1 raw26470step1Labels := by
      have ha : raw26470step1 = (fun i j => raw26470step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26470step1 raw26470step0; decide +kernel
      have hl : raw26470step1Labels = raw26470step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26470step0 raw26470step0Labels permutation51 permutation3
    mixedMoment B raw26470step1 raw26470step1Labels = mixedMoment B raw26470step2 raw26470step2Labels := by
      have ha : raw26470step2 = raw26470step1 := by apply Matrix.ext; unfold raw26470step2 raw26470step1; decide +kernel
      have hl : raw26470step1Labels = labelEmbedding6 ∘ raw26470step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26470step1 raw26470step1Labels raw26470step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4165 node4165Labels := by rfl

def raw26471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26471step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26471 raw26471Labels = mixedMoment B node4537 node4537Labels := by
  calc
    mixedMoment B raw26471 raw26471Labels = mixedMoment B raw26471step0 raw26471step0Labels := by
      have ha : raw26471step0 = (fun i j => raw26471 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26471step0 raw26471; decide +kernel
      have hl : raw26471step0Labels = raw26471Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26471 raw26471Labels permutation171 permutation3
    mixedMoment B raw26471step0 raw26471step0Labels = mixedMoment B raw26471step1 raw26471step1Labels := by
      have ha : raw26471step1 = raw26471step0 := by apply Matrix.ext; unfold raw26471step1 raw26471step0; decide +kernel
      have hl : raw26471step0Labels = labelEmbedding6 ∘ raw26471step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26471step0 raw26471step0Labels raw26471step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4537 node4537Labels := by rfl

def raw26472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26472step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26472step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26472step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26472step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26472 raw26472Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw26472 raw26472Labels = mixedMoment B raw26472step0 raw26472step0Labels := by
      have hz : ∀ j, raw26472 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26472step0 = (fun i j => raw26472 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26472step0 raw26472; decide +kernel
      have hl : raw26472step0Labels = raw26472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26472 raw26472Labels permutation520 hz
    mixedMoment B raw26472step0 raw26472step0Labels = mixedMoment B raw26472step1 raw26472step1Labels := by
      have hz : ∀ j, raw26472step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26472step1 = (fun i j => raw26472step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26472step1 raw26472step0; decide +kernel
      have hl : raw26472step1Labels = raw26472step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26472step0 raw26472step0Labels permutation56 hz
    mixedMoment B raw26472step1 raw26472step1Labels = mixedMoment B raw26472step2 raw26472step2Labels := by
      have ha : raw26472step2 = (fun i j => raw26472step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26472step2 raw26472step1; decide +kernel
      have hl : raw26472step2Labels = raw26472step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26472step1 raw26472step1Labels permutation12 permutation3
    mixedMoment B raw26472step2 raw26472step2Labels = mixedMoment B raw26472step3 raw26472step3Labels := by
      have ha : raw26472step3 = raw26472step2 := by apply Matrix.ext; unfold raw26472step3 raw26472step2; decide +kernel
      have hl : raw26472step2Labels = labelEmbedding6 ∘ raw26472step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26472step2 raw26472step2Labels raw26472step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw26473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26473step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26473 raw26473Labels = mixedMoment B node4570 node4570Labels := by
  calc
    mixedMoment B raw26473 raw26473Labels = mixedMoment B raw26473step0 raw26473step0Labels := by
      have hz : ∀ j, raw26473 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26473step0 = (fun i j => raw26473 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26473step0 raw26473; decide +kernel
      have hl : raw26473step0Labels = raw26473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26473 raw26473Labels permutation265 hz
    mixedMoment B raw26473step0 raw26473step0Labels = mixedMoment B raw26473step1 raw26473step1Labels := by
      have ha : raw26473step1 = (fun i j => raw26473step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26473step1 raw26473step0; decide +kernel
      have hl : raw26473step1Labels = raw26473step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26473step0 raw26473step0Labels permutation51 permutation3
    mixedMoment B raw26473step1 raw26473step1Labels = mixedMoment B raw26473step2 raw26473step2Labels := by
      have ha : raw26473step2 = raw26473step1 := by apply Matrix.ext; unfold raw26473step2 raw26473step1; decide +kernel
      have hl : raw26473step1Labels = labelEmbedding6 ∘ raw26473step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26473step1 raw26473step1Labels raw26473step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4570 node4570Labels := by rfl

def raw26474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26474step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26474step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26474step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26474 raw26474Labels = mixedMoment B node4165 node4165Labels := by
  calc
    mixedMoment B raw26474 raw26474Labels = mixedMoment B raw26474step0 raw26474step0Labels := by
      have hz : ∀ j, raw26474 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26474step0 = (fun i j => raw26474 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26474step0 raw26474; decide +kernel
      have hl : raw26474step0Labels = raw26474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26474 raw26474Labels permutation265 hz
    mixedMoment B raw26474step0 raw26474step0Labels = mixedMoment B raw26474step1 raw26474step1Labels := by
      have ha : raw26474step1 = (fun i j => raw26474step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26474step1 raw26474step0; decide +kernel
      have hl : raw26474step1Labels = raw26474step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26474step0 raw26474step0Labels permutation50 permutation3
    mixedMoment B raw26474step1 raw26474step1Labels = mixedMoment B raw26474step2 raw26474step2Labels := by
      have ha : raw26474step2 = raw26474step1 := by apply Matrix.ext; unfold raw26474step2 raw26474step1; decide +kernel
      have hl : raw26474step1Labels = labelEmbedding6 ∘ raw26474step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26474step1 raw26474step1Labels raw26474step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4165 node4165Labels := by rfl

def raw26475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26475step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26475 raw26475Labels = mixedMoment B node4537 node4537Labels := by
  calc
    mixedMoment B raw26475 raw26475Labels = mixedMoment B raw26475step0 raw26475step0Labels := by
      have ha : raw26475step0 = (fun i j => raw26475 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26475step0 raw26475; decide +kernel
      have hl : raw26475step0Labels = raw26475Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26475 raw26475Labels permutation170 permutation3
    mixedMoment B raw26475step0 raw26475step0Labels = mixedMoment B raw26475step1 raw26475step1Labels := by
      have ha : raw26475step1 = raw26475step0 := by apply Matrix.ext; unfold raw26475step1 raw26475step0; decide +kernel
      have hl : raw26475step0Labels = labelEmbedding6 ∘ raw26475step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26475step0 raw26475step0Labels raw26475step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4537 node4537Labels := by rfl

def raw26476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw26476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw26476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26476step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26476step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26476 raw26476Labels = mixedMoment B node4570 node4570Labels := by
  calc
    mixedMoment B raw26476 raw26476Labels = mixedMoment B raw26476step0 raw26476step0Labels := by
      have hz : ∀ j, raw26476 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26476step0 = (fun i j => raw26476 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26476step0 raw26476; decide +kernel
      have hl : raw26476step0Labels = raw26476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26476 raw26476Labels permutation265 hz
    mixedMoment B raw26476step0 raw26476step0Labels = mixedMoment B raw26476step1 raw26476step1Labels := by
      have ha : raw26476step1 = (fun i j => raw26476step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26476step1 raw26476step0; decide +kernel
      have hl : raw26476step1Labels = raw26476step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26476step0 raw26476step0Labels permutation50 permutation3
    mixedMoment B raw26476step1 raw26476step1Labels = mixedMoment B raw26476step2 raw26476step2Labels := by
      have ha : raw26476step2 = raw26476step1 := by apply Matrix.ext; unfold raw26476step2 raw26476step1; decide +kernel
      have hl : raw26476step1Labels = labelEmbedding6 ∘ raw26476step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26476step1 raw26476step1Labels raw26476step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4570 node4570Labels := by rfl

def raw26477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26477 raw26477Labels = mixedMoment B node592 node592Labels := by
  calc
    mixedMoment B raw26477 raw26477Labels = mixedMoment B raw26477step0 raw26477step0Labels := by
      have ha : raw26477step0 = (fun i j => raw26477 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26477step0 raw26477; decide +kernel
      have hl : raw26477step0Labels = raw26477Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26477 raw26477Labels permutation246 permutation3
    _ = mixedMoment B node592 node592Labels := by rfl

def raw26478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26478step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26478 raw26478Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw26478 raw26478Labels = mixedMoment B raw26478step0 raw26478step0Labels := by
      have hz : ∀ j, raw26478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26478step0 = (fun i j => raw26478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26478step0 raw26478; decide +kernel
      have hl : raw26478step0Labels = raw26478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26478 raw26478Labels permutation434 hz
    mixedMoment B raw26478step0 raw26478step0Labels = mixedMoment B raw26478step1 raw26478step1Labels := by
      have ha : raw26478step1 = (fun i j => raw26478step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26478step1 raw26478step0; decide +kernel
      have hl : raw26478step1Labels = raw26478step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26478step0 raw26478step0Labels permutation50 permutation3
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw26479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26479step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26479 raw26479Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw26479 raw26479Labels = mixedMoment B raw26479step0 raw26479step0Labels := by
      have hz : ∀ j, raw26479 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26479step0 = (fun i j => raw26479 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26479step0 raw26479; decide +kernel
      have hl : raw26479step0Labels = raw26479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26479 raw26479Labels permutation520 hz
    mixedMoment B raw26479step0 raw26479step0Labels = mixedMoment B raw26479step1 raw26479step1Labels := by
      have ha : raw26479step1 = (fun i j => raw26479step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26479step1 raw26479step0; decide +kernel
      have hl : raw26479step1Labels = raw26479step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26479step0 raw26479step0Labels permutation50 permutation3
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw26480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26480 raw26480Labels = mixedMoment B node1187 node1187Labels := by
  calc
    mixedMoment B raw26480 raw26480Labels = mixedMoment B raw26480step0 raw26480step0Labels := by
      have ha : raw26480step0 = (fun i j => raw26480 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26480step0 raw26480; decide +kernel
      have hl : raw26480step0Labels = raw26480Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26480 raw26480Labels permutation246 permutation3
    _ = mixedMoment B node1187 node1187Labels := by rfl

def raw26481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26481 raw26481Labels = mixedMoment B node593 node593Labels := by
  calc
    mixedMoment B raw26481 raw26481Labels = mixedMoment B raw26481step0 raw26481step0Labels := by
      have hz : ∀ j, raw26481 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26481step0 = (fun i j => raw26481 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26481step0 raw26481; decide +kernel
      have hl : raw26481step0Labels = raw26481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26481 raw26481Labels permutation265 hz
    mixedMoment B raw26481step0 raw26481step0Labels = mixedMoment B raw26481step1 raw26481step1Labels := by
      have ha : raw26481step1 = (fun i j => raw26481step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26481step1 raw26481step0; decide +kernel
      have hl : raw26481step1Labels = raw26481step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26481step0 raw26481step0Labels permutation53 permutation3
    _ = mixedMoment B node593 node593Labels := by rfl

def raw26482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26482 raw26482Labels = mixedMoment B node1122 node1122Labels := by
  calc
    mixedMoment B raw26482 raw26482Labels = mixedMoment B raw26482step0 raw26482step0Labels := by
      have ha : raw26482step0 = (fun i j => raw26482 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26482step0 raw26482; decide +kernel
      have hl : raw26482step0Labels = raw26482Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26482 raw26482Labels permutation173 permutation3
    _ = mixedMoment B node1122 node1122Labels := by rfl

def raw26483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26483 raw26483Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw26483 raw26483Labels = mixedMoment B raw26483step0 raw26483step0Labels := by
      have hz : ∀ j, raw26483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26483step0 = (fun i j => raw26483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26483step0 raw26483; decide +kernel
      have hl : raw26483step0Labels = raw26483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26483 raw26483Labels permutation434 hz
    mixedMoment B raw26483step0 raw26483step0Labels = mixedMoment B raw26483step1 raw26483step1Labels := by
      have hz : ∀ j, raw26483step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26483step1 = (fun i j => raw26483step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26483step1 raw26483step0; decide +kernel
      have hl : raw26483step1Labels = raw26483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26483step0 raw26483step0Labels permutation56 hz
    mixedMoment B raw26483step1 raw26483step1Labels = mixedMoment B raw26483step2 raw26483step2Labels := by
      have ha : raw26483step2 = (fun i j => raw26483step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26483step2 raw26483step1; decide +kernel
      have hl : raw26483step2Labels = raw26483step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26483step1 raw26483step1Labels permutation13 permutation3
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw26484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26484step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26484step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26484 raw26484Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw26484 raw26484Labels = mixedMoment B raw26484step0 raw26484step0Labels := by
      have hz : ∀ j, raw26484 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26484step0 = (fun i j => raw26484 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26484step0 raw26484; decide +kernel
      have hl : raw26484step0Labels = raw26484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26484 raw26484Labels permutation520 hz
    mixedMoment B raw26484step0 raw26484step0Labels = mixedMoment B raw26484step1 raw26484step1Labels := by
      have hz : ∀ j, raw26484step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26484step1 = (fun i j => raw26484step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26484step1 raw26484step0; decide +kernel
      have hl : raw26484step1Labels = raw26484step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26484step0 raw26484step0Labels permutation56 hz
    mixedMoment B raw26484step1 raw26484step1Labels = mixedMoment B raw26484step2 raw26484step2Labels := by
      have ha : raw26484step2 = (fun i j => raw26484step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26484step2 raw26484step1; decide +kernel
      have hl : raw26484step2Labels = raw26484step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26484step1 raw26484step1Labels permutation13 permutation3
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw26485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26485 raw26485Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw26485 raw26485Labels = mixedMoment B raw26485step0 raw26485step0Labels := by
      have hz : ∀ j, raw26485 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26485step0 = (fun i j => raw26485 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26485step0 raw26485; decide +kernel
      have hl : raw26485step0Labels = raw26485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26485 raw26485Labels permutation265 hz
    mixedMoment B raw26485step0 raw26485step0Labels = mixedMoment B raw26485step1 raw26485step1Labels := by
      have ha : raw26485step1 = (fun i j => raw26485step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26485step1 raw26485step0; decide +kernel
      have hl : raw26485step1Labels = raw26485step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26485step0 raw26485step0Labels permutation53 permutation3
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw26486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26486 raw26486Labels = mixedMoment B node593 node593Labels := by
  calc
    mixedMoment B raw26486 raw26486Labels = mixedMoment B raw26486step0 raw26486step0Labels := by
      have hz : ∀ j, raw26486 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26486step0 = (fun i j => raw26486 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26486step0 raw26486; decide +kernel
      have hl : raw26486step0Labels = raw26486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26486 raw26486Labels permutation265 hz
    mixedMoment B raw26486step0 raw26486step0Labels = mixedMoment B raw26486step1 raw26486step1Labels := by
      have ha : raw26486step1 = (fun i j => raw26486step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26486step1 raw26486step0; decide +kernel
      have hl : raw26486step1Labels = raw26486step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26486step0 raw26486step0Labels permutation51 permutation3
    _ = mixedMoment B node593 node593Labels := by rfl

def raw26487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26487step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26487 raw26487Labels = mixedMoment B node1122 node1122Labels := by
  calc
    mixedMoment B raw26487 raw26487Labels = mixedMoment B raw26487step0 raw26487step0Labels := by
      have ha : raw26487step0 = (fun i j => raw26487 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26487step0 raw26487; decide +kernel
      have hl : raw26487step0Labels = raw26487Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26487 raw26487Labels permutation171 permutation3
    _ = mixedMoment B node1122 node1122Labels := by rfl

def raw26488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw26488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26488step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26488 raw26488Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw26488 raw26488Labels = mixedMoment B raw26488step0 raw26488step0Labels := by
      have hz : ∀ j, raw26488 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26488step0 = (fun i j => raw26488 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26488step0 raw26488; decide +kernel
      have hl : raw26488step0Labels = raw26488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26488 raw26488Labels permutation520 hz
    mixedMoment B raw26488step0 raw26488step0Labels = mixedMoment B raw26488step1 raw26488step1Labels := by
      have hz : ∀ j, raw26488step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26488step1 = (fun i j => raw26488step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26488step1 raw26488step0; decide +kernel
      have hl : raw26488step1Labels = raw26488step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26488step0 raw26488step0Labels permutation56 hz
    mixedMoment B raw26488step1 raw26488step1Labels = mixedMoment B raw26488step2 raw26488step2Labels := by
      have ha : raw26488step2 = (fun i j => raw26488step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26488step2 raw26488step1; decide +kernel
      have hl : raw26488step2Labels = raw26488step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26488step1 raw26488step1Labels permutation12 permutation3
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw26489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw26489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26489 raw26489Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw26489 raw26489Labels = mixedMoment B raw26489step0 raw26489step0Labels := by
      have hz : ∀ j, raw26489 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26489step0 = (fun i j => raw26489 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26489step0 raw26489; decide +kernel
      have hl : raw26489step0Labels = raw26489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26489 raw26489Labels permutation265 hz
    mixedMoment B raw26489step0 raw26489step0Labels = mixedMoment B raw26489step1 raw26489step1Labels := by
      have ha : raw26489step1 = (fun i j => raw26489step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26489step1 raw26489step0; decide +kernel
      have hl : raw26489step1Labels = raw26489step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26489step0 raw26489step0Labels permutation51 permutation3
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw26490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26490 raw26490Labels = mixedMoment B node593 node593Labels := by
  calc
    mixedMoment B raw26490 raw26490Labels = mixedMoment B raw26490step0 raw26490step0Labels := by
      have hz : ∀ j, raw26490 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26490step0 = (fun i j => raw26490 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26490step0 raw26490; decide +kernel
      have hl : raw26490step0Labels = raw26490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26490 raw26490Labels permutation265 hz
    mixedMoment B raw26490step0 raw26490step0Labels = mixedMoment B raw26490step1 raw26490step1Labels := by
      have ha : raw26490step1 = (fun i j => raw26490step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26490step1 raw26490step0; decide +kernel
      have hl : raw26490step1Labels = raw26490step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26490step0 raw26490step0Labels permutation50 permutation3
    _ = mixedMoment B node593 node593Labels := by rfl

def raw26491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw26491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26491 raw26491Labels = mixedMoment B node1122 node1122Labels := by
  calc
    mixedMoment B raw26491 raw26491Labels = mixedMoment B raw26491step0 raw26491step0Labels := by
      have ha : raw26491step0 = (fun i j => raw26491 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26491step0 raw26491; decide +kernel
      have hl : raw26491step0Labels = raw26491Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26491 raw26491Labels permutation170 permutation3
    _ = mixedMoment B node1122 node1122Labels := by rfl

def raw26492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw26492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw26492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26492 raw26492Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw26492 raw26492Labels = mixedMoment B raw26492step0 raw26492step0Labels := by
      have hz : ∀ j, raw26492 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26492step0 = (fun i j => raw26492 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26492step0 raw26492; decide +kernel
      have hl : raw26492step0Labels = raw26492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26492 raw26492Labels permutation265 hz
    mixedMoment B raw26492step0 raw26492step0Labels = mixedMoment B raw26492step1 raw26492step1Labels := by
      have ha : raw26492step1 = (fun i j => raw26492step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26492step1 raw26492step0; decide +kernel
      have hl : raw26492step1Labels = raw26492step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26492step0 raw26492step0Labels permutation50 permutation3
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw26493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26493 raw26493Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw26493 raw26493Labels = mixedMoment B raw26493step0 raw26493step0Labels := by
      have ha : raw26493step0 = (fun i j => raw26493 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26493step0 raw26493; decide +kernel
      have hl : raw26493step0Labels = raw26493Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26493 raw26493Labels permutation170 permutation2
    _ = mixedMoment B node5162 node5162Labels := by rfl

def raw26494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26494step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26494 raw26494Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw26494 raw26494Labels = mixedMoment B raw26494step0 raw26494step0Labels := by
      have hz : ∀ j, raw26494 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26494step0 = (fun i j => raw26494 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26494step0 raw26494; decide +kernel
      have hl : raw26494step0Labels = raw26494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26494 raw26494Labels permutation265 hz
    mixedMoment B raw26494step0 raw26494step0Labels = mixedMoment B raw26494step1 raw26494step1Labels := by
      have ha : raw26494step1 = (fun i j => raw26494step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26494step1 raw26494step0; decide +kernel
      have hl : raw26494step1Labels = raw26494step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26494step0 raw26494step0Labels permutation48 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw26495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26495step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26495 raw26495Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw26495 raw26495Labels = mixedMoment B raw26495step0 raw26495step0Labels := by
      have hz : ∀ j, raw26495 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26495step0 = (fun i j => raw26495 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26495step0 raw26495; decide +kernel
      have hl : raw26495step0Labels = raw26495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26495 raw26495Labels permutation265 hz
    mixedMoment B raw26495step0 raw26495step0Labels = mixedMoment B raw26495step1 raw26495step1Labels := by
      have ha : raw26495step1 = (fun i j => raw26495step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26495step1 raw26495step0; decide +kernel
      have hl : raw26495step1Labels = raw26495step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26495step0 raw26495step0Labels permutation50 permutation2
    _ = mixedMoment B node5273 node5273Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
