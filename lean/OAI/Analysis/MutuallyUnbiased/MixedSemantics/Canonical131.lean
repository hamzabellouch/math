import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16768 raw16768Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw16768 raw16768Labels = mixedMoment B raw16768step0 raw16768step0Labels := by
      have ha : raw16768step0 = (fun i j => raw16768 (permutation679 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16768step0 raw16768; decide +kernel
      have hl : raw16768step0Labels = raw16768Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16768 raw16768Labels permutation679 permutation3
    mixedMoment B raw16768step0 raw16768step0Labels = mixedMoment B raw16768step1 raw16768step1Labels := by
      have ha : raw16768step1 = -raw16768step0 := by apply Matrix.ext; change ∀ i j, raw16768step1 i j = -(raw16768step0 i j); unfold raw16768step1 raw16768step0; decide +kernel
      have hl : raw16768step1Labels = raw16768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw16769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16769step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16769 raw16769Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw16769 raw16769Labels = mixedMoment B raw16769step0 raw16769step0Labels := by
      have hz : ∀ j, raw16769 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16769step0 = (fun i j => raw16769 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16769step0 raw16769; decide +kernel
      have hl : raw16769step0Labels = raw16769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16769 raw16769Labels permutation520 hz
    mixedMoment B raw16769step0 raw16769step0Labels = mixedMoment B raw16769step1 raw16769step1Labels := by
      have ha : raw16769step1 = (fun i j => raw16769step0 (permutation60 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16769step1 raw16769step0; decide +kernel
      have hl : raw16769step1Labels = raw16769step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16769step0 raw16769step0Labels permutation60 permutation6
    mixedMoment B raw16769step1 raw16769step1Labels = mixedMoment B raw16769step2 raw16769step2Labels := by
      have ha : raw16769step2 = -raw16769step1 := by apply Matrix.ext; change ∀ i j, raw16769step2 i j = -(raw16769step1 i j); unfold raw16769step2 raw16769step1; decide +kernel
      have hl : raw16769step2Labels = raw16769step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw16770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16770 raw16770Labels = mixedMoment B node3992 node3992Labels := by
  calc
    mixedMoment B raw16770 raw16770Labels = mixedMoment B raw16770step0 raw16770step0Labels := by
      have ha : raw16770step0 = (fun i j => raw16770 (permutation281 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16770step0 raw16770; decide +kernel
      have hl : raw16770step0Labels = raw16770Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16770 raw16770Labels permutation281 permutation6
    mixedMoment B raw16770step0 raw16770step0Labels = mixedMoment B raw16770step1 raw16770step1Labels := by
      have ha : raw16770step1 = -raw16770step0 := by apply Matrix.ext; change ∀ i j, raw16770step1 i j = -(raw16770step0 i j); unfold raw16770step1 raw16770step0; decide +kernel
      have hl : raw16770step1Labels = raw16770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3992 node3992Labels := by rfl

def raw16771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16771 raw16771Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw16771 raw16771Labels = mixedMoment B raw16771step0 raw16771step0Labels := by
      have ha : raw16771step0 = (fun i j => raw16771 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16771step0 raw16771; decide +kernel
      have hl : raw16771step0Labels = raw16771Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16771 raw16771Labels permutation182 permutation3
    _ = mixedMoment B node2698 node2698Labels := by rfl

def raw16772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16772 raw16772Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw16772 raw16772Labels = mixedMoment B raw16772step0 raw16772step0Labels := by
      have ha : raw16772step0 = (fun i j => raw16772 (permutation282 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16772step0 raw16772; decide +kernel
      have hl : raw16772step0Labels = raw16772Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16772 raw16772Labels permutation282 permutation6
    mixedMoment B raw16772step0 raw16772step0Labels = mixedMoment B raw16772step1 raw16772step1Labels := by
      have ha : raw16772step1 = -raw16772step0 := by apply Matrix.ext; change ∀ i j, raw16772step1 i j = -(raw16772step0 i j); unfold raw16772step1 raw16772step0; decide +kernel
      have hl : raw16772step1Labels = raw16772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw16773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16773 raw16773Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw16773 raw16773Labels = mixedMoment B raw16773step0 raw16773step0Labels := by
      have ha : raw16773step0 = (fun i j => raw16773 (permutation281 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16773step0 raw16773; decide +kernel
      have hl : raw16773step0Labels = raw16773Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16773 raw16773Labels permutation281 permutation6
    mixedMoment B raw16773step0 raw16773step0Labels = mixedMoment B raw16773step1 raw16773step1Labels := by
      have ha : raw16773step1 = -raw16773step0 := by apply Matrix.ext; change ∀ i j, raw16773step1 i j = -(raw16773step0 i j); unfold raw16773step1 raw16773step0; decide +kernel
      have hl : raw16773step1Labels = raw16773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw16774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16774step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16774 raw16774Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw16774 raw16774Labels = mixedMoment B raw16774step0 raw16774step0Labels := by
      have hz : ∀ j, raw16774 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16774step0 = (fun i j => raw16774 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16774step0 raw16774; decide +kernel
      have hl : raw16774step0Labels = raw16774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16774 raw16774Labels permutation520 hz
    mixedMoment B raw16774step0 raw16774step0Labels = mixedMoment B raw16774step1 raw16774step1Labels := by
      have ha : raw16774step1 = (fun i j => raw16774step0 (permutation60 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16774step1 raw16774step0; decide +kernel
      have hl : raw16774step1Labels = raw16774step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16774step0 raw16774step0Labels permutation60 permutation6
    mixedMoment B raw16774step1 raw16774step1Labels = mixedMoment B raw16774step2 raw16774step2Labels := by
      have ha : raw16774step2 = -raw16774step1 := by apply Matrix.ext; change ∀ i j, raw16774step2 i j = -(raw16774step1 i j); unfold raw16774step2 raw16774step1; decide +kernel
      have hl : raw16774step2Labels = raw16774step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw16775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16775 raw16775Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw16775 raw16775Labels = mixedMoment B raw16775step0 raw16775step0Labels := by
      have ha : raw16775step0 = (fun i j => raw16775 (permutation281 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16775step0 raw16775; decide +kernel
      have hl : raw16775step0Labels = raw16775Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16775 raw16775Labels permutation281 permutation6
    mixedMoment B raw16775step0 raw16775step0Labels = mixedMoment B raw16775step1 raw16775step1Labels := by
      have ha : raw16775step1 = -raw16775step0 := by apply Matrix.ext; change ∀ i j, raw16775step1 i j = -(raw16775step0 i j); unfold raw16775step1 raw16775step0; decide +kernel
      have hl : raw16775step1Labels = raw16775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw16776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16776step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16776 raw16776Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw16776 raw16776Labels = mixedMoment B raw16776step0 raw16776step0Labels := by
      have ha : raw16776step0 = (fun i j => raw16776 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16776step0 raw16776; decide +kernel
      have hl : raw16776step0Labels = raw16776Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16776 raw16776Labels permutation158 permutation3
    _ = mixedMoment B node2615 node2615Labels := by rfl

def raw16777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16777 raw16777Labels = mixedMoment B node3936 node3936Labels := by
  calc
    mixedMoment B raw16777 raw16777Labels = mixedMoment B raw16777step0 raw16777step0Labels := by
      have ha : raw16777step0 = (fun i j => raw16777 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16777step0 raw16777; decide +kernel
      have hl : raw16777step0Labels = raw16777Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16777 raw16777Labels permutation158 permutation3
    _ = mixedMoment B node3936 node3936Labels := by rfl

def raw16778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16778 raw16778Labels = mixedMoment B node3947 node3947Labels := by
  calc
    mixedMoment B raw16778 raw16778Labels = mixedMoment B raw16778step0 raw16778step0Labels := by
      have ha : raw16778step0 = (fun i j => raw16778 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16778step0 raw16778; decide +kernel
      have hl : raw16778step0Labels = raw16778Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16778 raw16778Labels permutation200 permutation3
    _ = mixedMoment B node3947 node3947Labels := by rfl

def raw16779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16779 raw16779Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw16779 raw16779Labels = mixedMoment B raw16779step0 raw16779step0Labels := by
      have hz : ∀ j, raw16779 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16779step0 = (fun i j => raw16779 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16779step0 raw16779; decide +kernel
      have hl : raw16779step0Labels = raw16779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16779 raw16779Labels permutation520 hz
    mixedMoment B raw16779step0 raw16779step0Labels = mixedMoment B raw16779step1 raw16779step1Labels := by
      have ha : raw16779step1 = (fun i j => raw16779step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16779step1 raw16779step0; decide +kernel
      have hl : raw16779step1Labels = raw16779step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16779step0 raw16779step0Labels permutation145 permutation3
    mixedMoment B raw16779step1 raw16779step1Labels = mixedMoment B raw16779step2 raw16779step2Labels := by
      have ha : raw16779step2 = -raw16779step1 := by apply Matrix.ext; change ∀ i j, raw16779step2 i j = -(raw16779step1 i j); unfold raw16779step2 raw16779step1; decide +kernel
      have hl : raw16779step2Labels = raw16779step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw16780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16780step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16780 raw16780Labels = mixedMoment B node4002 node4002Labels := by
  calc
    mixedMoment B raw16780 raw16780Labels = mixedMoment B raw16780step0 raw16780step0Labels := by
      have ha : raw16780step0 = (fun i j => raw16780 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16780step0 raw16780; decide +kernel
      have hl : raw16780step0Labels = raw16780Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16780 raw16780Labels permutation159 permutation3
    _ = mixedMoment B node4002 node4002Labels := by rfl

def raw16781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16781 raw16781Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw16781 raw16781Labels = mixedMoment B raw16781step0 raw16781step0Labels := by
      have ha : raw16781step0 = (fun i j => raw16781 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16781step0 raw16781; decide +kernel
      have hl : raw16781step0Labels = raw16781Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16781 raw16781Labels permutation152 permutation3
    _ = mixedMoment B node2615 node2615Labels := by rfl

def raw16782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16782 raw16782Labels = mixedMoment B node3936 node3936Labels := by
  calc
    mixedMoment B raw16782 raw16782Labels = mixedMoment B raw16782step0 raw16782step0Labels := by
      have ha : raw16782step0 = (fun i j => raw16782 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16782step0 raw16782; decide +kernel
      have hl : raw16782step0Labels = raw16782Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16782 raw16782Labels permutation152 permutation3
    _ = mixedMoment B node3936 node3936Labels := by rfl

def raw16783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16783 raw16783Labels = mixedMoment B node3947 node3947Labels := by
  calc
    mixedMoment B raw16783 raw16783Labels = mixedMoment B raw16783step0 raw16783step0Labels := by
      have ha : raw16783step0 = (fun i j => raw16783 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16783step0 raw16783; decide +kernel
      have hl : raw16783step0Labels = raw16783Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16783 raw16783Labels permutation176 permutation3
    _ = mixedMoment B node3947 node3947Labels := by rfl

def raw16784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16784 raw16784Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw16784 raw16784Labels = mixedMoment B raw16784step0 raw16784step0Labels := by
      have hz : ∀ j, raw16784 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16784step0 = (fun i j => raw16784 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16784step0 raw16784; decide +kernel
      have hl : raw16784step0Labels = raw16784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16784 raw16784Labels permutation520 hz
    mixedMoment B raw16784step0 raw16784step0Labels = mixedMoment B raw16784step1 raw16784step1Labels := by
      have ha : raw16784step1 = (fun i j => raw16784step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16784step1 raw16784step0; decide +kernel
      have hl : raw16784step1Labels = raw16784step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16784step0 raw16784step0Labels permutation151 permutation3
    mixedMoment B raw16784step1 raw16784step1Labels = mixedMoment B raw16784step2 raw16784step2Labels := by
      have ha : raw16784step2 = -raw16784step1 := by apply Matrix.ext; change ∀ i j, raw16784step2 i j = -(raw16784step1 i j); unfold raw16784step2 raw16784step1; decide +kernel
      have hl : raw16784step2Labels = raw16784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw16785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16785step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16785 raw16785Labels = mixedMoment B node4002 node4002Labels := by
  calc
    mixedMoment B raw16785 raw16785Labels = mixedMoment B raw16785step0 raw16785step0Labels := by
      have ha : raw16785step0 = (fun i j => raw16785 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16785step0 raw16785; decide +kernel
      have hl : raw16785step0Labels = raw16785Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16785 raw16785Labels permutation153 permutation3
    _ = mixedMoment B node4002 node4002Labels := by rfl

def raw16786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16786 raw16786Labels = mixedMoment B node2609 node2609Labels := by
  calc
    mixedMoment B raw16786 raw16786Labels = mixedMoment B raw16786step0 raw16786step0Labels := by
      have ha : raw16786step0 = (fun i j => raw16786 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16786step0 raw16786; decide +kernel
      have hl : raw16786step0Labels = raw16786Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16786 raw16786Labels permutation153 permutation3
    _ = mixedMoment B node2609 node2609Labels := by rfl

def raw16787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw16787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16787 raw16787Labels = mixedMoment B node3685 node3685Labels := by
  calc
    mixedMoment B raw16787 raw16787Labels = mixedMoment B raw16787step0 raw16787step0Labels := by
      have ha : raw16787step0 = (fun i j => raw16787 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16787step0 raw16787; decide +kernel
      have hl : raw16787step0Labels = raw16787Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16787 raw16787Labels permutation584 permutation3
    mixedMoment B raw16787step0 raw16787step0Labels = mixedMoment B raw16787step1 raw16787step1Labels := by
      have ha : raw16787step1 = -raw16787step0 := by apply Matrix.ext; change ∀ i j, raw16787step1 i j = -(raw16787step0 i j); unfold raw16787step1 raw16787step0; decide +kernel
      have hl : raw16787step1Labels = raw16787step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3685 node3685Labels := by rfl

def raw16788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16788 raw16788Labels = mixedMoment B node3688 node3688Labels := by
  calc
    mixedMoment B raw16788 raw16788Labels = mixedMoment B raw16788step0 raw16788step0Labels := by
      have ha : raw16788step0 = (fun i j => raw16788 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16788step0 raw16788; decide +kernel
      have hl : raw16788step0Labels = raw16788Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16788 raw16788Labels permutation587 permutation3
    mixedMoment B raw16788step0 raw16788step0Labels = mixedMoment B raw16788step1 raw16788step1Labels := by
      have ha : raw16788step1 = -raw16788step0 := by apply Matrix.ext; change ∀ i j, raw16788step1 i j = -(raw16788step0 i j); unfold raw16788step1 raw16788step0; decide +kernel
      have hl : raw16788step1Labels = raw16788step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3688 node3688Labels := by rfl

def raw16789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16789 raw16789Labels = mixedMoment B node3688 node3688Labels := by
  calc
    mixedMoment B raw16789 raw16789Labels = mixedMoment B raw16789step0 raw16789step0Labels := by
      have ha : raw16789step0 = (fun i j => raw16789 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16789step0 raw16789; decide +kernel
      have hl : raw16789step0Labels = raw16789Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16789 raw16789Labels permutation582 permutation3
    mixedMoment B raw16789step0 raw16789step0Labels = mixedMoment B raw16789step1 raw16789step1Labels := by
      have ha : raw16789step1 = -raw16789step0 := by apply Matrix.ext; change ∀ i j, raw16789step1 i j = -(raw16789step0 i j); unfold raw16789step1 raw16789step0; decide +kernel
      have hl : raw16789step1Labels = raw16789step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3688 node3688Labels := by rfl

def raw16790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw16790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16790 raw16790Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw16790 raw16790Labels = mixedMoment B raw16790step0 raw16790step0Labels := by
      have ha : raw16790step0 = (fun i j => raw16790 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16790step0 raw16790; decide +kernel
      have hl : raw16790step0Labels = raw16790Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16790 raw16790Labels permutation584 permutation3
    mixedMoment B raw16790step0 raw16790step0Labels = mixedMoment B raw16790step1 raw16790step1Labels := by
      have ha : raw16790step1 = -raw16790step0 := by apply Matrix.ext; change ∀ i j, raw16790step1 i j = -(raw16790step0 i j); unfold raw16790step1 raw16790step0; decide +kernel
      have hl : raw16790step1Labels = raw16790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw16791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw16791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16791 raw16791Labels = mixedMoment B node2469 node2469Labels := by
  calc
    mixedMoment B raw16791 raw16791Labels = mixedMoment B raw16791step0 raw16791step0Labels := by
      have ha : raw16791step0 = (fun i j => raw16791 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16791step0 raw16791; decide +kernel
      have hl : raw16791step0Labels = raw16791Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16791 raw16791Labels permutation682 permutation3
    mixedMoment B raw16791step0 raw16791step0Labels = mixedMoment B raw16791step1 raw16791step1Labels := by
      have ha : raw16791step1 = -raw16791step0 := by apply Matrix.ext; change ∀ i j, raw16791step1 i j = -(raw16791step0 i j); unfold raw16791step1 raw16791step0; decide +kernel
      have hl : raw16791step1Labels = raw16791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2469 node2469Labels := by rfl

def raw16792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw16792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16792 raw16792Labels = mixedMoment B node2473 node2473Labels := by
  calc
    mixedMoment B raw16792 raw16792Labels = mixedMoment B raw16792step0 raw16792step0Labels := by
      have ha : raw16792step0 = (fun i j => raw16792 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16792step0 raw16792; decide +kernel
      have hl : raw16792step0Labels = raw16792Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16792 raw16792Labels permutation682 permutation3
    mixedMoment B raw16792step0 raw16792step0Labels = mixedMoment B raw16792step1 raw16792step1Labels := by
      have ha : raw16792step1 = -raw16792step0 := by apply Matrix.ext; change ∀ i j, raw16792step1 i j = -(raw16792step0 i j); unfold raw16792step1 raw16792step0; decide +kernel
      have hl : raw16792step1Labels = raw16792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2473 node2473Labels := by rfl

def raw16793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16793 raw16793Labels = mixedMoment B node2478 node2478Labels := by
  calc
    mixedMoment B raw16793 raw16793Labels = mixedMoment B raw16793step0 raw16793step0Labels := by
      have ha : raw16793step0 = (fun i j => raw16793 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16793step0 raw16793; decide +kernel
      have hl : raw16793step0Labels = raw16793Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16793 raw16793Labels permutation686 permutation3
    mixedMoment B raw16793step0 raw16793step0Labels = mixedMoment B raw16793step1 raw16793step1Labels := by
      have ha : raw16793step1 = -raw16793step0 := by apply Matrix.ext; change ∀ i j, raw16793step1 i j = -(raw16793step0 i j); unfold raw16793step1 raw16793step0; decide +kernel
      have hl : raw16793step1Labels = raw16793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2478 node2478Labels := by rfl

def raw16794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16794 raw16794Labels = mixedMoment B node2478 node2478Labels := by
  calc
    mixedMoment B raw16794 raw16794Labels = mixedMoment B raw16794step0 raw16794step0Labels := by
      have ha : raw16794step0 = (fun i j => raw16794 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16794step0 raw16794; decide +kernel
      have hl : raw16794step0Labels = raw16794Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16794 raw16794Labels permutation680 permutation3
    mixedMoment B raw16794step0 raw16794step0Labels = mixedMoment B raw16794step1 raw16794step1Labels := by
      have ha : raw16794step1 = -raw16794step0 := by apply Matrix.ext; change ∀ i j, raw16794step1 i j = -(raw16794step0 i j); unfold raw16794step1 raw16794step0; decide +kernel
      have hl : raw16794step1Labels = raw16794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2478 node2478Labels := by rfl

def raw16795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw16795step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16795 raw16795Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw16795 raw16795Labels = mixedMoment B raw16795step0 raw16795step0Labels := by
      have hz : ∀ j, raw16795 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16795step0 = (fun i j => raw16795 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16795step0 raw16795; decide +kernel
      have hl : raw16795step0Labels = raw16795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16795 raw16795Labels permutation520 hz
    mixedMoment B raw16795step0 raw16795step0Labels = mixedMoment B raw16795step1 raw16795step1Labels := by
      have ha : raw16795step1 = (fun i j => raw16795step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16795step1 raw16795step0; decide +kernel
      have hl : raw16795step1Labels = raw16795step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16795step0 raw16795step0Labels permutation145 permutation3
    mixedMoment B raw16795step1 raw16795step1Labels = mixedMoment B raw16795step2 raw16795step2Labels := by
      have ha : raw16795step2 = -raw16795step1 := by apply Matrix.ext; change ∀ i j, raw16795step2 i j = -(raw16795step1 i j); unfold raw16795step2 raw16795step1; decide +kernel
      have hl : raw16795step2Labels = raw16795step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw16796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16796step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16796 raw16796Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw16796 raw16796Labels = mixedMoment B raw16796step0 raw16796step0Labels := by
      have ha : raw16796step0 = (fun i j => raw16796 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16796step0 raw16796; decide +kernel
      have hl : raw16796step0Labels = raw16796Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16796 raw16796Labels permutation277 permutation7
    mixedMoment B raw16796step0 raw16796step0Labels = mixedMoment B raw16796step1 raw16796step1Labels := by
      have ha : raw16796step1 = -raw16796step0 := by apply Matrix.ext; change ∀ i j, raw16796step1 i j = -(raw16796step0 i j); unfold raw16796step1 raw16796step0; decide +kernel
      have hl : raw16796step1Labels = raw16796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16796step1 raw16796step1Labels = mixedMoment B raw16796step2 raw16796step2Labels := by
      have ha : raw16796step2 = raw16796step1 := by apply Matrix.ext; unfold raw16796step2 raw16796step1; decide +kernel
      have hl : raw16796step1Labels = labelEmbedding1 ∘ raw16796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16796step1 raw16796step1Labels raw16796step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw16797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16797step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16797step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16797 raw16797Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw16797 raw16797Labels = mixedMoment B raw16797step0 raw16797step0Labels := by
      have ha : raw16797step0 = (fun i j => raw16797 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16797step0 raw16797; decide +kernel
      have hl : raw16797step0Labels = raw16797Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16797 raw16797Labels permutation277 permutation7
    mixedMoment B raw16797step0 raw16797step0Labels = mixedMoment B raw16797step1 raw16797step1Labels := by
      have ha : raw16797step1 = -raw16797step0 := by apply Matrix.ext; change ∀ i j, raw16797step1 i j = -(raw16797step0 i j); unfold raw16797step1 raw16797step0; decide +kernel
      have hl : raw16797step1Labels = raw16797step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16797step1 raw16797step1Labels = mixedMoment B raw16797step2 raw16797step2Labels := by
      have ha : raw16797step2 = raw16797step1 := by apply Matrix.ext; unfold raw16797step2 raw16797step1; decide +kernel
      have hl : raw16797step1Labels = labelEmbedding1 ∘ raw16797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16797step1 raw16797step1Labels raw16797step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw16798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16798step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16798 raw16798Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw16798 raw16798Labels = mixedMoment B raw16798step0 raw16798step0Labels := by
      have ha : raw16798step0 = (fun i j => raw16798 (permutation279 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16798step0 raw16798; decide +kernel
      have hl : raw16798step0Labels = raw16798Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16798 raw16798Labels permutation279 permutation7
    mixedMoment B raw16798step0 raw16798step0Labels = mixedMoment B raw16798step1 raw16798step1Labels := by
      have ha : raw16798step1 = -raw16798step0 := by apply Matrix.ext; change ∀ i j, raw16798step1 i j = -(raw16798step0 i j); unfold raw16798step1 raw16798step0; decide +kernel
      have hl : raw16798step1Labels = raw16798step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16798step1 raw16798step1Labels = mixedMoment B raw16798step2 raw16798step2Labels := by
      have ha : raw16798step2 = raw16798step1 := by apply Matrix.ext; unfold raw16798step2 raw16798step1; decide +kernel
      have hl : raw16798step1Labels = labelEmbedding1 ∘ raw16798step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16798step1 raw16798step1Labels raw16798step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw16799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16799step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16799 raw16799Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw16799 raw16799Labels = mixedMoment B raw16799step0 raw16799step0Labels := by
      have hz : ∀ j, raw16799 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16799step0 = (fun i j => raw16799 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16799step0 raw16799; decide +kernel
      have hl : raw16799step0Labels = raw16799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16799 raw16799Labels permutation520 hz
    mixedMoment B raw16799step0 raw16799step0Labels = mixedMoment B raw16799step1 raw16799step1Labels := by
      have ha : raw16799step1 = (fun i j => raw16799step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16799step1 raw16799step0; decide +kernel
      have hl : raw16799step1Labels = raw16799step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16799step0 raw16799step0Labels permutation56 permutation7
    mixedMoment B raw16799step1 raw16799step1Labels = mixedMoment B raw16799step2 raw16799step2Labels := by
      have ha : raw16799step2 = -raw16799step1 := by apply Matrix.ext; change ∀ i j, raw16799step2 i j = -(raw16799step1 i j); unfold raw16799step2 raw16799step1; decide +kernel
      have hl : raw16799step2Labels = raw16799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16799step2 raw16799step2Labels = mixedMoment B raw16799step3 raw16799step3Labels := by
      have ha : raw16799step3 = raw16799step2 := by apply Matrix.ext; unfold raw16799step3 raw16799step2; decide +kernel
      have hl : raw16799step2Labels = labelEmbedding1 ∘ raw16799step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16799step2 raw16799step2Labels raw16799step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw16800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16800step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16800 raw16800Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw16800 raw16800Labels = mixedMoment B raw16800step0 raw16800step0Labels := by
      have ha : raw16800step0 = (fun i j => raw16800 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16800step0 raw16800; decide +kernel
      have hl : raw16800step0Labels = raw16800Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16800 raw16800Labels permutation277 permutation7
    mixedMoment B raw16800step0 raw16800step0Labels = mixedMoment B raw16800step1 raw16800step1Labels := by
      have ha : raw16800step1 = -raw16800step0 := by apply Matrix.ext; change ∀ i j, raw16800step1 i j = -(raw16800step0 i j); unfold raw16800step1 raw16800step0; decide +kernel
      have hl : raw16800step1Labels = raw16800step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16800step1 raw16800step1Labels = mixedMoment B raw16800step2 raw16800step2Labels := by
      have ha : raw16800step2 = raw16800step1 := by apply Matrix.ext; unfold raw16800step2 raw16800step1; decide +kernel
      have hl : raw16800step1Labels = labelEmbedding1 ∘ raw16800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16800step1 raw16800step1Labels raw16800step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw16801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16801step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16801step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16801 raw16801Labels = mixedMoment B node3497 node3497Labels := by
  calc
    mixedMoment B raw16801 raw16801Labels = mixedMoment B raw16801step0 raw16801step0Labels := by
      have ha : raw16801step0 = (fun i j => raw16801 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16801step0 raw16801; decide +kernel
      have hl : raw16801step0Labels = raw16801Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16801 raw16801Labels permutation185 permutation5
    mixedMoment B raw16801step0 raw16801step0Labels = mixedMoment B raw16801step1 raw16801step1Labels := by
      have ha : raw16801step1 = -raw16801step0 := by apply Matrix.ext; change ∀ i j, raw16801step1 i j = -(raw16801step0 i j); unfold raw16801step1 raw16801step0; decide +kernel
      have hl : raw16801step1Labels = raw16801step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16801step1 raw16801step1Labels = mixedMoment B raw16801step2 raw16801step2Labels := by
      have ha : raw16801step2 = raw16801step1 := by apply Matrix.ext; unfold raw16801step2 raw16801step1; decide +kernel
      have hl : raw16801step1Labels = labelEmbedding1 ∘ raw16801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16801step1 raw16801step1Labels raw16801step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3497 node3497Labels := by rfl

def raw16802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16802step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16802 raw16802Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw16802 raw16802Labels = mixedMoment B raw16802step0 raw16802step0Labels := by
      have ha : raw16802step0 = (fun i j => raw16802 (permutation355 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16802step0 raw16802; decide +kernel
      have hl : raw16802step0Labels = raw16802Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16802 raw16802Labels permutation355 permutation5
    mixedMoment B raw16802step0 raw16802step0Labels = mixedMoment B raw16802step1 raw16802step1Labels := by
      have ha : raw16802step1 = -raw16802step0 := by apply Matrix.ext; change ∀ i j, raw16802step1 i j = -(raw16802step0 i j); unfold raw16802step1 raw16802step0; decide +kernel
      have hl : raw16802step1Labels = raw16802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16802step1 raw16802step1Labels = mixedMoment B raw16802step2 raw16802step2Labels := by
      have ha : raw16802step2 = raw16802step1 := by apply Matrix.ext; unfold raw16802step2 raw16802step1; decide +kernel
      have hl : raw16802step1Labels = labelEmbedding1 ∘ raw16802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16802step1 raw16802step1Labels raw16802step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3946 node3946Labels := by rfl

def raw16803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16803step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16803 raw16803Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw16803 raw16803Labels = mixedMoment B raw16803step0 raw16803step0Labels := by
      have ha : raw16803step0 = (fun i j => raw16803 (permutation441 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16803step0 raw16803; decide +kernel
      have hl : raw16803step0Labels = raw16803Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16803 raw16803Labels permutation441 permutation5
    mixedMoment B raw16803step0 raw16803step0Labels = mixedMoment B raw16803step1 raw16803step1Labels := by
      have ha : raw16803step1 = -raw16803step0 := by apply Matrix.ext; change ∀ i j, raw16803step1 i j = -(raw16803step0 i j); unfold raw16803step1 raw16803step0; decide +kernel
      have hl : raw16803step1Labels = raw16803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16803step1 raw16803step1Labels = mixedMoment B raw16803step2 raw16803step2Labels := by
      have ha : raw16803step2 = raw16803step1 := by apply Matrix.ext; unfold raw16803step2 raw16803step1; decide +kernel
      have hl : raw16803step1Labels = labelEmbedding1 ∘ raw16803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16803step1 raw16803step1Labels raw16803step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3946 node3946Labels := by rfl

def raw16804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16804 raw16804Labels = mixedMoment B node4028 node4028Labels := by
  calc
    mixedMoment B raw16804 raw16804Labels = mixedMoment B raw16804step0 raw16804step0Labels := by
      have hz : ∀ j, raw16804 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16804step0 = (fun i j => raw16804 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16804step0 raw16804; decide +kernel
      have hl : raw16804step0Labels = raw16804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16804 raw16804Labels permutation520 hz
    mixedMoment B raw16804step0 raw16804step0Labels = mixedMoment B raw16804step1 raw16804step1Labels := by
      have ha : raw16804step1 = (fun i j => raw16804step0 (permutation77 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16804step1 raw16804step0; decide +kernel
      have hl : raw16804step1Labels = raw16804step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16804step0 raw16804step0Labels permutation77 permutation5
    mixedMoment B raw16804step1 raw16804step1Labels = mixedMoment B raw16804step2 raw16804step2Labels := by
      have ha : raw16804step2 = raw16804step1 := by apply Matrix.ext; unfold raw16804step2 raw16804step1; decide +kernel
      have hl : raw16804step1Labels = labelEmbedding1 ∘ raw16804step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16804step1 raw16804step1Labels raw16804step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4028 node4028Labels := by rfl

def raw16805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16805step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16805step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16805 raw16805Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw16805 raw16805Labels = mixedMoment B raw16805step0 raw16805step0Labels := by
      have ha : raw16805step0 = (fun i j => raw16805 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16805step0 raw16805; decide +kernel
      have hl : raw16805step0Labels = raw16805Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16805 raw16805Labels permutation277 permutation7
    mixedMoment B raw16805step0 raw16805step0Labels = mixedMoment B raw16805step1 raw16805step1Labels := by
      have ha : raw16805step1 = -raw16805step0 := by apply Matrix.ext; change ∀ i j, raw16805step1 i j = -(raw16805step0 i j); unfold raw16805step1 raw16805step0; decide +kernel
      have hl : raw16805step1Labels = raw16805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16805step1 raw16805step1Labels = mixedMoment B raw16805step2 raw16805step2Labels := by
      have ha : raw16805step2 = raw16805step1 := by apply Matrix.ext; unfold raw16805step2 raw16805step1; decide +kernel
      have hl : raw16805step1Labels = labelEmbedding1 ∘ raw16805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16805step1 raw16805step1Labels raw16805step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw16806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16806step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16806step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16806 raw16806Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw16806 raw16806Labels = mixedMoment B raw16806step0 raw16806step0Labels := by
      have ha : raw16806step0 = (fun i j => raw16806 (permutation206 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16806step0 raw16806; decide +kernel
      have hl : raw16806step0Labels = raw16806Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16806 raw16806Labels permutation206 permutation5
    mixedMoment B raw16806step0 raw16806step0Labels = mixedMoment B raw16806step1 raw16806step1Labels := by
      have ha : raw16806step1 = -raw16806step0 := by apply Matrix.ext; change ∀ i j, raw16806step1 i j = -(raw16806step0 i j); unfold raw16806step1 raw16806step0; decide +kernel
      have hl : raw16806step1Labels = raw16806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16806step1 raw16806step1Labels = mixedMoment B raw16806step2 raw16806step2Labels := by
      have ha : raw16806step2 = raw16806step1 := by apply Matrix.ext; unfold raw16806step2 raw16806step1; decide +kernel
      have hl : raw16806step1Labels = labelEmbedding1 ∘ raw16806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16806step1 raw16806step1Labels raw16806step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw16807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16807step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16807 raw16807Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw16807 raw16807Labels = mixedMoment B raw16807step0 raw16807step0Labels := by
      have ha : raw16807step0 = (fun i j => raw16807 (permutation279 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16807step0 raw16807; decide +kernel
      have hl : raw16807step0Labels = raw16807Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16807 raw16807Labels permutation279 permutation7
    mixedMoment B raw16807step0 raw16807step0Labels = mixedMoment B raw16807step1 raw16807step1Labels := by
      have ha : raw16807step1 = -raw16807step0 := by apply Matrix.ext; change ∀ i j, raw16807step1 i j = -(raw16807step0 i j); unfold raw16807step1 raw16807step0; decide +kernel
      have hl : raw16807step1Labels = raw16807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16807step1 raw16807step1Labels = mixedMoment B raw16807step2 raw16807step2Labels := by
      have ha : raw16807step2 = raw16807step1 := by apply Matrix.ext; unfold raw16807step2 raw16807step1; decide +kernel
      have hl : raw16807step1Labels = labelEmbedding1 ∘ raw16807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16807step1 raw16807step1Labels raw16807step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

def raw16808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16808step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16808step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16808 raw16808Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw16808 raw16808Labels = mixedMoment B raw16808step0 raw16808step0Labels := by
      have ha : raw16808step0 = (fun i j => raw16808 (permutation440 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16808step0 raw16808; decide +kernel
      have hl : raw16808step0Labels = raw16808Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16808 raw16808Labels permutation440 permutation5
    mixedMoment B raw16808step0 raw16808step0Labels = mixedMoment B raw16808step1 raw16808step1Labels := by
      have ha : raw16808step1 = -raw16808step0 := by apply Matrix.ext; change ∀ i j, raw16808step1 i j = -(raw16808step0 i j); unfold raw16808step1 raw16808step0; decide +kernel
      have hl : raw16808step1Labels = raw16808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16808step1 raw16808step1Labels = mixedMoment B raw16808step2 raw16808step2Labels := by
      have ha : raw16808step2 = raw16808step1 := by apply Matrix.ext; unfold raw16808step2 raw16808step1; decide +kernel
      have hl : raw16808step1Labels = labelEmbedding1 ∘ raw16808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16808step1 raw16808step1Labels raw16808step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3955 node3955Labels := by rfl

def raw16809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16809step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16809step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16809step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16809step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16809step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16809 raw16809Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw16809 raw16809Labels = mixedMoment B raw16809step0 raw16809step0Labels := by
      have hz : ∀ j, raw16809 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16809step0 = (fun i j => raw16809 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16809step0 raw16809; decide +kernel
      have hl : raw16809step0Labels = raw16809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16809 raw16809Labels permutation520 hz
    mixedMoment B raw16809step0 raw16809step0Labels = mixedMoment B raw16809step1 raw16809step1Labels := by
      have ha : raw16809step1 = (fun i j => raw16809step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16809step1 raw16809step0; decide +kernel
      have hl : raw16809step1Labels = raw16809step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16809step0 raw16809step0Labels permutation58 permutation7
    mixedMoment B raw16809step1 raw16809step1Labels = mixedMoment B raw16809step2 raw16809step2Labels := by
      have ha : raw16809step2 = -raw16809step1 := by apply Matrix.ext; change ∀ i j, raw16809step2 i j = -(raw16809step1 i j); unfold raw16809step2 raw16809step1; decide +kernel
      have hl : raw16809step2Labels = raw16809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16809step2 raw16809step2Labels = mixedMoment B raw16809step3 raw16809step3Labels := by
      have ha : raw16809step3 = raw16809step2 := by apply Matrix.ext; unfold raw16809step3 raw16809step2; decide +kernel
      have hl : raw16809step2Labels = labelEmbedding1 ∘ raw16809step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16809step2 raw16809step2Labels raw16809step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw16810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16810step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16810step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16810step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16810 raw16810Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw16810 raw16810Labels = mixedMoment B raw16810step0 raw16810step0Labels := by
      have ha : raw16810step0 = (fun i j => raw16810 (permutation279 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16810step0 raw16810; decide +kernel
      have hl : raw16810step0Labels = raw16810Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16810 raw16810Labels permutation279 permutation7
    mixedMoment B raw16810step0 raw16810step0Labels = mixedMoment B raw16810step1 raw16810step1Labels := by
      have ha : raw16810step1 = -raw16810step0 := by apply Matrix.ext; change ∀ i j, raw16810step1 i j = -(raw16810step0 i j); unfold raw16810step1 raw16810step0; decide +kernel
      have hl : raw16810step1Labels = raw16810step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16810step1 raw16810step1Labels = mixedMoment B raw16810step2 raw16810step2Labels := by
      have ha : raw16810step2 = raw16810step1 := by apply Matrix.ext; unfold raw16810step2 raw16810step1; decide +kernel
      have hl : raw16810step1Labels = labelEmbedding1 ∘ raw16810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16810step1 raw16810step1Labels raw16810step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw16811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16811step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16811step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16811step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16811 raw16811Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw16811 raw16811Labels = mixedMoment B raw16811step0 raw16811step0Labels := by
      have ha : raw16811step0 = (fun i j => raw16811 (permutation182 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16811step0 raw16811; decide +kernel
      have hl : raw16811step0Labels = raw16811Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16811 raw16811Labels permutation182 permutation5
    mixedMoment B raw16811step0 raw16811step0Labels = mixedMoment B raw16811step1 raw16811step1Labels := by
      have ha : raw16811step1 = -raw16811step0 := by apply Matrix.ext; change ∀ i j, raw16811step1 i j = -(raw16811step0 i j); unfold raw16811step1 raw16811step0; decide +kernel
      have hl : raw16811step1Labels = raw16811step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16811step1 raw16811step1Labels = mixedMoment B raw16811step2 raw16811step2Labels := by
      have ha : raw16811step2 = raw16811step1 := by apply Matrix.ext; unfold raw16811step2 raw16811step1; decide +kernel
      have hl : raw16811step1Labels = labelEmbedding1 ∘ raw16811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16811step1 raw16811step1Labels raw16811step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw16812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16812step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16812 raw16812Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw16812 raw16812Labels = mixedMoment B raw16812step0 raw16812step0Labels := by
      have ha : raw16812step0 = (fun i j => raw16812 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16812step0 raw16812; decide +kernel
      have hl : raw16812step0Labels = raw16812Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16812 raw16812Labels permutation277 permutation7
    mixedMoment B raw16812step0 raw16812step0Labels = mixedMoment B raw16812step1 raw16812step1Labels := by
      have ha : raw16812step1 = -raw16812step0 := by apply Matrix.ext; change ∀ i j, raw16812step1 i j = -(raw16812step0 i j); unfold raw16812step1 raw16812step0; decide +kernel
      have hl : raw16812step1Labels = raw16812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16812step1 raw16812step1Labels = mixedMoment B raw16812step2 raw16812step2Labels := by
      have ha : raw16812step2 = raw16812step1 := by apply Matrix.ext; unfold raw16812step2 raw16812step1; decide +kernel
      have hl : raw16812step1Labels = labelEmbedding1 ∘ raw16812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16812step1 raw16812step1Labels raw16812step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

def raw16813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16813step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16813step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16813step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16813 raw16813Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw16813 raw16813Labels = mixedMoment B raw16813step0 raw16813step0Labels := by
      have ha : raw16813step0 = (fun i j => raw16813 (permutation352 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16813step0 raw16813; decide +kernel
      have hl : raw16813step0Labels = raw16813Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16813 raw16813Labels permutation352 permutation5
    mixedMoment B raw16813step0 raw16813step0Labels = mixedMoment B raw16813step1 raw16813step1Labels := by
      have ha : raw16813step1 = -raw16813step0 := by apply Matrix.ext; change ∀ i j, raw16813step1 i j = -(raw16813step0 i j); unfold raw16813step1 raw16813step0; decide +kernel
      have hl : raw16813step1Labels = raw16813step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16813step1 raw16813step1Labels = mixedMoment B raw16813step2 raw16813step2Labels := by
      have ha : raw16813step2 = raw16813step1 := by apply Matrix.ext; unfold raw16813step2 raw16813step1; decide +kernel
      have hl : raw16813step1Labels = labelEmbedding1 ∘ raw16813step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16813step1 raw16813step1Labels raw16813step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3955 node3955Labels := by rfl

def raw16814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16814step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16814step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16814step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16814step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16814 raw16814Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw16814 raw16814Labels = mixedMoment B raw16814step0 raw16814step0Labels := by
      have hz : ∀ j, raw16814 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16814step0 = (fun i j => raw16814 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16814step0 raw16814; decide +kernel
      have hl : raw16814step0Labels = raw16814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16814 raw16814Labels permutation520 hz
    mixedMoment B raw16814step0 raw16814step0Labels = mixedMoment B raw16814step1 raw16814step1Labels := by
      have ha : raw16814step1 = (fun i j => raw16814step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16814step1 raw16814step0; decide +kernel
      have hl : raw16814step1Labels = raw16814step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16814step0 raw16814step0Labels permutation56 permutation7
    mixedMoment B raw16814step1 raw16814step1Labels = mixedMoment B raw16814step2 raw16814step2Labels := by
      have ha : raw16814step2 = -raw16814step1 := by apply Matrix.ext; change ∀ i j, raw16814step2 i j = -(raw16814step1 i j); unfold raw16814step2 raw16814step1; decide +kernel
      have hl : raw16814step2Labels = raw16814step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16814step2 raw16814step2Labels = mixedMoment B raw16814step3 raw16814step3Labels := by
      have ha : raw16814step3 = raw16814step2 := by apply Matrix.ext; unfold raw16814step3 raw16814step2; decide +kernel
      have hl : raw16814step2Labels = labelEmbedding1 ∘ raw16814step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16814step2 raw16814step2Labels raw16814step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw16815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16815step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16815step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16815 raw16815Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw16815 raw16815Labels = mixedMoment B raw16815step0 raw16815step0Labels := by
      have ha : raw16815step0 = (fun i j => raw16815 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16815step0 raw16815; decide +kernel
      have hl : raw16815step0Labels = raw16815Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16815 raw16815Labels permutation277 permutation7
    mixedMoment B raw16815step0 raw16815step0Labels = mixedMoment B raw16815step1 raw16815step1Labels := by
      have ha : raw16815step1 = -raw16815step0 := by apply Matrix.ext; change ∀ i j, raw16815step1 i j = -(raw16815step0 i j); unfold raw16815step1 raw16815step0; decide +kernel
      have hl : raw16815step1Labels = raw16815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16815step1 raw16815step1Labels = mixedMoment B raw16815step2 raw16815step2Labels := by
      have ha : raw16815step2 = raw16815step1 := by apply Matrix.ext; unfold raw16815step2 raw16815step1; decide +kernel
      have hl : raw16815step1Labels = labelEmbedding1 ∘ raw16815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16815step1 raw16815step1Labels raw16815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw16816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16816step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16816step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16816 raw16816Labels = mixedMoment B node3491 node3491Labels := by
  calc
    mixedMoment B raw16816 raw16816Labels = mixedMoment B raw16816step0 raw16816step0Labels := by
      have ha : raw16816step0 = (fun i j => raw16816 (permutation183 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16816step0 raw16816; decide +kernel
      have hl : raw16816step0Labels = raw16816Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16816 raw16816Labels permutation183 permutation5
    mixedMoment B raw16816step0 raw16816step0Labels = mixedMoment B raw16816step1 raw16816step1Labels := by
      have ha : raw16816step1 = -raw16816step0 := by apply Matrix.ext; change ∀ i j, raw16816step1 i j = -(raw16816step0 i j); unfold raw16816step1 raw16816step0; decide +kernel
      have hl : raw16816step1Labels = raw16816step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16816step1 raw16816step1Labels = mixedMoment B raw16816step2 raw16816step2Labels := by
      have ha : raw16816step2 = raw16816step1 := by apply Matrix.ext; unfold raw16816step2 raw16816step1; decide +kernel
      have hl : raw16816step1Labels = labelEmbedding1 ∘ raw16816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16816step1 raw16816step1Labels raw16816step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3491 node3491Labels := by rfl

def raw16817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16817 raw16817Labels = mixedMoment B node3768 node3768Labels := by
  calc
    mixedMoment B raw16817 raw16817Labels = mixedMoment B raw16817step0 raw16817step0Labels := by
      have ha : raw16817step0 = (fun i j => raw16817 (permutation577 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16817step0 raw16817; decide +kernel
      have hl : raw16817step0Labels = raw16817Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16817 raw16817Labels permutation577 permutation5
    mixedMoment B raw16817step0 raw16817step0Labels = mixedMoment B raw16817step1 raw16817step1Labels := by
      have ha : raw16817step1 = raw16817step0 := by apply Matrix.ext; unfold raw16817step1 raw16817step0; decide +kernel
      have hl : raw16817step0Labels = labelEmbedding1 ∘ raw16817step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16817step0 raw16817step0Labels raw16817step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3768 node3768Labels := by rfl

def raw16818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16818step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16818 raw16818Labels = mixedMoment B node3750 node3750Labels := by
  calc
    mixedMoment B raw16818 raw16818Labels = mixedMoment B raw16818step0 raw16818step0Labels := by
      have ha : raw16818step0 = (fun i j => raw16818 (permutation578 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16818step0 raw16818; decide +kernel
      have hl : raw16818step0Labels = raw16818Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16818 raw16818Labels permutation578 permutation5
    mixedMoment B raw16818step0 raw16818step0Labels = mixedMoment B raw16818step1 raw16818step1Labels := by
      have ha : raw16818step1 = raw16818step0 := by apply Matrix.ext; unfold raw16818step1 raw16818step0; decide +kernel
      have hl : raw16818step0Labels = labelEmbedding1 ∘ raw16818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16818step0 raw16818step0Labels raw16818step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3750 node3750Labels := by rfl

def raw16819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16819step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16819 raw16819Labels = mixedMoment B node3750 node3750Labels := by
  calc
    mixedMoment B raw16819 raw16819Labels = mixedMoment B raw16819step0 raw16819step0Labels := by
      have ha : raw16819step0 = (fun i j => raw16819 (permutation576 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16819step0 raw16819; decide +kernel
      have hl : raw16819step0Labels = raw16819Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16819 raw16819Labels permutation576 permutation5
    mixedMoment B raw16819step0 raw16819step0Labels = mixedMoment B raw16819step1 raw16819step1Labels := by
      have ha : raw16819step1 = raw16819step0 := by apply Matrix.ext; unfold raw16819step1 raw16819step0; decide +kernel
      have hl : raw16819step0Labels = labelEmbedding1 ∘ raw16819step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16819step0 raw16819step0Labels raw16819step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3750 node3750Labels := by rfl

def raw16820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw16820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16820 raw16820Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw16820 raw16820Labels = mixedMoment B raw16820step0 raw16820step0Labels := by
      have ha : raw16820step0 = (fun i j => raw16820 (permutation540 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16820step0 raw16820; decide +kernel
      have hl : raw16820step0Labels = raw16820Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16820 raw16820Labels permutation540 permutation5
    mixedMoment B raw16820step0 raw16820step0Labels = mixedMoment B raw16820step1 raw16820step1Labels := by
      have ha : raw16820step1 = raw16820step0 := by apply Matrix.ext; unfold raw16820step1 raw16820step0; decide +kernel
      have hl : raw16820step0Labels = labelEmbedding1 ∘ raw16820step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16820step0 raw16820step0Labels raw16820step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw16821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw16821step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16821step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw16821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16821 raw16821Labels = mixedMoment B node3443 node3443Labels := by
  calc
    mixedMoment B raw16821 raw16821Labels = mixedMoment B raw16821step0 raw16821step0Labels := by
      have ha : raw16821step0 = (fun i j => raw16821 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16821step0 raw16821; decide +kernel
      have hl : raw16821step0Labels = raw16821Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16821 raw16821Labels permutation674 permutation5
    mixedMoment B raw16821step0 raw16821step0Labels = mixedMoment B raw16821step1 raw16821step1Labels := by
      have ha : raw16821step1 = raw16821step0 := by apply Matrix.ext; unfold raw16821step1 raw16821step0; decide +kernel
      have hl : raw16821step0Labels = labelEmbedding1 ∘ raw16821step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16821step0 raw16821step0Labels raw16821step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3443 node3443Labels := by rfl

def raw16822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16822step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16822 raw16822Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw16822 raw16822Labels = mixedMoment B raw16822step0 raw16822step0Labels := by
      have ha : raw16822step0 = (fun i j => raw16822 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16822step0 raw16822; decide +kernel
      have hl : raw16822step0Labels = raw16822Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16822 raw16822Labels permutation674 permutation5
    mixedMoment B raw16822step0 raw16822step0Labels = mixedMoment B raw16822step1 raw16822step1Labels := by
      have ha : raw16822step1 = raw16822step0 := by apply Matrix.ext; unfold raw16822step1 raw16822step0; decide +kernel
      have hl : raw16822step0Labels = labelEmbedding1 ∘ raw16822step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16822step0 raw16822step0Labels raw16822step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

def raw16823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16823step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16823 raw16823Labels = mixedMoment B node3445 node3445Labels := by
  calc
    mixedMoment B raw16823 raw16823Labels = mixedMoment B raw16823step0 raw16823step0Labels := by
      have ha : raw16823step0 = (fun i j => raw16823 (permutation675 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16823step0 raw16823; decide +kernel
      have hl : raw16823step0Labels = raw16823Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16823 raw16823Labels permutation675 permutation5
    mixedMoment B raw16823step0 raw16823step0Labels = mixedMoment B raw16823step1 raw16823step1Labels := by
      have ha : raw16823step1 = raw16823step0 := by apply Matrix.ext; unfold raw16823step1 raw16823step0; decide +kernel
      have hl : raw16823step0Labels = labelEmbedding1 ∘ raw16823step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16823step0 raw16823step0Labels raw16823step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3445 node3445Labels := by rfl

def raw16824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16824 raw16824Labels = mixedMoment B node3445 node3445Labels := by
  calc
    mixedMoment B raw16824 raw16824Labels = mixedMoment B raw16824step0 raw16824step0Labels := by
      have ha : raw16824step0 = (fun i j => raw16824 (permutation673 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16824step0 raw16824; decide +kernel
      have hl : raw16824step0Labels = raw16824Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16824 raw16824Labels permutation673 permutation5
    mixedMoment B raw16824step0 raw16824step0Labels = mixedMoment B raw16824step1 raw16824step1Labels := by
      have ha : raw16824step1 = raw16824step0 := by apply Matrix.ext; unfold raw16824step1 raw16824step0; decide +kernel
      have hl : raw16824step0Labels = labelEmbedding1 ∘ raw16824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16824step0 raw16824step0Labels raw16824step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3445 node3445Labels := by rfl

def raw16825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw16825step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16825step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16825 raw16825Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw16825 raw16825Labels = mixedMoment B raw16825step0 raw16825step0Labels := by
      have hz : ∀ j, raw16825 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16825step0 = (fun i j => raw16825 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16825step0 raw16825; decide +kernel
      have hl : raw16825step0Labels = raw16825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16825 raw16825Labels permutation520 hz
    mixedMoment B raw16825step0 raw16825step0Labels = mixedMoment B raw16825step1 raw16825step1Labels := by
      have ha : raw16825step1 = (fun i j => raw16825step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16825step1 raw16825step0; decide +kernel
      have hl : raw16825step1Labels = raw16825step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16825step0 raw16825step0Labels permutation137 permutation5
    mixedMoment B raw16825step1 raw16825step1Labels = mixedMoment B raw16825step2 raw16825step2Labels := by
      have ha : raw16825step2 = raw16825step1 := by apply Matrix.ext; unfold raw16825step2 raw16825step1; decide +kernel
      have hl : raw16825step1Labels = labelEmbedding1 ∘ raw16825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16825step1 raw16825step1Labels raw16825step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw16826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16826 raw16826Labels = mixedMoment B node3953 node3953Labels := by
  calc
    _ = mixedMoment B node3953 node3953Labels := by rfl

def raw16827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16827 raw16827Labels = mixedMoment B node3029 node3029Labels := by
  calc
    _ = mixedMoment B node3029 node3029Labels := by rfl

def raw16828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16828 raw16828Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw16828 raw16828Labels = mixedMoment B raw16828step0 raw16828step0Labels := by
      have ha : raw16828step0 = (fun i j => raw16828 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16828step0 raw16828; decide +kernel
      have hl : raw16828step0Labels = raw16828Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16828 raw16828Labels permutation160 permutation2
    _ = mixedMoment B node2862 node2862Labels := by rfl

def raw16829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16829 raw16829Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw16829 raw16829Labels = mixedMoment B raw16829step0 raw16829step0Labels := by
      have ha : raw16829step0 = (fun i j => raw16829 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16829step0 raw16829; decide +kernel
      have hl : raw16829step0Labels = raw16829Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16829 raw16829Labels permutation154 permutation2
    _ = mixedMoment B node2862 node2862Labels := by rfl

def raw16830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16830 raw16830Labels = mixedMoment B node2859 node2859Labels := by
  calc
    _ = mixedMoment B node2859 node2859Labels := by rfl

def raw16831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16831 raw16831Labels = mixedMoment B node2857 node2857Labels := by
  calc
    _ = mixedMoment B node2857 node2857Labels := by rfl

def raw16832 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw16832Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16832step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw16832step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16832step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw16832step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical16832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16832 raw16832Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw16832 raw16832Labels = mixedMoment B raw16832step0 raw16832step0Labels := by
      have hz : ∀ j, raw16832 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16832step0 = (fun i j => raw16832 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16832step0 raw16832; decide +kernel
      have hl : raw16832step0Labels = raw16832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16832 raw16832Labels permutation520 hz
    mixedMoment B raw16832step0 raw16832step0Labels = mixedMoment B raw16832step1 raw16832step1Labels := by
      have ha : raw16832step1 = (fun i j => raw16832step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16832step1 raw16832step0; decide +kernel
      have hl : raw16832step1Labels = raw16832step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16832step0 raw16832step0Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw16833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16833 raw16833Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw16833 raw16833Labels = mixedMoment B raw16833step0 raw16833step0Labels := by
      have ha : raw16833step0 = (fun i j => raw16833 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16833step0 raw16833; decide +kernel
      have hl : raw16833step0Labels = raw16833Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16833 raw16833Labels permutation265 permutation2
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw16834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16834 raw16834Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw16834 raw16834Labels = mixedMoment B raw16834step0 raw16834step0Labels := by
      have ha : raw16834step0 = (fun i j => raw16834 (permutation273 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16834step0 raw16834; decide +kernel
      have hl : raw16834step0Labels = raw16834Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16834 raw16834Labels permutation273 permutation2
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw16835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16835 raw16835Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw16835 raw16835Labels = mixedMoment B raw16835step0 raw16835step0Labels := by
      have ha : raw16835step0 = (fun i j => raw16835 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16835step0 raw16835; decide +kernel
      have hl : raw16835step0Labels = raw16835Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16835 raw16835Labels permutation267 permutation2
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw16836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16836 raw16836Labels = mixedMoment B node3685 node3685Labels := by
  calc
    mixedMoment B raw16836 raw16836Labels = mixedMoment B raw16836step0 raw16836step0Labels := by
      have ha : raw16836step0 = (fun i j => raw16836 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16836step0 raw16836; decide +kernel
      have hl : raw16836step0Labels = raw16836Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16836 raw16836Labels permutation265 permutation2
    _ = mixedMoment B node3685 node3685Labels := by rfl

def raw16837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw16837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16837 raw16837Labels = mixedMoment B node2981 node2981Labels := by
  calc
    mixedMoment B raw16837 raw16837Labels = mixedMoment B raw16837step0 raw16837step0Labels := by
      have ha : raw16837step0 = (fun i j => raw16837 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16837step0 raw16837; decide +kernel
      have hl : raw16837step0Labels = raw16837Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16837 raw16837Labels permutation681 permutation2
    mixedMoment B raw16837step0 raw16837step0Labels = mixedMoment B raw16837step1 raw16837step1Labels := by
      have ha : raw16837step1 = -raw16837step0 := by apply Matrix.ext; change ∀ i j, raw16837step1 i j = -(raw16837step0 i j); unfold raw16837step1 raw16837step0; decide +kernel
      have hl : raw16837step1Labels = raw16837step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2981 node2981Labels := by rfl

def raw16838 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16838step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16838step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16838step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16838step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16838 raw16838Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw16838 raw16838Labels = mixedMoment B raw16838step0 raw16838step0Labels := by
      have ha : raw16838step0 = (fun i j => raw16838 (permutation324 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16838step0 raw16838; decide +kernel
      have hl : raw16838step0Labels = raw16838Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16838 raw16838Labels permutation324 permutation5
    mixedMoment B raw16838step0 raw16838step0Labels = mixedMoment B raw16838step1 raw16838step1Labels := by
      have ha : raw16838step1 = -raw16838step0 := by apply Matrix.ext; change ∀ i j, raw16838step1 i j = -(raw16838step0 i j); unfold raw16838step1 raw16838step0; decide +kernel
      have hl : raw16838step1Labels = raw16838step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16838step1 raw16838step1Labels = mixedMoment B raw16838step2 raw16838step2Labels := by
      have ha : raw16838step2 = raw16838step1 := by apply Matrix.ext; unfold raw16838step2 raw16838step1; decide +kernel
      have hl : raw16838step1Labels = labelEmbedding8 ∘ raw16838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16838step1 raw16838step1Labels raw16838step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

def raw16839 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16839step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16839 raw16839Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw16839 raw16839Labels = mixedMoment B raw16839step0 raw16839step0Labels := by
      have hz : ∀ j, raw16839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16839step0 = (fun i j => raw16839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16839step0 raw16839; decide +kernel
      have hl : raw16839step0Labels = raw16839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16839 raw16839Labels permutation346 hz
    mixedMoment B raw16839step0 raw16839step0Labels = mixedMoment B raw16839step1 raw16839step1Labels := by
      have ha : raw16839step1 = (fun i j => raw16839step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16839step1 raw16839step0; decide +kernel
      have hl : raw16839step1Labels = raw16839step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16839step0 raw16839step0Labels permutation38 permutation2
    mixedMoment B raw16839step1 raw16839step1Labels = mixedMoment B raw16839step2 raw16839step2Labels := by
      have ha : raw16839step2 = -raw16839step1 := by apply Matrix.ext; change ∀ i j, raw16839step2 i j = -(raw16839step1 i j); unfold raw16839step2 raw16839step1; decide +kernel
      have hl : raw16839step2Labels = raw16839step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw16840 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16840step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16840step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16840 raw16840Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw16840 raw16840Labels = mixedMoment B raw16840step0 raw16840step0Labels := by
      have hz : ∀ j, raw16840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16840step0 = (fun i j => raw16840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16840step0 raw16840; decide +kernel
      have hl : raw16840step0Labels = raw16840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16840 raw16840Labels permutation434 hz
    mixedMoment B raw16840step0 raw16840step0Labels = mixedMoment B raw16840step1 raw16840step1Labels := by
      have ha : raw16840step1 = (fun i j => raw16840step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16840step1 raw16840step0; decide +kernel
      have hl : raw16840step1Labels = raw16840step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16840step0 raw16840step0Labels permutation38 permutation2
    mixedMoment B raw16840step1 raw16840step1Labels = mixedMoment B raw16840step2 raw16840step2Labels := by
      have ha : raw16840step2 = -raw16840step1 := by apply Matrix.ext; change ∀ i j, raw16840step2 i j = -(raw16840step1 i j); unfold raw16840step2 raw16840step1; decide +kernel
      have hl : raw16840step2Labels = raw16840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw16841 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16841 raw16841Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw16841 raw16841Labels = mixedMoment B raw16841step0 raw16841step0Labels := by
      have ha : raw16841step0 = (fun i j => raw16841 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16841step0 raw16841; decide +kernel
      have hl : raw16841step0Labels = raw16841Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16841 raw16841Labels permutation183 permutation2
    mixedMoment B raw16841step0 raw16841step0Labels = mixedMoment B raw16841step1 raw16841step1Labels := by
      have ha : raw16841step1 = -raw16841step0 := by apply Matrix.ext; change ∀ i j, raw16841step1 i j = -(raw16841step0 i j); unfold raw16841step1 raw16841step0; decide +kernel
      have hl : raw16841step1Labels = raw16841step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw16842 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16842 raw16842Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw16842 raw16842Labels = mixedMoment B raw16842step0 raw16842step0Labels := by
      have ha : raw16842step0 = (fun i j => raw16842 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16842step0 raw16842; decide +kernel
      have hl : raw16842step0Labels = raw16842Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16842 raw16842Labels permutation674 permutation2
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw16843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16843step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16843 raw16843Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw16843 raw16843Labels = mixedMoment B raw16843step0 raw16843step0Labels := by
      have hz : ∀ j, raw16843 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16843step0 = (fun i j => raw16843 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16843step0 raw16843; decide +kernel
      have hl : raw16843step0Labels = raw16843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16843 raw16843Labels permutation434 hz
    mixedMoment B raw16843step0 raw16843step0Labels = mixedMoment B raw16843step1 raw16843step1Labels := by
      have ha : raw16843step1 = (fun i j => raw16843step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16843step1 raw16843step0; decide +kernel
      have hl : raw16843step1Labels = raw16843step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16843step0 raw16843step0Labels permutation32 permutation6
    mixedMoment B raw16843step1 raw16843step1Labels = mixedMoment B raw16843step2 raw16843step2Labels := by
      have ha : raw16843step2 = raw16843step1 := by apply Matrix.ext; unfold raw16843step2 raw16843step1; decide +kernel
      have hl : raw16843step1Labels = labelEmbedding9 ∘ raw16843step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16843step1 raw16843step1Labels raw16843step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw16844 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16844step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16844step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16844step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16844step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16844 raw16844Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw16844 raw16844Labels = mixedMoment B raw16844step0 raw16844step0Labels := by
      have ha : raw16844step0 = (fun i j => raw16844 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16844step0 raw16844; decide +kernel
      have hl : raw16844step0Labels = raw16844Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16844 raw16844Labels permutation167 permutation4
    mixedMoment B raw16844step0 raw16844step0Labels = mixedMoment B raw16844step1 raw16844step1Labels := by
      have ha : raw16844step1 = -raw16844step0 := by apply Matrix.ext; change ∀ i j, raw16844step1 i j = -(raw16844step0 i j); unfold raw16844step1 raw16844step0; decide +kernel
      have hl : raw16844step1Labels = raw16844step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16844step1 raw16844step1Labels = mixedMoment B raw16844step2 raw16844step2Labels := by
      have ha : raw16844step2 = raw16844step1 := by apply Matrix.ext; unfold raw16844step2 raw16844step1; decide +kernel
      have hl : raw16844step1Labels = labelEmbedding7 ∘ raw16844step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16844step1 raw16844step1Labels raw16844step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw16845 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16845step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16845step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16845step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16845 raw16845Labels = mixedMoment B node5183 node5183Labels := by
  calc
    mixedMoment B raw16845 raw16845Labels = mixedMoment B raw16845step0 raw16845step0Labels := by
      have ha : raw16845step0 = (fun i j => raw16845 (permutation282 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16845step0 raw16845; decide +kernel
      have hl : raw16845step0Labels = raw16845Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16845 raw16845Labels permutation282 permutation5
    mixedMoment B raw16845step0 raw16845step0Labels = mixedMoment B raw16845step1 raw16845step1Labels := by
      have ha : raw16845step1 = -raw16845step0 := by apply Matrix.ext; change ∀ i j, raw16845step1 i j = -(raw16845step0 i j); unfold raw16845step1 raw16845step0; decide +kernel
      have hl : raw16845step1Labels = raw16845step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16845step1 raw16845step1Labels = mixedMoment B raw16845step2 raw16845step2Labels := by
      have ha : raw16845step2 = raw16845step1 := by apply Matrix.ext; unfold raw16845step2 raw16845step1; decide +kernel
      have hl : raw16845step1Labels = labelEmbedding8 ∘ raw16845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16845step1 raw16845step1Labels raw16845step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5183 node5183Labels := by rfl

def raw16846 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16846step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16846step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16846step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16846 raw16846Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw16846 raw16846Labels = mixedMoment B raw16846step0 raw16846step0Labels := by
      have hz : ∀ j, raw16846 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16846step0 = (fun i j => raw16846 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16846step0 raw16846; decide +kernel
      have hl : raw16846step0Labels = raw16846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16846 raw16846Labels permutation434 hz
    mixedMoment B raw16846step0 raw16846step0Labels = mixedMoment B raw16846step1 raw16846step1Labels := by
      have ha : raw16846step1 = (fun i j => raw16846step0 (permutation102 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16846step1 raw16846step0; decide +kernel
      have hl : raw16846step1Labels = raw16846step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16846step0 raw16846step0Labels permutation102 permutation5
    mixedMoment B raw16846step1 raw16846step1Labels = mixedMoment B raw16846step2 raw16846step2Labels := by
      have ha : raw16846step2 = raw16846step1 := by apply Matrix.ext; unfold raw16846step2 raw16846step1; decide +kernel
      have hl : raw16846step1Labels = labelEmbedding8 ∘ raw16846step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16846step1 raw16846step1Labels raw16846step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw16847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16847step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16847step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16847step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16847step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16847step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16847 raw16847Labels = mixedMoment B node5399 node5399Labels := by
  calc
    mixedMoment B raw16847 raw16847Labels = mixedMoment B raw16847step0 raw16847step0Labels := by
      have ha : raw16847step0 = (fun i j => raw16847 (permutation384 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16847step0 raw16847; decide +kernel
      have hl : raw16847step0Labels = raw16847Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16847 raw16847Labels permutation384 permutation3
    mixedMoment B raw16847step0 raw16847step0Labels = mixedMoment B raw16847step1 raw16847step1Labels := by
      have ha : raw16847step1 = -raw16847step0 := by apply Matrix.ext; change ∀ i j, raw16847step1 i j = -(raw16847step0 i j); unfold raw16847step1 raw16847step0; decide +kernel
      have hl : raw16847step1Labels = raw16847step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16847step1 raw16847step1Labels = mixedMoment B raw16847step2 raw16847step2Labels := by
      have ha : raw16847step2 = raw16847step1 := by apply Matrix.ext; unfold raw16847step2 raw16847step1; decide +kernel
      have hl : raw16847step1Labels = labelEmbedding6 ∘ raw16847step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16847step1 raw16847step1Labels raw16847step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5399 node5399Labels := by rfl

def raw16848 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16848 raw16848Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw16848 raw16848Labels = mixedMoment B raw16848step0 raw16848step0Labels := by
      have ha : raw16848step0 = (fun i j => raw16848 (permutation675 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16848step0 raw16848; decide +kernel
      have hl : raw16848step0Labels = raw16848Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16848 raw16848Labels permutation675 permutation2
    _ = mixedMoment B node5402 node5402Labels := by rfl

def raw16849 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16849step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16849step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16849step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16849 raw16849Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw16849 raw16849Labels = mixedMoment B raw16849step0 raw16849step0Labels := by
      have ha : raw16849step0 = (fun i j => raw16849 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16849step0 raw16849; decide +kernel
      have hl : raw16849step0Labels = raw16849Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16849 raw16849Labels permutation165 permutation4
    mixedMoment B raw16849step0 raw16849step0Labels = mixedMoment B raw16849step1 raw16849step1Labels := by
      have ha : raw16849step1 = -raw16849step0 := by apply Matrix.ext; change ∀ i j, raw16849step1 i j = -(raw16849step0 i j); unfold raw16849step1 raw16849step0; decide +kernel
      have hl : raw16849step1Labels = raw16849step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16849step1 raw16849step1Labels = mixedMoment B raw16849step2 raw16849step2Labels := by
      have ha : raw16849step2 = raw16849step1 := by apply Matrix.ext; unfold raw16849step2 raw16849step1; decide +kernel
      have hl : raw16849step1Labels = labelEmbedding7 ∘ raw16849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16849step1 raw16849step1Labels raw16849step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw16850 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16850step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16850step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16850step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16850step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16850 raw16850Labels = mixedMoment B node5183 node5183Labels := by
  calc
    mixedMoment B raw16850 raw16850Labels = mixedMoment B raw16850step0 raw16850step0Labels := by
      have ha : raw16850step0 = (fun i j => raw16850 (permutation281 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16850step0 raw16850; decide +kernel
      have hl : raw16850step0Labels = raw16850Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16850 raw16850Labels permutation281 permutation5
    mixedMoment B raw16850step0 raw16850step0Labels = mixedMoment B raw16850step1 raw16850step1Labels := by
      have ha : raw16850step1 = -raw16850step0 := by apply Matrix.ext; change ∀ i j, raw16850step1 i j = -(raw16850step0 i j); unfold raw16850step1 raw16850step0; decide +kernel
      have hl : raw16850step1Labels = raw16850step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16850step1 raw16850step1Labels = mixedMoment B raw16850step2 raw16850step2Labels := by
      have ha : raw16850step2 = raw16850step1 := by apply Matrix.ext; unfold raw16850step2 raw16850step1; decide +kernel
      have hl : raw16850step1Labels = labelEmbedding8 ∘ raw16850step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16850step1 raw16850step1Labels raw16850step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5183 node5183Labels := by rfl

def raw16851 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16851step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16851step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16851 raw16851Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw16851 raw16851Labels = mixedMoment B raw16851step0 raw16851step0Labels := by
      have hz : ∀ j, raw16851 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16851step0 = (fun i j => raw16851 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16851step0 raw16851; decide +kernel
      have hl : raw16851step0Labels = raw16851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16851 raw16851Labels permutation346 hz
    mixedMoment B raw16851step0 raw16851step0Labels = mixedMoment B raw16851step1 raw16851step1Labels := by
      have ha : raw16851step1 = (fun i j => raw16851step0 (permutation102 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16851step1 raw16851step0; decide +kernel
      have hl : raw16851step1Labels = raw16851step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16851step0 raw16851step0Labels permutation102 permutation5
    mixedMoment B raw16851step1 raw16851step1Labels = mixedMoment B raw16851step2 raw16851step2Labels := by
      have ha : raw16851step2 = raw16851step1 := by apply Matrix.ext; unfold raw16851step2 raw16851step1; decide +kernel
      have hl : raw16851step1Labels = labelEmbedding8 ∘ raw16851step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16851step1 raw16851step1Labels raw16851step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw16852 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16852step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16852step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16852step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16852 raw16852Labels = mixedMoment B node5399 node5399Labels := by
  calc
    mixedMoment B raw16852 raw16852Labels = mixedMoment B raw16852step0 raw16852step0Labels := by
      have ha : raw16852step0 = (fun i j => raw16852 (permutation469 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16852step0 raw16852; decide +kernel
      have hl : raw16852step0Labels = raw16852Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16852 raw16852Labels permutation469 permutation3
    mixedMoment B raw16852step0 raw16852step0Labels = mixedMoment B raw16852step1 raw16852step1Labels := by
      have ha : raw16852step1 = -raw16852step0 := by apply Matrix.ext; change ∀ i j, raw16852step1 i j = -(raw16852step0 i j); unfold raw16852step1 raw16852step0; decide +kernel
      have hl : raw16852step1Labels = raw16852step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16852step1 raw16852step1Labels = mixedMoment B raw16852step2 raw16852step2Labels := by
      have ha : raw16852step2 = raw16852step1 := by apply Matrix.ext; unfold raw16852step2 raw16852step1; decide +kernel
      have hl : raw16852step1Labels = labelEmbedding6 ∘ raw16852step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16852step1 raw16852step1Labels raw16852step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5399 node5399Labels := by rfl

def raw16853 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16853 raw16853Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw16853 raw16853Labels = mixedMoment B raw16853step0 raw16853step0Labels := by
      have ha : raw16853step0 = (fun i j => raw16853 (permutation673 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16853step0 raw16853; decide +kernel
      have hl : raw16853step0Labels = raw16853Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16853 raw16853Labels permutation673 permutation2
    _ = mixedMoment B node5402 node5402Labels := by rfl

def raw16854 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16854step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16854step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16854step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16854step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16854 raw16854Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw16854 raw16854Labels = mixedMoment B raw16854step0 raw16854step0Labels := by
      have ha : raw16854step0 = (fun i j => raw16854 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16854step0 raw16854; decide +kernel
      have hl : raw16854step0Labels = raw16854Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16854 raw16854Labels permutation152 permutation4
    mixedMoment B raw16854step0 raw16854step0Labels = mixedMoment B raw16854step1 raw16854step1Labels := by
      have ha : raw16854step1 = -raw16854step0 := by apply Matrix.ext; change ∀ i j, raw16854step1 i j = -(raw16854step0 i j); unfold raw16854step1 raw16854step0; decide +kernel
      have hl : raw16854step1Labels = raw16854step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16854step1 raw16854step1Labels = mixedMoment B raw16854step2 raw16854step2Labels := by
      have ha : raw16854step2 = raw16854step1 := by apply Matrix.ext; unfold raw16854step2 raw16854step1; decide +kernel
      have hl : raw16854step1Labels = labelEmbedding7 ∘ raw16854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16854step1 raw16854step1Labels raw16854step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw16855 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16855step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16855step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16855step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16855 raw16855Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw16855 raw16855Labels = mixedMoment B raw16855step0 raw16855step0Labels := by
      have ha : raw16855step0 = (fun i j => raw16855 (permutation287 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16855step0 raw16855; decide +kernel
      have hl : raw16855step0Labels = raw16855Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16855 raw16855Labels permutation287 permutation5
    mixedMoment B raw16855step0 raw16855step0Labels = mixedMoment B raw16855step1 raw16855step1Labels := by
      have ha : raw16855step1 = -raw16855step0 := by apply Matrix.ext; change ∀ i j, raw16855step1 i j = -(raw16855step0 i j); unfold raw16855step1 raw16855step0; decide +kernel
      have hl : raw16855step1Labels = raw16855step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16855step1 raw16855step1Labels = mixedMoment B raw16855step2 raw16855step2Labels := by
      have ha : raw16855step2 = raw16855step1 := by apply Matrix.ext; unfold raw16855step2 raw16855step1; decide +kernel
      have hl : raw16855step1Labels = labelEmbedding8 ∘ raw16855step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16855step1 raw16855step1Labels raw16855step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw16856 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16856step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16856 raw16856Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw16856 raw16856Labels = mixedMoment B raw16856step0 raw16856step0Labels := by
      have hz : ∀ j, raw16856 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16856step0 = (fun i j => raw16856 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16856step0 raw16856; decide +kernel
      have hl : raw16856step0Labels = raw16856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16856 raw16856Labels permutation346 hz
    mixedMoment B raw16856step0 raw16856step0Labels = mixedMoment B raw16856step1 raw16856step1Labels := by
      have ha : raw16856step1 = (fun i j => raw16856step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16856step1 raw16856step0; decide +kernel
      have hl : raw16856step1Labels = raw16856step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16856step0 raw16856step0Labels permutation32 permutation6
    mixedMoment B raw16856step1 raw16856step1Labels = mixedMoment B raw16856step2 raw16856step2Labels := by
      have ha : raw16856step2 = raw16856step1 := by apply Matrix.ext; unfold raw16856step2 raw16856step1; decide +kernel
      have hl : raw16856step1Labels = labelEmbedding9 ∘ raw16856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16856step1 raw16856step1Labels raw16856step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw16857 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16857step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16857 raw16857Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw16857 raw16857Labels = mixedMoment B raw16857step0 raw16857step0Labels := by
      have hz : ∀ j, raw16857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16857step0 = (fun i j => raw16857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16857step0 raw16857; decide +kernel
      have hl : raw16857step0Labels = raw16857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16857 raw16857Labels permutation434 hz
    mixedMoment B raw16857step0 raw16857step0Labels = mixedMoment B raw16857step1 raw16857step1Labels := by
      have ha : raw16857step1 = (fun i j => raw16857step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16857step1 raw16857step0; decide +kernel
      have hl : raw16857step1Labels = raw16857step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16857step0 raw16857step0Labels permutation32 permutation6
    mixedMoment B raw16857step1 raw16857step1Labels = mixedMoment B raw16857step2 raw16857step2Labels := by
      have ha : raw16857step2 = raw16857step1 := by apply Matrix.ext; unfold raw16857step2 raw16857step1; decide +kernel
      have hl : raw16857step1Labels = labelEmbedding9 ∘ raw16857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16857step1 raw16857step1Labels raw16857step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw16858 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16858step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16858step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16858step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16858 raw16858Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw16858 raw16858Labels = mixedMoment B raw16858step0 raw16858step0Labels := by
      have ha : raw16858step0 = (fun i j => raw16858 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16858step0 raw16858; decide +kernel
      have hl : raw16858step0Labels = raw16858Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16858 raw16858Labels permutation682 permutation7
    mixedMoment B raw16858step0 raw16858step0Labels = mixedMoment B raw16858step1 raw16858step1Labels := by
      have ha : raw16858step1 = -raw16858step0 := by apply Matrix.ext; change ∀ i j, raw16858step1 i j = -(raw16858step0 i j); unfold raw16858step1 raw16858step0; decide +kernel
      have hl : raw16858step1Labels = raw16858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16858step1 raw16858step1Labels = mixedMoment B raw16858step2 raw16858step2Labels := by
      have ha : raw16858step2 = raw16858step1 := by apply Matrix.ext; unfold raw16858step2 raw16858step1; decide +kernel
      have hl : raw16858step1Labels = labelEmbedding10 ∘ raw16858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16858step1 raw16858step1Labels raw16858step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw16859 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw16859step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16859step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16859step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw16859step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16859 raw16859Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw16859 raw16859Labels = mixedMoment B raw16859step0 raw16859step0Labels := by
      have ha : raw16859step0 = (fun i j => raw16859 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16859step0 raw16859; decide +kernel
      have hl : raw16859step0Labels = raw16859Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16859 raw16859Labels permutation164 permutation4
    mixedMoment B raw16859step0 raw16859step0Labels = mixedMoment B raw16859step1 raw16859step1Labels := by
      have ha : raw16859step1 = -raw16859step0 := by apply Matrix.ext; change ∀ i j, raw16859step1 i j = -(raw16859step0 i j); unfold raw16859step1 raw16859step0; decide +kernel
      have hl : raw16859step1Labels = raw16859step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16859step1 raw16859step1Labels = mixedMoment B raw16859step2 raw16859step2Labels := by
      have ha : raw16859step2 = raw16859step1 := by apply Matrix.ext; unfold raw16859step2 raw16859step1; decide +kernel
      have hl : raw16859step1Labels = labelEmbedding7 ∘ raw16859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16859step1 raw16859step1Labels raw16859step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw16860 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16860step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16860step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16860step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16860step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16860 raw16860Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw16860 raw16860Labels = mixedMoment B raw16860step0 raw16860step0Labels := by
      have ha : raw16860step0 = (fun i j => raw16860 (permutation277 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16860step0 raw16860; decide +kernel
      have hl : raw16860step0Labels = raw16860Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16860 raw16860Labels permutation277 permutation5
    mixedMoment B raw16860step0 raw16860step0Labels = mixedMoment B raw16860step1 raw16860step1Labels := by
      have ha : raw16860step1 = -raw16860step0 := by apply Matrix.ext; change ∀ i j, raw16860step1 i j = -(raw16860step0 i j); unfold raw16860step1 raw16860step0; decide +kernel
      have hl : raw16860step1Labels = raw16860step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16860step1 raw16860step1Labels = mixedMoment B raw16860step2 raw16860step2Labels := by
      have ha : raw16860step2 = raw16860step1 := by apply Matrix.ext; unfold raw16860step2 raw16860step1; decide +kernel
      have hl : raw16860step1Labels = labelEmbedding8 ∘ raw16860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16860step1 raw16860step1Labels raw16860step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw16861 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16861step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16861 raw16861Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw16861 raw16861Labels = mixedMoment B raw16861step0 raw16861step0Labels := by
      have hz : ∀ j, raw16861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16861step0 = (fun i j => raw16861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16861step0 raw16861; decide +kernel
      have hl : raw16861step0Labels = raw16861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16861 raw16861Labels permutation346 hz
    mixedMoment B raw16861step0 raw16861step0Labels = mixedMoment B raw16861step1 raw16861step1Labels := by
      have ha : raw16861step1 = (fun i j => raw16861step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16861step1 raw16861step0; decide +kernel
      have hl : raw16861step1Labels = raw16861step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16861step0 raw16861step0Labels permutation144 permutation4
    mixedMoment B raw16861step1 raw16861step1Labels = mixedMoment B raw16861step2 raw16861step2Labels := by
      have ha : raw16861step2 = raw16861step1 := by apply Matrix.ext; unfold raw16861step2 raw16861step1; decide +kernel
      have hl : raw16861step1Labels = labelEmbedding7 ∘ raw16861step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16861step1 raw16861step1Labels raw16861step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw16862 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16862step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16862 raw16862Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw16862 raw16862Labels = mixedMoment B raw16862step0 raw16862step0Labels := by
      have hz : ∀ j, raw16862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16862step0 = (fun i j => raw16862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16862step0 raw16862; decide +kernel
      have hl : raw16862step0Labels = raw16862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16862 raw16862Labels permutation434 hz
    mixedMoment B raw16862step0 raw16862step0Labels = mixedMoment B raw16862step1 raw16862step1Labels := by
      have ha : raw16862step1 = (fun i j => raw16862step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16862step1 raw16862step0; decide +kernel
      have hl : raw16862step1Labels = raw16862step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16862step0 raw16862step0Labels permutation144 permutation4
    mixedMoment B raw16862step1 raw16862step1Labels = mixedMoment B raw16862step2 raw16862step2Labels := by
      have ha : raw16862step2 = raw16862step1 := by apply Matrix.ext; unfold raw16862step2 raw16862step1; decide +kernel
      have hl : raw16862step1Labels = labelEmbedding7 ∘ raw16862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16862step1 raw16862step1Labels raw16862step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw16863 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16863step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16863 raw16863Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw16863 raw16863Labels = mixedMoment B raw16863step0 raw16863step0Labels := by
      have ha : raw16863step0 = (fun i j => raw16863 (permutation639 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16863step0 raw16863; decide +kernel
      have hl : raw16863step0Labels = raw16863Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16863 raw16863Labels permutation639 permutation4
    mixedMoment B raw16863step0 raw16863step0Labels = mixedMoment B raw16863step1 raw16863step1Labels := by
      have ha : raw16863step1 = raw16863step0 := by apply Matrix.ext; unfold raw16863step1 raw16863step0; decide +kernel
      have hl : raw16863step0Labels = labelEmbedding7 ∘ raw16863step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16863step0 raw16863step0Labels raw16863step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw16864 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16864 raw16864Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw16864 raw16864Labels = mixedMoment B raw16864step0 raw16864step0Labels := by
      have ha : raw16864step0 = (fun i j => raw16864 (permutation332 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16864step0 raw16864; decide +kernel
      have hl : raw16864step0Labels = raw16864Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16864 raw16864Labels permutation332 permutation3
    _ = mixedMoment B node3505 node3505Labels := by rfl

def raw16865 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16865step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16865 raw16865Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw16865 raw16865Labels = mixedMoment B raw16865step0 raw16865step0Labels := by
      have hz : ∀ j, raw16865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16865step0 = (fun i j => raw16865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16865step0 raw16865; decide +kernel
      have hl : raw16865step0Labels = raw16865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16865 raw16865Labels permutation346 hz
    mixedMoment B raw16865step0 raw16865step0Labels = mixedMoment B raw16865step1 raw16865step1Labels := by
      have ha : raw16865step1 = (fun i j => raw16865step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16865step1 raw16865step0; decide +kernel
      have hl : raw16865step1Labels = raw16865step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16865step0 raw16865step0Labels permutation151 permutation6
    mixedMoment B raw16865step1 raw16865step1Labels = mixedMoment B raw16865step2 raw16865step2Labels := by
      have ha : raw16865step2 = -raw16865step1 := by apply Matrix.ext; change ∀ i j, raw16865step2 i j = -(raw16865step1 i j); unfold raw16865step2 raw16865step1; decide +kernel
      have hl : raw16865step2Labels = raw16865step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw16866 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16866 raw16866Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw16866 raw16866Labels = mixedMoment B raw16866step0 raw16866step0Labels := by
      have hz : ∀ j, raw16866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16866step0 = (fun i j => raw16866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16866step0 raw16866; decide +kernel
      have hl : raw16866step0Labels = raw16866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16866 raw16866Labels permutation434 hz
    mixedMoment B raw16866step0 raw16866step0Labels = mixedMoment B raw16866step1 raw16866step1Labels := by
      have ha : raw16866step1 = (fun i j => raw16866step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16866step1 raw16866step0; decide +kernel
      have hl : raw16866step1Labels = raw16866step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16866step0 raw16866step0Labels permutation151 permutation6
    mixedMoment B raw16866step1 raw16866step1Labels = mixedMoment B raw16866step2 raw16866step2Labels := by
      have ha : raw16866step2 = -raw16866step1 := by apply Matrix.ext; change ∀ i j, raw16866step2 i j = -(raw16866step1 i j); unfold raw16866step2 raw16866step1; decide +kernel
      have hl : raw16866step2Labels = raw16866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw16867 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16867 raw16867Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw16867 raw16867Labels = mixedMoment B raw16867step0 raw16867step0Labels := by
      have ha : raw16867step0 = (fun i j => raw16867 (permutation540 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16867step0 raw16867; decide +kernel
      have hl : raw16867step0Labels = raw16867Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16867 raw16867Labels permutation540 permutation3
    _ = mixedMoment B node3949 node3949Labels := by rfl

def raw16868 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16868 raw16868Labels = mixedMoment B node4023 node4023Labels := by
  calc
    mixedMoment B raw16868 raw16868Labels = mixedMoment B raw16868step0 raw16868step0Labels := by
      have ha : raw16868step0 = (fun i j => raw16868 (permutation620 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16868step0 raw16868; decide +kernel
      have hl : raw16868step0Labels = raw16868Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16868 raw16868Labels permutation620 permutation3
    _ = mixedMoment B node4023 node4023Labels := by rfl

def raw16869 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16869 raw16869Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw16869 raw16869Labels = mixedMoment B raw16869step0 raw16869step0Labels := by
      have hz : ∀ j, raw16869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16869step0 = (fun i j => raw16869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16869step0 raw16869; decide +kernel
      have hl : raw16869step0Labels = raw16869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16869 raw16869Labels permutation346 hz
    mixedMoment B raw16869step0 raw16869step0Labels = mixedMoment B raw16869step1 raw16869step1Labels := by
      have ha : raw16869step1 = (fun i j => raw16869step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16869step1 raw16869step0; decide +kernel
      have hl : raw16869step1Labels = raw16869step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16869step0 raw16869step0Labels permutation32 permutation6
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw16870 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16870step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16870 raw16870Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw16870 raw16870Labels = mixedMoment B raw16870step0 raw16870step0Labels := by
      have hz : ∀ j, raw16870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16870step0 = (fun i j => raw16870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16870step0 raw16870; decide +kernel
      have hl : raw16870step0Labels = raw16870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16870 raw16870Labels permutation434 hz
    mixedMoment B raw16870step0 raw16870step0Labels = mixedMoment B raw16870step1 raw16870step1Labels := by
      have ha : raw16870step1 = (fun i j => raw16870step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16870step1 raw16870step0; decide +kernel
      have hl : raw16870step1Labels = raw16870step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16870step0 raw16870step0Labels permutation32 permutation6
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw16871 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16871 raw16871Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw16871 raw16871Labels = mixedMoment B raw16871step0 raw16871step0Labels := by
      have ha : raw16871step0 = (fun i j => raw16871 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16871step0 raw16871; decide +kernel
      have hl : raw16871step0Labels = raw16871Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16871 raw16871Labels permutation158 permutation6
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw16872 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16872 raw16872Labels = mixedMoment B node3501 node3501Labels := by
  calc
    mixedMoment B raw16872 raw16872Labels = mixedMoment B raw16872step0 raw16872step0Labels := by
      have ha : raw16872step0 = (fun i j => raw16872 (permutation330 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16872step0 raw16872; decide +kernel
      have hl : raw16872step0Labels = raw16872Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16872 raw16872Labels permutation330 permutation3
    _ = mixedMoment B node3501 node3501Labels := by rfl

def raw16873 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16873 raw16873Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw16873 raw16873Labels = mixedMoment B raw16873step0 raw16873step0Labels := by
      have hz : ∀ j, raw16873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16873step0 = (fun i j => raw16873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16873step0 raw16873; decide +kernel
      have hl : raw16873step0Labels = raw16873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16873 raw16873Labels permutation434 hz
    mixedMoment B raw16873step0 raw16873step0Labels = mixedMoment B raw16873step1 raw16873step1Labels := by
      have ha : raw16873step1 = (fun i j => raw16873step0 (permutation85 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16873step1 raw16873step0; decide +kernel
      have hl : raw16873step1Labels = raw16873step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16873step0 raw16873step0Labels permutation85 permutation3
    mixedMoment B raw16873step1 raw16873step1Labels = mixedMoment B raw16873step2 raw16873step2Labels := by
      have ha : raw16873step2 = -raw16873step1 := by apply Matrix.ext; change ∀ i j, raw16873step2 i j = -(raw16873step1 i j); unfold raw16873step2 raw16873step1; decide +kernel
      have hl : raw16873step2Labels = raw16873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw16874 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16874 raw16874Labels = mixedMoment B node3785 node3785Labels := by
  calc
    mixedMoment B raw16874 raw16874Labels = mixedMoment B raw16874step0 raw16874step0Labels := by
      have ha : raw16874step0 = (fun i j => raw16874 (permutation384 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16874step0 raw16874; decide +kernel
      have hl : raw16874step0Labels = raw16874Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16874 raw16874Labels permutation384 permutation3
    mixedMoment B raw16874step0 raw16874step0Labels = mixedMoment B raw16874step1 raw16874step1Labels := by
      have ha : raw16874step1 = -raw16874step0 := by apply Matrix.ext; change ∀ i j, raw16874step1 i j = -(raw16874step0 i j); unfold raw16874step1 raw16874step0; decide +kernel
      have hl : raw16874step1Labels = raw16874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3785 node3785Labels := by rfl

def raw16875 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16875 raw16875Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw16875 raw16875Labels = mixedMoment B raw16875step0 raw16875step0Labels := by
      have ha : raw16875step0 = (fun i j => raw16875 (permutation382 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16875step0 raw16875; decide +kernel
      have hl : raw16875step0Labels = raw16875Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16875 raw16875Labels permutation382 permutation3
    mixedMoment B raw16875step0 raw16875step0Labels = mixedMoment B raw16875step1 raw16875step1Labels := by
      have ha : raw16875step1 = -raw16875step0 := by apply Matrix.ext; change ∀ i j, raw16875step1 i j = -(raw16875step0 i j); unfold raw16875step1 raw16875step0; decide +kernel
      have hl : raw16875step1Labels = raw16875step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3788 node3788Labels := by rfl

def raw16876 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16876 raw16876Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw16876 raw16876Labels = mixedMoment B raw16876step0 raw16876step0Labels := by
      have ha : raw16876step0 = (fun i j => raw16876 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16876step0 raw16876; decide +kernel
      have hl : raw16876step0Labels = raw16876Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16876 raw16876Labels permutation152 permutation6
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw16877 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16877 raw16877Labels = mixedMoment B node3501 node3501Labels := by
  calc
    mixedMoment B raw16877 raw16877Labels = mixedMoment B raw16877step0 raw16877step0Labels := by
      have ha : raw16877step0 = (fun i j => raw16877 (permutation329 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16877step0 raw16877; decide +kernel
      have hl : raw16877step0Labels = raw16877Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16877 raw16877Labels permutation329 permutation3
    _ = mixedMoment B node3501 node3501Labels := by rfl

def raw16878 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16878step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16878 raw16878Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw16878 raw16878Labels = mixedMoment B raw16878step0 raw16878step0Labels := by
      have hz : ∀ j, raw16878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16878step0 = (fun i j => raw16878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16878step0 raw16878; decide +kernel
      have hl : raw16878step0Labels = raw16878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16878 raw16878Labels permutation346 hz
    mixedMoment B raw16878step0 raw16878step0Labels = mixedMoment B raw16878step1 raw16878step1Labels := by
      have ha : raw16878step1 = (fun i j => raw16878step0 (permutation85 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16878step1 raw16878step0; decide +kernel
      have hl : raw16878step1Labels = raw16878step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16878step0 raw16878step0Labels permutation85 permutation3
    mixedMoment B raw16878step1 raw16878step1Labels = mixedMoment B raw16878step2 raw16878step2Labels := by
      have ha : raw16878step2 = -raw16878step1 := by apply Matrix.ext; change ∀ i j, raw16878step2 i j = -(raw16878step1 i j); unfold raw16878step2 raw16878step1; decide +kernel
      have hl : raw16878step2Labels = raw16878step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw16879 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16879 raw16879Labels = mixedMoment B node3785 node3785Labels := by
  calc
    mixedMoment B raw16879 raw16879Labels = mixedMoment B raw16879step0 raw16879step0Labels := by
      have ha : raw16879step0 = (fun i j => raw16879 (permutation469 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16879step0 raw16879; decide +kernel
      have hl : raw16879step0Labels = raw16879Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16879 raw16879Labels permutation469 permutation3
    mixedMoment B raw16879step0 raw16879step0Labels = mixedMoment B raw16879step1 raw16879step1Labels := by
      have ha : raw16879step1 = -raw16879step0 := by apply Matrix.ext; change ∀ i j, raw16879step1 i j = -(raw16879step0 i j); unfold raw16879step1 raw16879step0; decide +kernel
      have hl : raw16879step1Labels = raw16879step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3785 node3785Labels := by rfl

def raw16880 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16880step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16880 raw16880Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw16880 raw16880Labels = mixedMoment B raw16880step0 raw16880step0Labels := by
      have ha : raw16880step0 = (fun i j => raw16880 (permutation467 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16880step0 raw16880; decide +kernel
      have hl : raw16880step0Labels = raw16880Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16880 raw16880Labels permutation467 permutation3
    mixedMoment B raw16880step0 raw16880step0Labels = mixedMoment B raw16880step1 raw16880step1Labels := by
      have ha : raw16880step1 = -raw16880step0 := by apply Matrix.ext; change ∀ i j, raw16880step1 i j = -(raw16880step0 i j); unfold raw16880step1 raw16880step0; decide +kernel
      have hl : raw16880step1Labels = raw16880step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3788 node3788Labels := by rfl

def raw16881 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16881 raw16881Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw16881 raw16881Labels = mixedMoment B raw16881step0 raw16881step0Labels := by
      have ha : raw16881step0 = (fun i j => raw16881 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16881step0 raw16881; decide +kernel
      have hl : raw16881step0Labels = raw16881Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16881 raw16881Labels permutation152 permutation6
    _ = mixedMoment B node3758 node3758Labels := by rfl

def raw16882 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16882 raw16882Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw16882 raw16882Labels = mixedMoment B raw16882step0 raw16882step0Labels := by
      have ha : raw16882step0 = (fun i j => raw16882 (permutation344 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16882step0 raw16882; decide +kernel
      have hl : raw16882step0Labels = raw16882Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16882 raw16882Labels permutation344 permutation3
    _ = mixedMoment B node3569 node3569Labels := by rfl

def raw16883 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16883 raw16883Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw16883 raw16883Labels = mixedMoment B raw16883step0 raw16883step0Labels := by
      have hz : ∀ j, raw16883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16883step0 = (fun i j => raw16883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16883step0 raw16883; decide +kernel
      have hl : raw16883step0Labels = raw16883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16883 raw16883Labels permutation346 hz
    mixedMoment B raw16883step0 raw16883step0Labels = mixedMoment B raw16883step1 raw16883step1Labels := by
      have ha : raw16883step1 = (fun i j => raw16883step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16883step1 raw16883step0; decide +kernel
      have hl : raw16883step1Labels = raw16883step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16883step0 raw16883step0Labels permutation32 permutation6
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw16884 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16884 raw16884Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw16884 raw16884Labels = mixedMoment B raw16884step0 raw16884step0Labels := by
      have hz : ∀ j, raw16884 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16884step0 = (fun i j => raw16884 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16884step0 raw16884; decide +kernel
      have hl : raw16884step0Labels = raw16884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16884 raw16884Labels permutation434 hz
    mixedMoment B raw16884step0 raw16884step0Labels = mixedMoment B raw16884step1 raw16884step1Labels := by
      have ha : raw16884step1 = (fun i j => raw16884step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16884step1 raw16884step0; decide +kernel
      have hl : raw16884step1Labels = raw16884step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16884step0 raw16884step0Labels permutation32 permutation6
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw16885 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16885 raw16885Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw16885 raw16885Labels = mixedMoment B raw16885step0 raw16885step0Labels := by
      have ha : raw16885step0 = (fun i j => raw16885 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16885step0 raw16885; decide +kernel
      have hl : raw16885step0Labels = raw16885Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16885 raw16885Labels permutation152 permutation6
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw16886 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16886 raw16886Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw16886 raw16886Labels = mixedMoment B raw16886step0 raw16886step0Labels := by
      have ha : raw16886step0 = (fun i j => raw16886 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16886step0 raw16886; decide +kernel
      have hl : raw16886step0Labels = raw16886Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16886 raw16886Labels permutation152 permutation6
    _ = mixedMoment B node3757 node3757Labels := by rfl

def raw16887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16887 raw16887Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw16887 raw16887Labels = mixedMoment B raw16887step0 raw16887step0Labels := by
      have ha : raw16887step0 = (fun i j => raw16887 (permutation329 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16887step0 raw16887; decide +kernel
      have hl : raw16887step0Labels = raw16887Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16887 raw16887Labels permutation329 permutation3
    _ = mixedMoment B node3537 node3537Labels := by rfl

def raw16888 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16888step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16888step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16888 raw16888Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw16888 raw16888Labels = mixedMoment B raw16888step0 raw16888step0Labels := by
      have hz : ∀ j, raw16888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16888step0 = (fun i j => raw16888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16888step0 raw16888; decide +kernel
      have hl : raw16888step0Labels = raw16888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16888 raw16888Labels permutation346 hz
    mixedMoment B raw16888step0 raw16888step0Labels = mixedMoment B raw16888step1 raw16888step1Labels := by
      have ha : raw16888step1 = (fun i j => raw16888step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16888step1 raw16888step0; decide +kernel
      have hl : raw16888step1Labels = raw16888step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16888step0 raw16888step0Labels permutation151 permutation6
    mixedMoment B raw16888step1 raw16888step1Labels = mixedMoment B raw16888step2 raw16888step2Labels := by
      have ha : raw16888step2 = -raw16888step1 := by apply Matrix.ext; change ∀ i j, raw16888step2 i j = -(raw16888step1 i j); unfold raw16888step2 raw16888step1; decide +kernel
      have hl : raw16888step2Labels = raw16888step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw16889 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16889 raw16889Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw16889 raw16889Labels = mixedMoment B raw16889step0 raw16889step0Labels := by
      have hz : ∀ j, raw16889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16889step0 = (fun i j => raw16889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16889step0 raw16889; decide +kernel
      have hl : raw16889step0Labels = raw16889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16889 raw16889Labels permutation434 hz
    mixedMoment B raw16889step0 raw16889step0Labels = mixedMoment B raw16889step1 raw16889step1Labels := by
      have ha : raw16889step1 = (fun i j => raw16889step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16889step1 raw16889step0; decide +kernel
      have hl : raw16889step1Labels = raw16889step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16889step0 raw16889step0Labels permutation151 permutation6
    mixedMoment B raw16889step1 raw16889step1Labels = mixedMoment B raw16889step2 raw16889step2Labels := by
      have ha : raw16889step2 = -raw16889step1 := by apply Matrix.ext; change ∀ i j, raw16889step2 i j = -(raw16889step1 i j); unfold raw16889step2 raw16889step1; decide +kernel
      have hl : raw16889step2Labels = raw16889step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw16890 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16890 raw16890Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw16890 raw16890Labels = mixedMoment B raw16890step0 raw16890step0Labels := by
      have ha : raw16890step0 = (fun i j => raw16890 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16890step0 raw16890; decide +kernel
      have hl : raw16890step0Labels = raw16890Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16890 raw16890Labels permutation682 permutation6
    mixedMoment B raw16890step0 raw16890step0Labels = mixedMoment B raw16890step1 raw16890step1Labels := by
      have ha : raw16890step1 = -raw16890step0 := by apply Matrix.ext; change ∀ i j, raw16890step1 i j = -(raw16890step0 i j); unfold raw16890step1 raw16890step0; decide +kernel
      have hl : raw16890step1Labels = raw16890step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3869 node3869Labels := by rfl

def raw16891 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16891step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16891step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16891step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16891step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16891 raw16891Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw16891 raw16891Labels = mixedMoment B raw16891step0 raw16891step0Labels := by
      have ha : raw16891step0 = (fun i j => raw16891 (permutation324 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16891step0 raw16891; decide +kernel
      have hl : raw16891step0Labels = raw16891Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16891 raw16891Labels permutation324 permutation5
    mixedMoment B raw16891step0 raw16891step0Labels = mixedMoment B raw16891step1 raw16891step1Labels := by
      have ha : raw16891step1 = -raw16891step0 := by apply Matrix.ext; change ∀ i j, raw16891step1 i j = -(raw16891step0 i j); unfold raw16891step1 raw16891step0; decide +kernel
      have hl : raw16891step1Labels = raw16891step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16891step1 raw16891step1Labels = mixedMoment B raw16891step2 raw16891step2Labels := by
      have ha : raw16891step2 = raw16891step1 := by apply Matrix.ext; unfold raw16891step2 raw16891step1; decide +kernel
      have hl : raw16891step1Labels = labelEmbedding1 ∘ raw16891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16891step1 raw16891step1Labels raw16891step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2728 node2728Labels := by rfl

def raw16892 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16892step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16892 raw16892Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw16892 raw16892Labels = mixedMoment B raw16892step0 raw16892step0Labels := by
      have hz : ∀ j, raw16892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16892step0 = (fun i j => raw16892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16892step0 raw16892; decide +kernel
      have hl : raw16892step0Labels = raw16892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16892 raw16892Labels permutation346 hz
    mixedMoment B raw16892step0 raw16892step0Labels = mixedMoment B raw16892step1 raw16892step1Labels := by
      have ha : raw16892step1 = (fun i j => raw16892step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16892step1 raw16892step0; decide +kernel
      have hl : raw16892step1Labels = raw16892step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16892step0 raw16892step0Labels permutation32 permutation7
    mixedMoment B raw16892step1 raw16892step1Labels = mixedMoment B raw16892step2 raw16892step2Labels := by
      have ha : raw16892step2 = raw16892step1 := by apply Matrix.ext; unfold raw16892step2 raw16892step1; decide +kernel
      have hl : raw16892step1Labels = labelEmbedding1 ∘ raw16892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16892step1 raw16892step1Labels raw16892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw16893 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16893step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16893step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16893 raw16893Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw16893 raw16893Labels = mixedMoment B raw16893step0 raw16893step0Labels := by
      have hz : ∀ j, raw16893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16893step0 = (fun i j => raw16893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16893step0 raw16893; decide +kernel
      have hl : raw16893step0Labels = raw16893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16893 raw16893Labels permutation434 hz
    mixedMoment B raw16893step0 raw16893step0Labels = mixedMoment B raw16893step1 raw16893step1Labels := by
      have ha : raw16893step1 = (fun i j => raw16893step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16893step1 raw16893step0; decide +kernel
      have hl : raw16893step1Labels = raw16893step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16893step0 raw16893step0Labels permutation32 permutation7
    mixedMoment B raw16893step1 raw16893step1Labels = mixedMoment B raw16893step2 raw16893step2Labels := by
      have ha : raw16893step2 = raw16893step1 := by apply Matrix.ext; unfold raw16893step2 raw16893step1; decide +kernel
      have hl : raw16893step1Labels = labelEmbedding1 ∘ raw16893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16893step1 raw16893step1Labels raw16893step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw16894 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16894 raw16894Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw16894 raw16894Labels = mixedMoment B raw16894step0 raw16894step0Labels := by
      have ha : raw16894step0 = (fun i j => raw16894 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16894step0 raw16894; decide +kernel
      have hl : raw16894step0Labels = raw16894Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16894 raw16894Labels permutation152 permutation7
    mixedMoment B raw16894step0 raw16894step0Labels = mixedMoment B raw16894step1 raw16894step1Labels := by
      have ha : raw16894step1 = raw16894step0 := by apply Matrix.ext; unfold raw16894step1 raw16894step0; decide +kernel
      have hl : raw16894step0Labels = labelEmbedding1 ∘ raw16894step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16894step0 raw16894step0Labels raw16894step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

def raw16895 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16895step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16895step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16895step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16895 raw16895Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw16895 raw16895Labels = mixedMoment B raw16895step0 raw16895step0Labels := by
      have ha : raw16895step0 = (fun i j => raw16895 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16895step0 raw16895; decide +kernel
      have hl : raw16895step0Labels = raw16895Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16895 raw16895Labels permutation682 permutation7
    mixedMoment B raw16895step0 raw16895step0Labels = mixedMoment B raw16895step1 raw16895step1Labels := by
      have ha : raw16895step1 = -raw16895step0 := by apply Matrix.ext; change ∀ i j, raw16895step1 i j = -(raw16895step0 i j); unfold raw16895step1 raw16895step0; decide +kernel
      have hl : raw16895step1Labels = raw16895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16895step1 raw16895step1Labels = mixedMoment B raw16895step2 raw16895step2Labels := by
      have ha : raw16895step2 = raw16895step1 := by apply Matrix.ext; unfold raw16895step2 raw16895step1; decide +kernel
      have hl : raw16895step1Labels = labelEmbedding1 ∘ raw16895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16895step1 raw16895step1Labels raw16895step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
