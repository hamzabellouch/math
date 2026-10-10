import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw15232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw15232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15232step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15232step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15232step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15232step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15232 raw15232Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw15232 raw15232Labels = mixedMoment B raw15232step0 raw15232step0Labels := by
      have hz : ∀ j, raw15232 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15232step0 = (fun i j => raw15232 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15232step0 raw15232; decide +kernel
      have hl : raw15232step0Labels = raw15232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15232 raw15232Labels permutation346 hz
    mixedMoment B raw15232step0 raw15232step0Labels = mixedMoment B raw15232step1 raw15232step1Labels := by
      have ha : raw15232step1 = (fun i j => raw15232step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15232step1 raw15232step0; decide +kernel
      have hl : raw15232step1Labels = raw15232step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15232step0 raw15232step0Labels permutation151 permutation3
    mixedMoment B raw15232step1 raw15232step1Labels = mixedMoment B raw15232step2 raw15232step2Labels := by
      have ha : raw15232step2 = -raw15232step1 := by apply Matrix.ext; change ∀ i j, raw15232step2 i j = -(raw15232step1 i j); unfold raw15232step2 raw15232step1; decide +kernel
      have hl : raw15232step2Labels = raw15232step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15232step2 raw15232step2Labels = mixedMoment B raw15232step3 raw15232step3Labels := by
      have ha : raw15232step3 = raw15232step2 := by apply Matrix.ext; unfold raw15232step3 raw15232step2; decide +kernel
      have hl : raw15232step2Labels = labelEmbedding6 ∘ raw15232step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15232step2 raw15232step2Labels raw15232step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw15233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15233Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15233step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15233 raw15233Labels = mixedMoment B node3868 node3868Labels := by
  calc
    mixedMoment B raw15233 raw15233Labels = mixedMoment B raw15233step0 raw15233step0Labels := by
      have hz : ∀ j, raw15233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15233step0 = (fun i j => raw15233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15233step0 raw15233; decide +kernel
      have hl : raw15233step0Labels = raw15233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15233 raw15233Labels permutation346 hz
    mixedMoment B raw15233step0 raw15233step0Labels = mixedMoment B raw15233step1 raw15233step1Labels := by
      have ha : raw15233step1 = (fun i j => raw15233step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15233step1 raw15233step0; decide +kernel
      have hl : raw15233step1Labels = raw15233step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15233step0 raw15233step0Labels permutation56 permutation3
    _ = mixedMoment B node3868 node3868Labels := by rfl

def raw15234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15234Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15234 raw15234Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw15234 raw15234Labels = mixedMoment B raw15234step0 raw15234step0Labels := by
      have ha : raw15234step0 = (fun i j => raw15234 (permutation509 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15234step0 raw15234; decide +kernel
      have hl : raw15234step0Labels = raw15234Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15234 raw15234Labels permutation509 permutation6
    _ = mixedMoment B node3869 node3869Labels := by rfl

def raw15235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15235Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15235step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15235step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15235 raw15235Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw15235 raw15235Labels = mixedMoment B raw15235step0 raw15235step0Labels := by
      have hz : ∀ j, raw15235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15235step0 = (fun i j => raw15235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15235step0 raw15235; decide +kernel
      have hl : raw15235step0Labels = raw15235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15235 raw15235Labels permutation346 hz
    mixedMoment B raw15235step0 raw15235step0Labels = mixedMoment B raw15235step1 raw15235step1Labels := by
      have ha : raw15235step1 = (fun i j => raw15235step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15235step1 raw15235step0; decide +kernel
      have hl : raw15235step1Labels = raw15235step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15235step0 raw15235step0Labels permutation101 permutation6
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw15236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15236Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15236step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15236step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15236 raw15236Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw15236 raw15236Labels = mixedMoment B raw15236step0 raw15236step0Labels := by
      have hz : ∀ j, raw15236 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15236step0 = (fun i j => raw15236 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15236step0 raw15236; decide +kernel
      have hl : raw15236step0Labels = raw15236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15236 raw15236Labels permutation346 hz
    mixedMoment B raw15236step0 raw15236step0Labels = mixedMoment B raw15236step1 raw15236step1Labels := by
      have ha : raw15236step1 = (fun i j => raw15236step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15236step1 raw15236step0; decide +kernel
      have hl : raw15236step1Labels = raw15236step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15236step0 raw15236step0Labels permutation101 permutation6
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw15237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15237Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15237step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15237step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15237 raw15237Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw15237 raw15237Labels = mixedMoment B raw15237step0 raw15237step0Labels := by
      have hz : ∀ j, raw15237 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15237step0 = (fun i j => raw15237 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15237step0 raw15237; decide +kernel
      have hl : raw15237step0Labels = raw15237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15237 raw15237Labels permutation346 hz
    mixedMoment B raw15237step0 raw15237step0Labels = mixedMoment B raw15237step1 raw15237step1Labels := by
      have ha : raw15237step1 = (fun i j => raw15237step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15237step1 raw15237step0; decide +kernel
      have hl : raw15237step1Labels = raw15237step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15237step0 raw15237step0Labels permutation101 permutation6
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw15238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15238Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15238step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15238step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15238step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15238step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15238 raw15238Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw15238 raw15238Labels = mixedMoment B raw15238step0 raw15238step0Labels := by
      have hz : ∀ j, raw15238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15238step0 = (fun i j => raw15238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15238step0 raw15238; decide +kernel
      have hl : raw15238step0Labels = raw15238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15238 raw15238Labels permutation346 hz
    mixedMoment B raw15238step0 raw15238step0Labels = mixedMoment B raw15238step1 raw15238step1Labels := by
      have hz : ∀ j, raw15238step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw15238step1 = (fun i j => raw15238step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw15238step1 raw15238step0; decide +kernel
      have hl : raw15238step1Labels = raw15238step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15238step0 raw15238step0Labels permutation56 hz
    mixedMoment B raw15238step1 raw15238step1Labels = mixedMoment B raw15238step2 raw15238step2Labels := by
      have ha : raw15238step2 = (fun i j => raw15238step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15238step2 raw15238step1; decide +kernel
      have hl : raw15238step2Labels = raw15238step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15238step1 raw15238step1Labels permutation8 permutation3
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw15239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15239 raw15239Labels = mixedMoment B node3714 node3714Labels := by
  calc
    mixedMoment B raw15239 raw15239Labels = mixedMoment B raw15239step0 raw15239step0Labels := by
      have ha : raw15239step0 = (fun i j => raw15239 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15239step0 raw15239; decide +kernel
      have hl : raw15239step0Labels = raw15239Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15239 raw15239Labels permutation271 permutation3
    _ = mixedMoment B node3714 node3714Labels := by rfl

def raw15240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15240 raw15240Labels = mixedMoment B node3559 node3559Labels := by
  calc
    mixedMoment B raw15240 raw15240Labels = mixedMoment B raw15240step0 raw15240step0Labels := by
      have ha : raw15240step0 = (fun i j => raw15240 (permutation509 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15240step0 raw15240; decide +kernel
      have hl : raw15240step0Labels = raw15240Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15240 raw15240Labels permutation509 permutation6
    _ = mixedMoment B node3559 node3559Labels := by rfl

def raw15241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15241 raw15241Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw15241 raw15241Labels = mixedMoment B raw15241step0 raw15241step0Labels := by
      have ha : raw15241step0 = (fun i j => raw15241 (permutation509 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15241step0 raw15241; decide +kernel
      have hl : raw15241step0Labels = raw15241Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15241 raw15241Labels permutation509 permutation6
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw15242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15242step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15242 raw15242Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw15242 raw15242Labels = mixedMoment B raw15242step0 raw15242step0Labels := by
      have ha : raw15242step0 = (fun i j => raw15242 (permutation509 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15242step0 raw15242; decide +kernel
      have hl : raw15242step0Labels = raw15242Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15242 raw15242Labels permutation509 permutation6
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw15243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15243step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15243 raw15243Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw15243 raw15243Labels = mixedMoment B raw15243step0 raw15243step0Labels := by
      have hz : ∀ j, raw15243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15243step0 = (fun i j => raw15243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15243step0 raw15243; decide +kernel
      have hl : raw15243step0Labels = raw15243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15243 raw15243Labels permutation346 hz
    mixedMoment B raw15243step0 raw15243step0Labels = mixedMoment B raw15243step1 raw15243step1Labels := by
      have ha : raw15243step1 = (fun i j => raw15243step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15243step1 raw15243step0; decide +kernel
      have hl : raw15243step1Labels = raw15243step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15243step0 raw15243step0Labels permutation56 permutation3
    _ = mixedMoment B node3733 node3733Labels := by rfl

def raw15244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15244step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15244 raw15244Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw15244 raw15244Labels = mixedMoment B raw15244step0 raw15244step0Labels := by
      have ha : raw15244step0 = (fun i j => raw15244 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15244step0 raw15244; decide +kernel
      have hl : raw15244step0Labels = raw15244Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15244 raw15244Labels permutation686 permutation3
    mixedMoment B raw15244step0 raw15244step0Labels = mixedMoment B raw15244step1 raw15244step1Labels := by
      have ha : raw15244step1 = -raw15244step0 := by apply Matrix.ext; change ∀ i j, raw15244step1 i j = -(raw15244step0 i j); unfold raw15244step1 raw15244step0; decide +kernel
      have hl : raw15244step1Labels = raw15244step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3949 node3949Labels := by rfl

def raw15245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15245step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15245step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw15245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15245 raw15245Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw15245 raw15245Labels = mixedMoment B raw15245step0 raw15245step0Labels := by
      have hz : ∀ j, raw15245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15245step0 = (fun i j => raw15245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15245step0 raw15245; decide +kernel
      have hl : raw15245step0Labels = raw15245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15245 raw15245Labels permutation346 hz
    mixedMoment B raw15245step0 raw15245step0Labels = mixedMoment B raw15245step1 raw15245step1Labels := by
      have ha : raw15245step1 = (fun i j => raw15245step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15245step1 raw15245step0; decide +kernel
      have hl : raw15245step1Labels = raw15245step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15245step0 raw15245step0Labels permutation145 permutation3
    mixedMoment B raw15245step1 raw15245step1Labels = mixedMoment B raw15245step2 raw15245step2Labels := by
      have ha : raw15245step2 = -raw15245step1 := by apply Matrix.ext; change ∀ i j, raw15245step2 i j = -(raw15245step1 i j); unfold raw15245step2 raw15245step1; decide +kernel
      have hl : raw15245step2Labels = raw15245step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4003 node4003Labels := by rfl

def raw15246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15246step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15246 raw15246Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw15246 raw15246Labels = mixedMoment B raw15246step0 raw15246step0Labels := by
      have hz : ∀ j, raw15246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15246step0 = (fun i j => raw15246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15246step0 raw15246; decide +kernel
      have hl : raw15246step0Labels = raw15246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15246 raw15246Labels permutation346 hz
    mixedMoment B raw15246step0 raw15246step0Labels = mixedMoment B raw15246step1 raw15246step1Labels := by
      have ha : raw15246step1 = (fun i j => raw15246step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15246step1 raw15246step0; decide +kernel
      have hl : raw15246step1Labels = raw15246step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15246step0 raw15246step0Labels permutation101 permutation6
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw15247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15247step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw15247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15247step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15247 raw15247Labels = mixedMoment B node3348 node3348Labels := by
  calc
    mixedMoment B raw15247 raw15247Labels = mixedMoment B raw15247step0 raw15247step0Labels := by
      have hz : ∀ j, raw15247 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15247step0 = (fun i j => raw15247 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15247step0 raw15247; decide +kernel
      have hl : raw15247step0Labels = raw15247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15247 raw15247Labels permutation346 hz
    mixedMoment B raw15247step0 raw15247step0Labels = mixedMoment B raw15247step1 raw15247step1Labels := by
      have ha : raw15247step1 = (fun i j => raw15247step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15247step1 raw15247step0; decide +kernel
      have hl : raw15247step1Labels = raw15247step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15247step0 raw15247step0Labels permutation126 permutation3
    mixedMoment B raw15247step1 raw15247step1Labels = mixedMoment B raw15247step2 raw15247step2Labels := by
      have ha : raw15247step2 = -raw15247step1 := by apply Matrix.ext; change ∀ i j, raw15247step2 i j = -(raw15247step1 i j); unfold raw15247step2 raw15247step1; decide +kernel
      have hl : raw15247step2Labels = raw15247step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3348 node3348Labels := by rfl

def raw15248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15248 raw15248Labels = mixedMoment B node3347 node3347Labels := by
  calc
    mixedMoment B raw15248 raw15248Labels = mixedMoment B raw15248step0 raw15248step0Labels := by
      have ha : raw15248step0 = (fun i j => raw15248 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15248step0 raw15248; decide +kernel
      have hl : raw15248step0Labels = raw15248Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15248 raw15248Labels permutation587 permutation3
    mixedMoment B raw15248step0 raw15248step0Labels = mixedMoment B raw15248step1 raw15248step1Labels := by
      have ha : raw15248step1 = -raw15248step0 := by apply Matrix.ext; change ∀ i j, raw15248step1 i j = -(raw15248step0 i j); unfold raw15248step1 raw15248step0; decide +kernel
      have hl : raw15248step1Labels = raw15248step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3347 node3347Labels := by rfl

def raw15249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15249step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw15249step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw15249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15249 raw15249Labels = mixedMoment B node3358 node3358Labels := by
  calc
    mixedMoment B raw15249 raw15249Labels = mixedMoment B raw15249step0 raw15249step0Labels := by
      have hz : ∀ j, raw15249 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15249step0 = (fun i j => raw15249 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15249step0 raw15249; decide +kernel
      have hl : raw15249step0Labels = raw15249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15249 raw15249Labels permutation346 hz
    mixedMoment B raw15249step0 raw15249step0Labels = mixedMoment B raw15249step1 raw15249step1Labels := by
      have ha : raw15249step1 = (fun i j => raw15249step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15249step1 raw15249step0; decide +kernel
      have hl : raw15249step1Labels = raw15249step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15249step0 raw15249step0Labels permutation125 permutation3
    mixedMoment B raw15249step1 raw15249step1Labels = mixedMoment B raw15249step2 raw15249step2Labels := by
      have ha : raw15249step2 = -raw15249step1 := by apply Matrix.ext; change ∀ i j, raw15249step2 i j = -(raw15249step1 i j); unfold raw15249step2 raw15249step1; decide +kernel
      have hl : raw15249step2Labels = raw15249step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3358 node3358Labels := by rfl

def raw15250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw15250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw15250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15250 raw15250Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw15250 raw15250Labels = mixedMoment B raw15250step0 raw15250step0Labels := by
      have hz : ∀ j, raw15250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15250step0 = (fun i j => raw15250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15250step0 raw15250; decide +kernel
      have hl : raw15250step0Labels = raw15250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15250 raw15250Labels permutation346 hz
    mixedMoment B raw15250step0 raw15250step0Labels = mixedMoment B raw15250step1 raw15250step1Labels := by
      have ha : raw15250step1 = (fun i j => raw15250step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15250step1 raw15250step0; decide +kernel
      have hl : raw15250step1Labels = raw15250step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15250step0 raw15250step0Labels permutation127 permutation3
    mixedMoment B raw15250step1 raw15250step1Labels = mixedMoment B raw15250step2 raw15250step2Labels := by
      have ha : raw15250step2 = -raw15250step1 := by apply Matrix.ext; change ∀ i j, raw15250step2 i j = -(raw15250step1 i j); unfold raw15250step2 raw15250step1; decide +kernel
      have hl : raw15250step2Labels = raw15250step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw15251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw15251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15251 raw15251Labels = mixedMoment B node2394 node2394Labels := by
  calc
    mixedMoment B raw15251 raw15251Labels = mixedMoment B raw15251step0 raw15251step0Labels := by
      have hz : ∀ j, raw15251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15251step0 = (fun i j => raw15251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15251step0 raw15251; decide +kernel
      have hl : raw15251step0Labels = raw15251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15251 raw15251Labels permutation346 hz
    mixedMoment B raw15251step0 raw15251step0Labels = mixedMoment B raw15251step1 raw15251step1Labels := by
      have ha : raw15251step1 = (fun i j => raw15251step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15251step1 raw15251step0; decide +kernel
      have hl : raw15251step1Labels = raw15251step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15251step0 raw15251step0Labels permutation150 permutation3
    mixedMoment B raw15251step1 raw15251step1Labels = mixedMoment B raw15251step2 raw15251step2Labels := by
      have ha : raw15251step2 = -raw15251step1 := by apply Matrix.ext; change ∀ i j, raw15251step2 i j = -(raw15251step1 i j); unfold raw15251step2 raw15251step1; decide +kernel
      have hl : raw15251step2Labels = raw15251step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2394 node2394Labels := by rfl

def raw15252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15252step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15252 raw15252Labels = mixedMoment B node2392 node2392Labels := by
  calc
    mixedMoment B raw15252 raw15252Labels = mixedMoment B raw15252step0 raw15252step0Labels := by
      have ha : raw15252step0 = (fun i j => raw15252 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15252step0 raw15252; decide +kernel
      have hl : raw15252step0Labels = raw15252Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15252 raw15252Labels permutation686 permutation3
    mixedMoment B raw15252step0 raw15252step0Labels = mixedMoment B raw15252step1 raw15252step1Labels := by
      have ha : raw15252step1 = -raw15252step0 := by apply Matrix.ext; change ∀ i j, raw15252step1 i j = -(raw15252step0 i j); unfold raw15252step1 raw15252step0; decide +kernel
      have hl : raw15252step1Labels = raw15252step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2392 node2392Labels := by rfl

def raw15253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15253step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw15253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw15253step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15253 raw15253Labels = mixedMoment B node2405 node2405Labels := by
  calc
    mixedMoment B raw15253 raw15253Labels = mixedMoment B raw15253step0 raw15253step0Labels := by
      have hz : ∀ j, raw15253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15253step0 = (fun i j => raw15253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15253step0 raw15253; decide +kernel
      have hl : raw15253step0Labels = raw15253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15253 raw15253Labels permutation346 hz
    mixedMoment B raw15253step0 raw15253step0Labels = mixedMoment B raw15253step1 raw15253step1Labels := by
      have ha : raw15253step1 = (fun i j => raw15253step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15253step1 raw15253step0; decide +kernel
      have hl : raw15253step1Labels = raw15253step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15253step0 raw15253step0Labels permutation149 permutation3
    mixedMoment B raw15253step1 raw15253step1Labels = mixedMoment B raw15253step2 raw15253step2Labels := by
      have ha : raw15253step2 = -raw15253step1 := by apply Matrix.ext; change ∀ i j, raw15253step2 i j = -(raw15253step1 i j); unfold raw15253step2 raw15253step1; decide +kernel
      have hl : raw15253step2Labels = raw15253step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2405 node2405Labels := by rfl

def raw15254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw15254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw15254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15254 raw15254Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw15254 raw15254Labels = mixedMoment B raw15254step0 raw15254step0Labels := by
      have hz : ∀ j, raw15254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15254step0 = (fun i j => raw15254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15254step0 raw15254; decide +kernel
      have hl : raw15254step0Labels = raw15254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15254 raw15254Labels permutation346 hz
    mixedMoment B raw15254step0 raw15254step0Labels = mixedMoment B raw15254step1 raw15254step1Labels := by
      have ha : raw15254step1 = (fun i j => raw15254step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15254step1 raw15254step0; decide +kernel
      have hl : raw15254step1Labels = raw15254step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15254step0 raw15254step0Labels permutation151 permutation3
    mixedMoment B raw15254step1 raw15254step1Labels = mixedMoment B raw15254step2 raw15254step2Labels := by
      have ha : raw15254step2 = -raw15254step1 := by apply Matrix.ext; change ∀ i j, raw15254step2 i j = -(raw15254step1 i j); unfold raw15254step2 raw15254step1; decide +kernel
      have hl : raw15254step2Labels = raw15254step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw15255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15255 raw15255Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw15255 raw15255Labels = mixedMoment B raw15255step0 raw15255step0Labels := by
      have hz : ∀ j, raw15255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15255step0 = (fun i j => raw15255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15255step0 raw15255; decide +kernel
      have hl : raw15255step0Labels = raw15255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15255 raw15255Labels permutation346 hz
    mixedMoment B raw15255step0 raw15255step0Labels = mixedMoment B raw15255step1 raw15255step1Labels := by
      have ha : raw15255step1 = (fun i j => raw15255step0 (permutation90 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15255step1 raw15255step0; decide +kernel
      have hl : raw15255step1Labels = raw15255step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15255step0 raw15255step0Labels permutation90 permutation4
    mixedMoment B raw15255step1 raw15255step1Labels = mixedMoment B raw15255step2 raw15255step2Labels := by
      have ha : raw15255step2 = -raw15255step1 := by apply Matrix.ext; change ∀ i j, raw15255step2 i j = -(raw15255step1 i j); unfold raw15255step2 raw15255step1; decide +kernel
      have hl : raw15255step2Labels = raw15255step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3733 node3733Labels := by rfl

def raw15256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15256 raw15256Labels = mixedMoment B node3819 node3819Labels := by
  calc
    mixedMoment B raw15256 raw15256Labels = mixedMoment B raw15256step0 raw15256step0Labels := by
      have ha : raw15256step0 = (fun i j => raw15256 (permutation458 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15256step0 raw15256; decide +kernel
      have hl : raw15256step0Labels = raw15256Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15256 raw15256Labels permutation458 permutation4
    mixedMoment B raw15256step0 raw15256step0Labels = mixedMoment B raw15256step1 raw15256step1Labels := by
      have ha : raw15256step1 = -raw15256step0 := by apply Matrix.ext; change ∀ i j, raw15256step1 i j = -(raw15256step0 i j); unfold raw15256step1 raw15256step0; decide +kernel
      have hl : raw15256step1Labels = raw15256step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3819 node3819Labels := by rfl

def raw15257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15257 raw15257Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw15257 raw15257Labels = mixedMoment B raw15257step0 raw15257step0Labels := by
      have hz : ∀ j, raw15257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15257step0 = (fun i j => raw15257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15257step0 raw15257; decide +kernel
      have hl : raw15257step0Labels = raw15257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15257 raw15257Labels permutation346 hz
    mixedMoment B raw15257step0 raw15257step0Labels = mixedMoment B raw15257step1 raw15257step1Labels := by
      have ha : raw15257step1 = (fun i j => raw15257step0 (permutation90 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15257step1 raw15257step0; decide +kernel
      have hl : raw15257step1Labels = raw15257step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15257step0 raw15257step0Labels permutation90 permutation4
    mixedMoment B raw15257step1 raw15257step1Labels = mixedMoment B raw15257step2 raw15257step2Labels := by
      have ha : raw15257step2 = -raw15257step1 := by apply Matrix.ext; change ∀ i j, raw15257step2 i j = -(raw15257step1 i j); unfold raw15257step2 raw15257step1; decide +kernel
      have hl : raw15257step2Labels = raw15257step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2591 node2591Labels := by rfl

def raw15258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15258step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15258 raw15258Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw15258 raw15258Labels = mixedMoment B raw15258step0 raw15258step0Labels := by
      have hz : ∀ j, raw15258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15258step0 = (fun i j => raw15258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15258step0 raw15258; decide +kernel
      have hl : raw15258step0Labels = raw15258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15258 raw15258Labels permutation346 hz
    mixedMoment B raw15258step0 raw15258step0Labels = mixedMoment B raw15258step1 raw15258step1Labels := by
      have ha : raw15258step1 = (fun i j => raw15258step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15258step1 raw15258step0; decide +kernel
      have hl : raw15258step1Labels = raw15258step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15258step0 raw15258step0Labels permutation91 permutation4
    mixedMoment B raw15258step1 raw15258step1Labels = mixedMoment B raw15258step2 raw15258step2Labels := by
      have ha : raw15258step2 = -raw15258step1 := by apply Matrix.ext; change ∀ i j, raw15258step2 i j = -(raw15258step1 i j); unfold raw15258step2 raw15258step1; decide +kernel
      have hl : raw15258step2Labels = raw15258step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw15259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15259Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15259step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15259 raw15259Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw15259 raw15259Labels = mixedMoment B raw15259step0 raw15259step0Labels := by
      have hz : ∀ j, raw15259 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15259step0 = (fun i j => raw15259 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15259step0 raw15259; decide +kernel
      have hl : raw15259step0Labels = raw15259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15259 raw15259Labels permutation346 hz
    mixedMoment B raw15259step0 raw15259step0Labels = mixedMoment B raw15259step1 raw15259step1Labels := by
      have ha : raw15259step1 = (fun i j => raw15259step0 (permutation90 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15259step1 raw15259step0; decide +kernel
      have hl : raw15259step1Labels = raw15259step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15259step0 raw15259step0Labels permutation90 permutation4
    mixedMoment B raw15259step1 raw15259step1Labels = mixedMoment B raw15259step2 raw15259step2Labels := by
      have ha : raw15259step2 = -raw15259step1 := by apply Matrix.ext; change ∀ i j, raw15259step2 i j = -(raw15259step1 i j); unfold raw15259step2 raw15259step1; decide +kernel
      have hl : raw15259step2Labels = raw15259step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw15260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw15260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15260 raw15260Labels = mixedMoment B node3729 node3729Labels := by
  calc
    mixedMoment B raw15260 raw15260Labels = mixedMoment B raw15260step0 raw15260step0Labels := by
      have ha : raw15260step0 = (fun i j => raw15260 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15260step0 raw15260; decide +kernel
      have hl : raw15260step0Labels = raw15260Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15260 raw15260Labels permutation160 permutation2
    _ = mixedMoment B node3729 node3729Labels := by rfl

def raw15261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15261 raw15261Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw15261 raw15261Labels = mixedMoment B raw15261step0 raw15261step0Labels := by
      have hz : ∀ j, raw15261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15261step0 = (fun i j => raw15261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15261step0 raw15261; decide +kernel
      have hl : raw15261step0Labels = raw15261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15261 raw15261Labels permutation346 hz
    mixedMoment B raw15261step0 raw15261step0Labels = mixedMoment B raw15261step1 raw15261step1Labels := by
      have ha : raw15261step1 = (fun i j => raw15261step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15261step1 raw15261step0; decide +kernel
      have hl : raw15261step1Labels = raw15261step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15261step0 raw15261step0Labels permutation34 permutation2
    _ = mixedMoment B node3733 node3733Labels := by rfl

def raw15262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15262Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15262step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw15262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15262 raw15262Labels = mixedMoment B node3010 node3010Labels := by
  calc
    mixedMoment B raw15262 raw15262Labels = mixedMoment B raw15262step0 raw15262step0Labels := by
      have hz : ∀ j, raw15262 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15262step0 = (fun i j => raw15262 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15262step0 raw15262; decide +kernel
      have hl : raw15262step0Labels = raw15262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15262 raw15262Labels permutation346 hz
    mixedMoment B raw15262step0 raw15262step0Labels = mixedMoment B raw15262step1 raw15262step1Labels := by
      have ha : raw15262step1 = (fun i j => raw15262step0 (permutation122 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15262step1 raw15262step0; decide +kernel
      have hl : raw15262step1Labels = raw15262step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15262step0 raw15262step0Labels permutation122 permutation4
    _ = mixedMoment B node3010 node3010Labels := by rfl

def raw15263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, -2, 1], ![0, 2, -2], ![-2, 2, 0], ![-2, 0, 2]]
def raw15263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw15263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15263 raw15263Labels = mixedMoment B node3010 node3010Labels := by
  calc
    mixedMoment B raw15263 raw15263Labels = mixedMoment B raw15263step0 raw15263step0Labels := by
      have hz : ∀ j, raw15263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15263step0 = (fun i j => raw15263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15263step0 raw15263; decide +kernel
      have hl : raw15263step0Labels = raw15263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15263 raw15263Labels permutation346 hz
    mixedMoment B raw15263step0 raw15263step0Labels = mixedMoment B raw15263step1 raw15263step1Labels := by
      have ha : raw15263step1 = (fun i j => raw15263step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15263step1 raw15263step0; decide +kernel
      have hl : raw15263step1Labels = raw15263step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15263step0 raw15263step0Labels permutation151 permutation2
    mixedMoment B raw15263step1 raw15263step1Labels = mixedMoment B raw15263step2 raw15263step2Labels := by
      have ha : raw15263step2 = -raw15263step1 := by apply Matrix.ext; change ∀ i j, raw15263step2 i j = -(raw15263step1 i j); unfold raw15263step2 raw15263step1; decide +kernel
      have hl : raw15263step2Labels = raw15263step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3010 node3010Labels := by rfl

def raw15264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw15264step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15264step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15264step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15264step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15264 raw15264Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw15264 raw15264Labels = mixedMoment B raw15264step0 raw15264step0Labels := by
      have hz : ∀ j, raw15264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15264step0 = (fun i j => raw15264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15264step0 raw15264; decide +kernel
      have hl : raw15264step0Labels = raw15264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15264 raw15264Labels permutation346 hz
    mixedMoment B raw15264step0 raw15264step0Labels = mixedMoment B raw15264step1 raw15264step1Labels := by
      have ha : raw15264step1 = (fun i j => raw15264step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15264step1 raw15264step0; decide +kernel
      have hl : raw15264step1Labels = raw15264step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15264step0 raw15264step0Labels permutation87 permutation6
    mixedMoment B raw15264step1 raw15264step1Labels = mixedMoment B raw15264step2 raw15264step2Labels := by
      have ha : raw15264step2 = -raw15264step1 := by apply Matrix.ext; change ∀ i j, raw15264step2 i j = -(raw15264step1 i j); unfold raw15264step2 raw15264step1; decide +kernel
      have hl : raw15264step2Labels = raw15264step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15264step2 raw15264step2Labels = mixedMoment B raw15264step3 raw15264step3Labels := by
      have ha : raw15264step3 = raw15264step2 := by apply Matrix.ext; unfold raw15264step3 raw15264step2; decide +kernel
      have hl : raw15264step2Labels = labelEmbedding9 ∘ raw15264step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15264step2 raw15264step2Labels raw15264step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw15265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw15265step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15265step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15265step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15265 raw15265Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw15265 raw15265Labels = mixedMoment B raw15265step0 raw15265step0Labels := by
      have ha : raw15265step0 = (fun i j => raw15265 (permutation452 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15265step0 raw15265; decide +kernel
      have hl : raw15265step0Labels = raw15265Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15265 raw15265Labels permutation452 permutation6
    mixedMoment B raw15265step0 raw15265step0Labels = mixedMoment B raw15265step1 raw15265step1Labels := by
      have ha : raw15265step1 = -raw15265step0 := by apply Matrix.ext; change ∀ i j, raw15265step1 i j = -(raw15265step0 i j); unfold raw15265step1 raw15265step0; decide +kernel
      have hl : raw15265step1Labels = raw15265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15265step1 raw15265step1Labels = mixedMoment B raw15265step2 raw15265step2Labels := by
      have ha : raw15265step2 = raw15265step1 := by apply Matrix.ext; unfold raw15265step2 raw15265step1; decide +kernel
      have hl : raw15265step1Labels = labelEmbedding9 ∘ raw15265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15265step1 raw15265step1Labels raw15265step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw15266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15266step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15266step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15266 raw15266Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw15266 raw15266Labels = mixedMoment B raw15266step0 raw15266step0Labels := by
      have hz : ∀ j, raw15266 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15266step0 = (fun i j => raw15266 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15266step0 raw15266; decide +kernel
      have hl : raw15266step0Labels = raw15266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15266 raw15266Labels permutation346 hz
    mixedMoment B raw15266step0 raw15266step0Labels = mixedMoment B raw15266step1 raw15266step1Labels := by
      have ha : raw15266step1 = (fun i j => raw15266step0 (permutation122 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15266step1 raw15266step0; decide +kernel
      have hl : raw15266step1Labels = raw15266step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15266step0 raw15266step0Labels permutation122 permutation7
    mixedMoment B raw15266step1 raw15266step1Labels = mixedMoment B raw15266step2 raw15266step2Labels := by
      have ha : raw15266step2 = raw15266step1 := by apply Matrix.ext; unfold raw15266step2 raw15266step1; decide +kernel
      have hl : raw15266step1Labels = labelEmbedding10 ∘ raw15266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15266step1 raw15266step1Labels raw15266step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw15267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw15267step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15267step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15267step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15267step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15267 raw15267Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw15267 raw15267Labels = mixedMoment B raw15267step0 raw15267step0Labels := by
      have hz : ∀ j, raw15267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15267step0 = (fun i j => raw15267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15267step0 raw15267; decide +kernel
      have hl : raw15267step0Labels = raw15267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15267 raw15267Labels permutation346 hz
    mixedMoment B raw15267step0 raw15267step0Labels = mixedMoment B raw15267step1 raw15267step1Labels := by
      have ha : raw15267step1 = (fun i j => raw15267step0 (permutation105 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15267step1 raw15267step0; decide +kernel
      have hl : raw15267step1Labels = raw15267step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15267step0 raw15267step0Labels permutation105 permutation4
    mixedMoment B raw15267step1 raw15267step1Labels = mixedMoment B raw15267step2 raw15267step2Labels := by
      have ha : raw15267step2 = -raw15267step1 := by apply Matrix.ext; change ∀ i j, raw15267step2 i j = -(raw15267step1 i j); unfold raw15267step2 raw15267step1; decide +kernel
      have hl : raw15267step2Labels = raw15267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15267step2 raw15267step2Labels = mixedMoment B raw15267step3 raw15267step3Labels := by
      have ha : raw15267step3 = raw15267step2 := by apply Matrix.ext; unfold raw15267step3 raw15267step2; decide +kernel
      have hl : raw15267step2Labels = labelEmbedding7 ∘ raw15267step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15267step2 raw15267step2Labels raw15267step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw15268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15268step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15268step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15268step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15268 raw15268Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw15268 raw15268Labels = mixedMoment B raw15268step0 raw15268step0Labels := by
      have hz : ∀ j, raw15268 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15268step0 = (fun i j => raw15268 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15268step0 raw15268; decide +kernel
      have hl : raw15268step0Labels = raw15268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15268 raw15268Labels permutation346 hz
    mixedMoment B raw15268step0 raw15268step0Labels = mixedMoment B raw15268step1 raw15268step1Labels := by
      have ha : raw15268step1 = (fun i j => raw15268step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15268step1 raw15268step0; decide +kernel
      have hl : raw15268step1Labels = raw15268step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15268step0 raw15268step0Labels permutation87 permutation6
    mixedMoment B raw15268step1 raw15268step1Labels = mixedMoment B raw15268step2 raw15268step2Labels := by
      have ha : raw15268step2 = -raw15268step1 := by apply Matrix.ext; change ∀ i j, raw15268step2 i j = -(raw15268step1 i j); unfold raw15268step2 raw15268step1; decide +kernel
      have hl : raw15268step2Labels = raw15268step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15268step2 raw15268step2Labels = mixedMoment B raw15268step3 raw15268step3Labels := by
      have ha : raw15268step3 = raw15268step2 := by apply Matrix.ext; unfold raw15268step3 raw15268step2; decide +kernel
      have hl : raw15268step2Labels = labelEmbedding9 ∘ raw15268step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15268step2 raw15268step2Labels raw15268step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw15269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15269step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15269step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15269step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15269step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15269 raw15269Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw15269 raw15269Labels = mixedMoment B raw15269step0 raw15269step0Labels := by
      have hz : ∀ j, raw15269 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15269step0 = (fun i j => raw15269 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15269step0 raw15269; decide +kernel
      have hl : raw15269step0Labels = raw15269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15269 raw15269Labels permutation346 hz
    mixedMoment B raw15269step0 raw15269step0Labels = mixedMoment B raw15269step1 raw15269step1Labels := by
      have ha : raw15269step1 = (fun i j => raw15269step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15269step1 raw15269step0; decide +kernel
      have hl : raw15269step1Labels = raw15269step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15269step0 raw15269step0Labels permutation45 permutation5
    mixedMoment B raw15269step1 raw15269step1Labels = mixedMoment B raw15269step2 raw15269step2Labels := by
      have ha : raw15269step2 = -raw15269step1 := by apply Matrix.ext; change ∀ i j, raw15269step2 i j = -(raw15269step1 i j); unfold raw15269step2 raw15269step1; decide +kernel
      have hl : raw15269step2Labels = raw15269step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15269step2 raw15269step2Labels = mixedMoment B raw15269step3 raw15269step3Labels := by
      have ha : raw15269step3 = raw15269step2 := by apply Matrix.ext; unfold raw15269step3 raw15269step2; decide +kernel
      have hl : raw15269step2Labels = labelEmbedding8 ∘ raw15269step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15269step2 raw15269step2Labels raw15269step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw15270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15270step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15270 raw15270Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw15270 raw15270Labels = mixedMoment B raw15270step0 raw15270step0Labels := by
      have ha : raw15270step0 = (fun i j => raw15270 (permutation465 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15270step0 raw15270; decide +kernel
      have hl : raw15270step0Labels = raw15270Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15270 raw15270Labels permutation465 permutation4
    mixedMoment B raw15270step0 raw15270step0Labels = mixedMoment B raw15270step1 raw15270step1Labels := by
      have ha : raw15270step1 = raw15270step0 := by apply Matrix.ext; unfold raw15270step1 raw15270step0; decide +kernel
      have hl : raw15270step0Labels = labelEmbedding7 ∘ raw15270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15270step0 raw15270step0Labels raw15270step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5402 node5402Labels := by rfl

def raw15271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15271step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15271step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15271 raw15271Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw15271 raw15271Labels = mixedMoment B raw15271step0 raw15271step0Labels := by
      have hz : ∀ j, raw15271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15271step0 = (fun i j => raw15271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15271step0 raw15271; decide +kernel
      have hl : raw15271step0Labels = raw15271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15271 raw15271Labels permutation346 hz
    mixedMoment B raw15271step0 raw15271step0Labels = mixedMoment B raw15271step1 raw15271step1Labels := by
      have ha : raw15271step1 = (fun i j => raw15271step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15271step1 raw15271step0; decide +kernel
      have hl : raw15271step1Labels = raw15271step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15271step0 raw15271step0Labels permutation38 permutation3
    mixedMoment B raw15271step1 raw15271step1Labels = mixedMoment B raw15271step2 raw15271step2Labels := by
      have ha : raw15271step2 = raw15271step1 := by apply Matrix.ext; unfold raw15271step2 raw15271step1; decide +kernel
      have hl : raw15271step1Labels = labelEmbedding6 ∘ raw15271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15271step1 raw15271step1Labels raw15271step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw15272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15272step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15272step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15272step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15272step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15272 raw15272Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw15272 raw15272Labels = mixedMoment B raw15272step0 raw15272step0Labels := by
      have hz : ∀ j, raw15272 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15272step0 = (fun i j => raw15272 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15272step0 raw15272; decide +kernel
      have hl : raw15272step0Labels = raw15272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15272 raw15272Labels permutation346 hz
    mixedMoment B raw15272step0 raw15272step0Labels = mixedMoment B raw15272step1 raw15272step1Labels := by
      have ha : raw15272step1 = (fun i j => raw15272step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15272step1 raw15272step0; decide +kernel
      have hl : raw15272step1Labels = raw15272step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15272step0 raw15272step0Labels permutation108 permutation4
    mixedMoment B raw15272step1 raw15272step1Labels = mixedMoment B raw15272step2 raw15272step2Labels := by
      have ha : raw15272step2 = -raw15272step1 := by apply Matrix.ext; change ∀ i j, raw15272step2 i j = -(raw15272step1 i j); unfold raw15272step2 raw15272step1; decide +kernel
      have hl : raw15272step2Labels = raw15272step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15272step2 raw15272step2Labels = mixedMoment B raw15272step3 raw15272step3Labels := by
      have ha : raw15272step3 = raw15272step2 := by apply Matrix.ext; unfold raw15272step3 raw15272step2; decide +kernel
      have hl : raw15272step2Labels = labelEmbedding7 ∘ raw15272step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15272step2 raw15272step2Labels raw15272step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw15273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15273step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15273 raw15273Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw15273 raw15273Labels = mixedMoment B raw15273step0 raw15273step0Labels := by
      have hz : ∀ j, raw15273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15273step0 = (fun i j => raw15273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15273step0 raw15273; decide +kernel
      have hl : raw15273step0Labels = raw15273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15273 raw15273Labels permutation346 hz
    mixedMoment B raw15273step0 raw15273step0Labels = mixedMoment B raw15273step1 raw15273step1Labels := by
      have ha : raw15273step1 = (fun i j => raw15273step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15273step1 raw15273step0; decide +kernel
      have hl : raw15273step1Labels = raw15273step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15273step0 raw15273step0Labels permutation91 permutation4
    mixedMoment B raw15273step1 raw15273step1Labels = mixedMoment B raw15273step2 raw15273step2Labels := by
      have ha : raw15273step2 = raw15273step1 := by apply Matrix.ext; unfold raw15273step2 raw15273step1; decide +kernel
      have hl : raw15273step1Labels = labelEmbedding7 ∘ raw15273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15273step1 raw15273step1Labels raw15273step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw15274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15274step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15274 raw15274Labels = mixedMoment B node4813 node4813Labels := by
  calc
    mixedMoment B raw15274 raw15274Labels = mixedMoment B raw15274step0 raw15274step0Labels := by
      have ha : raw15274step0 = (fun i j => raw15274 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15274step0 raw15274; decide +kernel
      have hl : raw15274step0Labels = raw15274Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15274 raw15274Labels permutation160 permutation3
    mixedMoment B raw15274step0 raw15274step0Labels = mixedMoment B raw15274step1 raw15274step1Labels := by
      have ha : raw15274step1 = raw15274step0 := by apply Matrix.ext; unfold raw15274step1 raw15274step0; decide +kernel
      have hl : raw15274step0Labels = labelEmbedding6 ∘ raw15274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15274step0 raw15274step0Labels raw15274step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4813 node4813Labels := by rfl

def raw15275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15275step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15275 raw15275Labels = mixedMoment B node5358 node5358Labels := by
  calc
    mixedMoment B raw15275 raw15275Labels = mixedMoment B raw15275step0 raw15275step0Labels := by
      have ha : raw15275step0 = (fun i j => raw15275 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15275step0 raw15275; decide +kernel
      have hl : raw15275step0Labels = raw15275Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15275 raw15275Labels permutation160 permutation3
    mixedMoment B raw15275step0 raw15275step0Labels = mixedMoment B raw15275step1 raw15275step1Labels := by
      have ha : raw15275step1 = raw15275step0 := by apply Matrix.ext; unfold raw15275step1 raw15275step0; decide +kernel
      have hl : raw15275step0Labels = labelEmbedding6 ∘ raw15275step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15275step0 raw15275step0Labels raw15275step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5358 node5358Labels := by rfl

def raw15276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15276step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15276 raw15276Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw15276 raw15276Labels = mixedMoment B raw15276step0 raw15276step0Labels := by
      have ha : raw15276step0 = (fun i j => raw15276 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15276step0 raw15276; decide +kernel
      have hl : raw15276step0Labels = raw15276Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15276 raw15276Labels permutation160 permutation3
    mixedMoment B raw15276step0 raw15276step0Labels = mixedMoment B raw15276step1 raw15276step1Labels := by
      have ha : raw15276step1 = raw15276step0 := by apply Matrix.ext; unfold raw15276step1 raw15276step0; decide +kernel
      have hl : raw15276step0Labels = labelEmbedding6 ∘ raw15276step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15276step0 raw15276step0Labels raw15276step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw15277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15277step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15277step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15277step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15277step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15277 raw15277Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw15277 raw15277Labels = mixedMoment B raw15277step0 raw15277step0Labels := by
      have ha : raw15277step0 = (fun i j => raw15277 (permutation225 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15277step0 raw15277; decide +kernel
      have hl : raw15277step0Labels = raw15277Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15277 raw15277Labels permutation225 permutation5
    mixedMoment B raw15277step0 raw15277step0Labels = mixedMoment B raw15277step1 raw15277step1Labels := by
      have ha : raw15277step1 = -raw15277step0 := by apply Matrix.ext; change ∀ i j, raw15277step1 i j = -(raw15277step0 i j); unfold raw15277step1 raw15277step0; decide +kernel
      have hl : raw15277step1Labels = raw15277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15277step1 raw15277step1Labels = mixedMoment B raw15277step2 raw15277step2Labels := by
      have ha : raw15277step2 = raw15277step1 := by apply Matrix.ext; unfold raw15277step2 raw15277step1; decide +kernel
      have hl : raw15277step1Labels = labelEmbedding8 ∘ raw15277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15277step1 raw15277step1Labels raw15277step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw15278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15278step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15278 raw15278Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw15278 raw15278Labels = mixedMoment B raw15278step0 raw15278step0Labels := by
      have ha : raw15278step0 = (fun i j => raw15278 (permutation474 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15278step0 raw15278; decide +kernel
      have hl : raw15278step0Labels = raw15278Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15278 raw15278Labels permutation474 permutation4
    mixedMoment B raw15278step0 raw15278step0Labels = mixedMoment B raw15278step1 raw15278step1Labels := by
      have ha : raw15278step1 = raw15278step0 := by apply Matrix.ext; unfold raw15278step1 raw15278step0; decide +kernel
      have hl : raw15278step0Labels = labelEmbedding7 ∘ raw15278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15278step0 raw15278step0Labels raw15278step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw15279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw15279step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw15279step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15279 raw15279Labels = mixedMoment B node4829 node4829Labels := by
  calc
    mixedMoment B raw15279 raw15279Labels = mixedMoment B raw15279step0 raw15279step0Labels := by
      have hz : ∀ j, raw15279 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15279step0 = (fun i j => raw15279 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15279step0 raw15279; decide +kernel
      have hl : raw15279step0Labels = raw15279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15279 raw15279Labels permutation346 hz
    mixedMoment B raw15279step0 raw15279step0Labels = mixedMoment B raw15279step1 raw15279step1Labels := by
      have ha : raw15279step1 = (fun i j => raw15279step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15279step1 raw15279step0; decide +kernel
      have hl : raw15279step1Labels = raw15279step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15279step0 raw15279step0Labels permutation34 permutation3
    mixedMoment B raw15279step1 raw15279step1Labels = mixedMoment B raw15279step2 raw15279step2Labels := by
      have ha : raw15279step2 = raw15279step1 := by apply Matrix.ext; unfold raw15279step2 raw15279step1; decide +kernel
      have hl : raw15279step1Labels = labelEmbedding6 ∘ raw15279step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15279step1 raw15279step1Labels raw15279step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4829 node4829Labels := by rfl

def raw15280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15280step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15280step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15280 raw15280Labels = mixedMoment B node5200 node5200Labels := by
  calc
    mixedMoment B raw15280 raw15280Labels = mixedMoment B raw15280step0 raw15280step0Labels := by
      have hz : ∀ j, raw15280 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15280step0 = (fun i j => raw15280 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15280step0 raw15280; decide +kernel
      have hl : raw15280step0Labels = raw15280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15280 raw15280Labels permutation346 hz
    mixedMoment B raw15280step0 raw15280step0Labels = mixedMoment B raw15280step1 raw15280step1Labels := by
      have ha : raw15280step1 = (fun i j => raw15280step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15280step1 raw15280step0; decide +kernel
      have hl : raw15280step1Labels = raw15280step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15280step0 raw15280step0Labels permutation101 permutation4
    mixedMoment B raw15280step1 raw15280step1Labels = mixedMoment B raw15280step2 raw15280step2Labels := by
      have ha : raw15280step2 = raw15280step1 := by apply Matrix.ext; unfold raw15280step2 raw15280step1; decide +kernel
      have hl : raw15280step1Labels = labelEmbedding7 ∘ raw15280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15280step1 raw15280step1Labels raw15280step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5200 node5200Labels := by rfl

def raw15281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15281step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15281 raw15281Labels = mixedMoment B node5186 node5186Labels := by
  calc
    mixedMoment B raw15281 raw15281Labels = mixedMoment B raw15281step0 raw15281step0Labels := by
      have ha : raw15281step0 = (fun i j => raw15281 (permutation509 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15281step0 raw15281; decide +kernel
      have hl : raw15281step0Labels = raw15281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15281 raw15281Labels permutation509 permutation4
    mixedMoment B raw15281step0 raw15281step0Labels = mixedMoment B raw15281step1 raw15281step1Labels := by
      have ha : raw15281step1 = raw15281step0 := by apply Matrix.ext; unfold raw15281step1 raw15281step0; decide +kernel
      have hl : raw15281step0Labels = labelEmbedding7 ∘ raw15281step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15281step0 raw15281step0Labels raw15281step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5186 node5186Labels := by rfl

def raw15282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw15282step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw15282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15282 raw15282Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw15282 raw15282Labels = mixedMoment B raw15282step0 raw15282step0Labels := by
      have hz : ∀ j, raw15282 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15282step0 = (fun i j => raw15282 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15282step0 raw15282; decide +kernel
      have hl : raw15282step0Labels = raw15282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15282 raw15282Labels permutation346 hz
    mixedMoment B raw15282step0 raw15282step0Labels = mixedMoment B raw15282step1 raw15282step1Labels := by
      have ha : raw15282step1 = (fun i j => raw15282step0 (permutation100 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15282step1 raw15282step0; decide +kernel
      have hl : raw15282step1Labels = raw15282step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15282step0 raw15282step0Labels permutation100 permutation4
    mixedMoment B raw15282step1 raw15282step1Labels = mixedMoment B raw15282step2 raw15282step2Labels := by
      have ha : raw15282step2 = raw15282step1 := by apply Matrix.ext; unfold raw15282step2 raw15282step1; decide +kernel
      have hl : raw15282step1Labels = labelEmbedding7 ∘ raw15282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15282step1 raw15282step1Labels raw15282step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw15283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15283step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15283step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15283 raw15283Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw15283 raw15283Labels = mixedMoment B raw15283step0 raw15283step0Labels := by
      have hz : ∀ j, raw15283 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15283step0 = (fun i j => raw15283 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15283step0 raw15283; decide +kernel
      have hl : raw15283step0Labels = raw15283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15283 raw15283Labels permutation346 hz
    mixedMoment B raw15283step0 raw15283step0Labels = mixedMoment B raw15283step1 raw15283step1Labels := by
      have ha : raw15283step1 = (fun i j => raw15283step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15283step1 raw15283step0; decide +kernel
      have hl : raw15283step1Labels = raw15283step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15283step0 raw15283step0Labels permutation91 permutation4
    mixedMoment B raw15283step1 raw15283step1Labels = mixedMoment B raw15283step2 raw15283step2Labels := by
      have ha : raw15283step2 = raw15283step1 := by apply Matrix.ext; unfold raw15283step2 raw15283step1; decide +kernel
      have hl : raw15283step1Labels = labelEmbedding7 ∘ raw15283step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15283step1 raw15283step1Labels raw15283step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw15284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15284step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15284step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15284 raw15284Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw15284 raw15284Labels = mixedMoment B raw15284step0 raw15284step0Labels := by
      have hz : ∀ j, raw15284 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15284step0 = (fun i j => raw15284 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15284step0 raw15284; decide +kernel
      have hl : raw15284step0Labels = raw15284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15284 raw15284Labels permutation346 hz
    mixedMoment B raw15284step0 raw15284step0Labels = mixedMoment B raw15284step1 raw15284step1Labels := by
      have ha : raw15284step1 = (fun i j => raw15284step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15284step1 raw15284step0; decide +kernel
      have hl : raw15284step1Labels = raw15284step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15284step0 raw15284step0Labels permutation32 permutation3
    mixedMoment B raw15284step1 raw15284step1Labels = mixedMoment B raw15284step2 raw15284step2Labels := by
      have ha : raw15284step2 = raw15284step1 := by apply Matrix.ext; unfold raw15284step2 raw15284step1; decide +kernel
      have hl : raw15284step1Labels = labelEmbedding6 ∘ raw15284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15284step1 raw15284step1Labels raw15284step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw15285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15285 raw15285Labels = mixedMoment B node5361 node5361Labels := by
  calc
    mixedMoment B raw15285 raw15285Labels = mixedMoment B raw15285step0 raw15285step0Labels := by
      have hz : ∀ j, raw15285 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15285step0 = (fun i j => raw15285 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15285step0 raw15285; decide +kernel
      have hl : raw15285step0Labels = raw15285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15285 raw15285Labels permutation346 hz
    mixedMoment B raw15285step0 raw15285step0Labels = mixedMoment B raw15285step1 raw15285step1Labels := by
      have ha : raw15285step1 = (fun i j => raw15285step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15285step1 raw15285step0; decide +kernel
      have hl : raw15285step1Labels = raw15285step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15285step0 raw15285step0Labels permutation126 permutation2
    mixedMoment B raw15285step1 raw15285step1Labels = mixedMoment B raw15285step2 raw15285step2Labels := by
      have ha : raw15285step2 = -raw15285step1 := by apply Matrix.ext; change ∀ i j, raw15285step2 i j = -(raw15285step1 i j); unfold raw15285step2 raw15285step1; decide +kernel
      have hl : raw15285step2Labels = raw15285step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5361 node5361Labels := by rfl

def raw15286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw15286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15286 raw15286Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw15286 raw15286Labels = mixedMoment B raw15286step0 raw15286step0Labels := by
      have ha : raw15286step0 = (fun i j => raw15286 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15286step0 raw15286; decide +kernel
      have hl : raw15286step0Labels = raw15286Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15286 raw15286Labels permutation589 permutation2
    mixedMoment B raw15286step0 raw15286step0Labels = mixedMoment B raw15286step1 raw15286step1Labels := by
      have ha : raw15286step1 = -raw15286step0 := by apply Matrix.ext; change ∀ i j, raw15286step1 i j = -(raw15286step0 i j); unfold raw15286step1 raw15286step0; decide +kernel
      have hl : raw15286step1Labels = raw15286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw15287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15287 raw15287Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw15287 raw15287Labels = mixedMoment B raw15287step0 raw15287step0Labels := by
      have hz : ∀ j, raw15287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15287step0 = (fun i j => raw15287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15287step0 raw15287; decide +kernel
      have hl : raw15287step0Labels = raw15287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15287 raw15287Labels permutation346 hz
    mixedMoment B raw15287step0 raw15287step0Labels = mixedMoment B raw15287step1 raw15287step1Labels := by
      have ha : raw15287step1 = (fun i j => raw15287step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15287step1 raw15287step0; decide +kernel
      have hl : raw15287step1Labels = raw15287step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15287step0 raw15287step0Labels permutation125 permutation2
    mixedMoment B raw15287step1 raw15287step1Labels = mixedMoment B raw15287step2 raw15287step2Labels := by
      have ha : raw15287step2 = -raw15287step1 := by apply Matrix.ext; change ∀ i j, raw15287step2 i j = -(raw15287step1 i j); unfold raw15287step2 raw15287step1; decide +kernel
      have hl : raw15287step2Labels = raw15287step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw15288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15288step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15288 raw15288Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw15288 raw15288Labels = mixedMoment B raw15288step0 raw15288step0Labels := by
      have hz : ∀ j, raw15288 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15288step0 = (fun i j => raw15288 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15288step0 raw15288; decide +kernel
      have hl : raw15288step0Labels = raw15288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15288 raw15288Labels permutation346 hz
    mixedMoment B raw15288step0 raw15288step0Labels = mixedMoment B raw15288step1 raw15288step1Labels := by
      have ha : raw15288step1 = (fun i j => raw15288step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15288step1 raw15288step0; decide +kernel
      have hl : raw15288step1Labels = raw15288step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15288step0 raw15288step0Labels permutation127 permutation2
    mixedMoment B raw15288step1 raw15288step1Labels = mixedMoment B raw15288step2 raw15288step2Labels := by
      have ha : raw15288step2 = -raw15288step1 := by apply Matrix.ext; change ∀ i j, raw15288step2 i j = -(raw15288step1 i j); unfold raw15288step2 raw15288step1; decide +kernel
      have hl : raw15288step2Labels = raw15288step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw15289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw15289step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw15289step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15289 raw15289Labels = mixedMoment B node4814 node4814Labels := by
  calc
    mixedMoment B raw15289 raw15289Labels = mixedMoment B raw15289step0 raw15289step0Labels := by
      have hz : ∀ j, raw15289 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15289step0 = (fun i j => raw15289 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15289step0 raw15289; decide +kernel
      have hl : raw15289step0Labels = raw15289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15289 raw15289Labels permutation346 hz
    mixedMoment B raw15289step0 raw15289step0Labels = mixedMoment B raw15289step1 raw15289step1Labels := by
      have ha : raw15289step1 = (fun i j => raw15289step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15289step1 raw15289step0; decide +kernel
      have hl : raw15289step1Labels = raw15289step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15289step0 raw15289step0Labels permutation32 permutation3
    mixedMoment B raw15289step1 raw15289step1Labels = mixedMoment B raw15289step2 raw15289step2Labels := by
      have ha : raw15289step2 = raw15289step1 := by apply Matrix.ext; unfold raw15289step2 raw15289step1; decide +kernel
      have hl : raw15289step1Labels = labelEmbedding6 ∘ raw15289step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15289step1 raw15289step1Labels raw15289step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4814 node4814Labels := by rfl

def raw15290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw15290step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15290step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15290step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15290step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15290 raw15290Labels = mixedMoment B node5180 node5180Labels := by
  calc
    mixedMoment B raw15290 raw15290Labels = mixedMoment B raw15290step0 raw15290step0Labels := by
      have hz : ∀ j, raw15290 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15290step0 = (fun i j => raw15290 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15290step0 raw15290; decide +kernel
      have hl : raw15290step0Labels = raw15290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15290 raw15290Labels permutation346 hz
    mixedMoment B raw15290step0 raw15290step0Labels = mixedMoment B raw15290step1 raw15290step1Labels := by
      have ha : raw15290step1 = (fun i j => raw15290step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15290step1 raw15290step0; decide +kernel
      have hl : raw15290step1Labels = raw15290step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15290step0 raw15290step0Labels permutation151 permutation3
    mixedMoment B raw15290step1 raw15290step1Labels = mixedMoment B raw15290step2 raw15290step2Labels := by
      have ha : raw15290step2 = -raw15290step1 := by apply Matrix.ext; change ∀ i j, raw15290step2 i j = -(raw15290step1 i j); unfold raw15290step2 raw15290step1; decide +kernel
      have hl : raw15290step2Labels = raw15290step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15290step2 raw15290step2Labels = mixedMoment B raw15290step3 raw15290step3Labels := by
      have ha : raw15290step3 = raw15290step2 := by apply Matrix.ext; unfold raw15290step3 raw15290step2; decide +kernel
      have hl : raw15290step2Labels = labelEmbedding6 ∘ raw15290step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15290step2 raw15290step2Labels raw15290step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5180 node5180Labels := by rfl

def raw15291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15291step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15291step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15291step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15291 raw15291Labels = mixedMoment B node5178 node5178Labels := by
  calc
    mixedMoment B raw15291 raw15291Labels = mixedMoment B raw15291step0 raw15291step0Labels := by
      have ha : raw15291step0 = (fun i j => raw15291 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15291step0 raw15291; decide +kernel
      have hl : raw15291step0Labels = raw15291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15291 raw15291Labels permutation686 permutation3
    mixedMoment B raw15291step0 raw15291step0Labels = mixedMoment B raw15291step1 raw15291step1Labels := by
      have ha : raw15291step1 = -raw15291step0 := by apply Matrix.ext; change ∀ i j, raw15291step1 i j = -(raw15291step0 i j); unfold raw15291step1 raw15291step0; decide +kernel
      have hl : raw15291step1Labels = raw15291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15291step1 raw15291step1Labels = mixedMoment B raw15291step2 raw15291step2Labels := by
      have ha : raw15291step2 = raw15291step1 := by apply Matrix.ext; unfold raw15291step2 raw15291step1; decide +kernel
      have hl : raw15291step1Labels = labelEmbedding6 ∘ raw15291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15291step1 raw15291step1Labels raw15291step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5178 node5178Labels := by rfl

def raw15292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15292step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw15292step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw15292step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15292 raw15292Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw15292 raw15292Labels = mixedMoment B raw15292step0 raw15292step0Labels := by
      have hz : ∀ j, raw15292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15292step0 = (fun i j => raw15292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15292step0 raw15292; decide +kernel
      have hl : raw15292step0Labels = raw15292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15292 raw15292Labels permutation346 hz
    mixedMoment B raw15292step0 raw15292step0Labels = mixedMoment B raw15292step1 raw15292step1Labels := by
      have ha : raw15292step1 = (fun i j => raw15292step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15292step1 raw15292step0; decide +kernel
      have hl : raw15292step1Labels = raw15292step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15292step0 raw15292step0Labels permutation151 permutation3
    mixedMoment B raw15292step1 raw15292step1Labels = mixedMoment B raw15292step2 raw15292step2Labels := by
      have ha : raw15292step2 = -raw15292step1 := by apply Matrix.ext; change ∀ i j, raw15292step2 i j = -(raw15292step1 i j); unfold raw15292step2 raw15292step1; decide +kernel
      have hl : raw15292step2Labels = raw15292step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15292step2 raw15292step2Labels = mixedMoment B raw15292step3 raw15292step3Labels := by
      have ha : raw15292step3 = raw15292step2 := by apply Matrix.ext; unfold raw15292step3 raw15292step2; decide +kernel
      have hl : raw15292step2Labels = labelEmbedding6 ∘ raw15292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15292step2 raw15292step2Labels raw15292step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw15293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw15293step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw15293step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw15293step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15293 raw15293Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw15293 raw15293Labels = mixedMoment B raw15293step0 raw15293step0Labels := by
      have hz : ∀ j, raw15293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15293step0 = (fun i j => raw15293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15293step0 raw15293; decide +kernel
      have hl : raw15293step0Labels = raw15293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15293 raw15293Labels permutation346 hz
    mixedMoment B raw15293step0 raw15293step0Labels = mixedMoment B raw15293step1 raw15293step1Labels := by
      have ha : raw15293step1 = (fun i j => raw15293step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15293step1 raw15293step0; decide +kernel
      have hl : raw15293step1Labels = raw15293step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15293step0 raw15293step0Labels permutation145 permutation3
    mixedMoment B raw15293step1 raw15293step1Labels = mixedMoment B raw15293step2 raw15293step2Labels := by
      have ha : raw15293step2 = -raw15293step1 := by apply Matrix.ext; change ∀ i j, raw15293step2 i j = -(raw15293step1 i j); unfold raw15293step2 raw15293step1; decide +kernel
      have hl : raw15293step2Labels = raw15293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15293step2 raw15293step2Labels = mixedMoment B raw15293step3 raw15293step3Labels := by
      have ha : raw15293step3 = raw15293step2 := by apply Matrix.ext; unfold raw15293step3 raw15293step2; decide +kernel
      have hl : raw15293step2Labels = labelEmbedding6 ∘ raw15293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15293step2 raw15293step2Labels raw15293step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw15294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15294step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw15294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15294 raw15294Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw15294 raw15294Labels = mixedMoment B raw15294step0 raw15294step0Labels := by
      have hz : ∀ j, raw15294 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15294step0 = (fun i j => raw15294 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15294step0 raw15294; decide +kernel
      have hl : raw15294step0Labels = raw15294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15294 raw15294Labels permutation346 hz
    mixedMoment B raw15294step0 raw15294step0Labels = mixedMoment B raw15294step1 raw15294step1Labels := by
      have ha : raw15294step1 = (fun i j => raw15294step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15294step1 raw15294step0; decide +kernel
      have hl : raw15294step1Labels = raw15294step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15294step0 raw15294step0Labels permutation87 permutation6
    mixedMoment B raw15294step1 raw15294step1Labels = mixedMoment B raw15294step2 raw15294step2Labels := by
      have ha : raw15294step2 = -raw15294step1 := by apply Matrix.ext; change ∀ i j, raw15294step2 i j = -(raw15294step1 i j); unfold raw15294step2 raw15294step1; decide +kernel
      have hl : raw15294step2Labels = raw15294step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw15295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw15295step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15295 raw15295Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw15295 raw15295Labels = mixedMoment B raw15295step0 raw15295step0Labels := by
      have ha : raw15295step0 = (fun i j => raw15295 (permutation452 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15295step0 raw15295; decide +kernel
      have hl : raw15295step0Labels = raw15295Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15295 raw15295Labels permutation452 permutation6
    mixedMoment B raw15295step0 raw15295step0Labels = mixedMoment B raw15295step1 raw15295step1Labels := by
      have ha : raw15295step1 = -raw15295step0 := by apply Matrix.ext; change ∀ i j, raw15295step1 i j = -(raw15295step0 i j); unfold raw15295step1 raw15295step0; decide +kernel
      have hl : raw15295step1Labels = raw15295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw15296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw15296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15296 raw15296Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw15296 raw15296Labels = mixedMoment B raw15296step0 raw15296step0Labels := by
      have hz : ∀ j, raw15296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15296step0 = (fun i j => raw15296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15296step0 raw15296; decide +kernel
      have hl : raw15296step0Labels = raw15296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15296 raw15296Labels permutation346 hz
    mixedMoment B raw15296step0 raw15296step0Labels = mixedMoment B raw15296step1 raw15296step1Labels := by
      have ha : raw15296step1 = (fun i j => raw15296step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15296step1 raw15296step0; decide +kernel
      have hl : raw15296step1Labels = raw15296step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15296step0 raw15296step0Labels permutation87 permutation6
    mixedMoment B raw15296step1 raw15296step1Labels = mixedMoment B raw15296step2 raw15296step2Labels := by
      have ha : raw15296step2 = -raw15296step1 := by apply Matrix.ext; change ∀ i j, raw15296step2 i j = -(raw15296step1 i j); unfold raw15296step2 raw15296step1; decide +kernel
      have hl : raw15296step2Labels = raw15296step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw15297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw15297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15297 raw15297Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw15297 raw15297Labels = mixedMoment B raw15297step0 raw15297step0Labels := by
      have hz : ∀ j, raw15297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15297step0 = (fun i j => raw15297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15297step0 raw15297; decide +kernel
      have hl : raw15297step0Labels = raw15297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15297 raw15297Labels permutation346 hz
    mixedMoment B raw15297step0 raw15297step0Labels = mixedMoment B raw15297step1 raw15297step1Labels := by
      have ha : raw15297step1 = (fun i j => raw15297step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15297step1 raw15297step0; decide +kernel
      have hl : raw15297step1Labels = raw15297step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15297step0 raw15297step0Labels permutation87 permutation6
    mixedMoment B raw15297step1 raw15297step1Labels = mixedMoment B raw15297step2 raw15297step2Labels := by
      have ha : raw15297step2 = -raw15297step1 := by apply Matrix.ext; change ∀ i j, raw15297step2 i j = -(raw15297step1 i j); unfold raw15297step2 raw15297step1; decide +kernel
      have hl : raw15297step2Labels = raw15297step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw15298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15298 raw15298Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw15298 raw15298Labels = mixedMoment B raw15298step0 raw15298step0Labels := by
      have hz : ∀ j, raw15298 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15298step0 = (fun i j => raw15298 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15298step0 raw15298; decide +kernel
      have hl : raw15298step0Labels = raw15298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15298 raw15298Labels permutation346 hz
    mixedMoment B raw15298step0 raw15298step0Labels = mixedMoment B raw15298step1 raw15298step1Labels := by
      have ha : raw15298step1 = (fun i j => raw15298step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15298step1 raw15298step0; decide +kernel
      have hl : raw15298step1Labels = raw15298step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15298step0 raw15298step0Labels permutation87 permutation6
    mixedMoment B raw15298step1 raw15298step1Labels = mixedMoment B raw15298step2 raw15298step2Labels := by
      have ha : raw15298step2 = -raw15298step1 := by apply Matrix.ext; change ∀ i j, raw15298step2 i j = -(raw15298step1 i j); unfold raw15298step2 raw15298step1; decide +kernel
      have hl : raw15298step2Labels = raw15298step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw15299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15299 raw15299Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw15299 raw15299Labels = mixedMoment B raw15299step0 raw15299step0Labels := by
      have hz : ∀ j, raw15299 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15299step0 = (fun i j => raw15299 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15299step0 raw15299; decide +kernel
      have hl : raw15299step0Labels = raw15299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15299 raw15299Labels permutation346 hz
    mixedMoment B raw15299step0 raw15299step0Labels = mixedMoment B raw15299step1 raw15299step1Labels := by
      have ha : raw15299step1 = (fun i j => raw15299step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15299step1 raw15299step0; decide +kernel
      have hl : raw15299step1Labels = raw15299step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15299step0 raw15299step0Labels permutation32 permutation3
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw15300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15300 raw15300Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw15300 raw15300Labels = mixedMoment B raw15300step0 raw15300step0Labels := by
      have ha : raw15300step0 = (fun i j => raw15300 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15300step0 raw15300; decide +kernel
      have hl : raw15300step0Labels = raw15300Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15300 raw15300Labels permutation176 permutation3
    _ = mixedMoment B node3802 node3802Labels := by rfl

def raw15301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15301 raw15301Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw15301 raw15301Labels = mixedMoment B raw15301step0 raw15301step0Labels := by
      have hz : ∀ j, raw15301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15301step0 = (fun i j => raw15301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15301step0 raw15301; decide +kernel
      have hl : raw15301step0Labels = raw15301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15301 raw15301Labels permutation346 hz
    mixedMoment B raw15301step0 raw15301step0Labels = mixedMoment B raw15301step1 raw15301step1Labels := by
      have ha : raw15301step1 = (fun i j => raw15301step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15301step1 raw15301step0; decide +kernel
      have hl : raw15301step1Labels = raw15301step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15301step0 raw15301step0Labels permutation38 permutation3
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw15302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw15302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw15302step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15302 raw15302Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw15302 raw15302Labels = mixedMoment B raw15302step0 raw15302step0Labels := by
      have hz : ∀ j, raw15302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15302step0 = (fun i j => raw15302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15302step0 raw15302; decide +kernel
      have hl : raw15302step0Labels = raw15302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15302 raw15302Labels permutation346 hz
    mixedMoment B raw15302step0 raw15302step0Labels = mixedMoment B raw15302step1 raw15302step1Labels := by
      have ha : raw15302step1 = (fun i j => raw15302step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15302step1 raw15302step0; decide +kernel
      have hl : raw15302step1Labels = raw15302step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15302step0 raw15302step0Labels permutation87 permutation6
    mixedMoment B raw15302step1 raw15302step1Labels = mixedMoment B raw15302step2 raw15302step2Labels := by
      have ha : raw15302step2 = -raw15302step1 := by apply Matrix.ext; change ∀ i j, raw15302step2 i j = -(raw15302step1 i j); unfold raw15302step2 raw15302step1; decide +kernel
      have hl : raw15302step2Labels = raw15302step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw15303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15303step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15303 raw15303Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw15303 raw15303Labels = mixedMoment B raw15303step0 raw15303step0Labels := by
      have hz : ∀ j, raw15303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15303step0 = (fun i j => raw15303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15303step0 raw15303; decide +kernel
      have hl : raw15303step0Labels = raw15303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15303 raw15303Labels permutation346 hz
    mixedMoment B raw15303step0 raw15303step0Labels = mixedMoment B raw15303step1 raw15303step1Labels := by
      have ha : raw15303step1 = (fun i j => raw15303step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15303step1 raw15303step0; decide +kernel
      have hl : raw15303step1Labels = raw15303step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15303step0 raw15303step0Labels permutation87 permutation6
    mixedMoment B raw15303step1 raw15303step1Labels = mixedMoment B raw15303step2 raw15303step2Labels := by
      have ha : raw15303step2 = -raw15303step1 := by apply Matrix.ext; change ∀ i j, raw15303step2 i j = -(raw15303step1 i j); unfold raw15303step2 raw15303step1; decide +kernel
      have hl : raw15303step2Labels = raw15303step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw15304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15304step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15304 raw15304Labels = mixedMoment B node2031 node2031Labels := by
  calc
    mixedMoment B raw15304 raw15304Labels = mixedMoment B raw15304step0 raw15304step0Labels := by
      have ha : raw15304step0 = (fun i j => raw15304 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15304step0 raw15304; decide +kernel
      have hl : raw15304step0Labels = raw15304Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15304 raw15304Labels permutation160 permutation3
    _ = mixedMoment B node2031 node2031Labels := by rfl

def raw15305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15305 raw15305Labels = mixedMoment B node3696 node3696Labels := by
  calc
    mixedMoment B raw15305 raw15305Labels = mixedMoment B raw15305step0 raw15305step0Labels := by
      have ha : raw15305step0 = (fun i j => raw15305 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15305step0 raw15305; decide +kernel
      have hl : raw15305step0Labels = raw15305Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15305 raw15305Labels permutation160 permutation3
    _ = mixedMoment B node3696 node3696Labels := by rfl

def raw15306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15306step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15306 raw15306Labels = mixedMoment B node3827 node3827Labels := by
  calc
    mixedMoment B raw15306 raw15306Labels = mixedMoment B raw15306step0 raw15306step0Labels := by
      have ha : raw15306step0 = (fun i j => raw15306 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15306step0 raw15306; decide +kernel
      have hl : raw15306step0Labels = raw15306Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15306 raw15306Labels permutation160 permutation3
    _ = mixedMoment B node3827 node3827Labels := by rfl

def raw15307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15307 raw15307Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw15307 raw15307Labels = mixedMoment B raw15307step0 raw15307step0Labels := by
      have ha : raw15307step0 = (fun i j => raw15307 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15307step0 raw15307; decide +kernel
      have hl : raw15307step0Labels = raw15307Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15307 raw15307Labels permutation166 permutation3
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw15308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15308 raw15308Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw15308 raw15308Labels = mixedMoment B raw15308step0 raw15308step0Labels := by
      have ha : raw15308step0 = (fun i j => raw15308 (permutation457 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15308step0 raw15308; decide +kernel
      have hl : raw15308step0Labels = raw15308Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15308 raw15308Labels permutation457 permutation6
    mixedMoment B raw15308step0 raw15308step0Labels = mixedMoment B raw15308step1 raw15308step1Labels := by
      have ha : raw15308step1 = -raw15308step0 := by apply Matrix.ext; change ∀ i j, raw15308step1 i j = -(raw15308step0 i j); unfold raw15308step1 raw15308step0; decide +kernel
      have hl : raw15308step1Labels = raw15308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw15309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw15309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15309 raw15309Labels = mixedMoment B node2049 node2049Labels := by
  calc
    mixedMoment B raw15309 raw15309Labels = mixedMoment B raw15309step0 raw15309step0Labels := by
      have hz : ∀ j, raw15309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15309step0 = (fun i j => raw15309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15309step0 raw15309; decide +kernel
      have hl : raw15309step0Labels = raw15309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15309 raw15309Labels permutation346 hz
    mixedMoment B raw15309step0 raw15309step0Labels = mixedMoment B raw15309step1 raw15309step1Labels := by
      have ha : raw15309step1 = (fun i j => raw15309step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15309step1 raw15309step0; decide +kernel
      have hl : raw15309step1Labels = raw15309step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15309step0 raw15309step0Labels permutation34 permutation3
    _ = mixedMoment B node2049 node2049Labels := by rfl

def raw15310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15310step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15310 raw15310Labels = mixedMoment B node3575 node3575Labels := by
  calc
    mixedMoment B raw15310 raw15310Labels = mixedMoment B raw15310step0 raw15310step0Labels := by
      have hz : ∀ j, raw15310 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15310step0 = (fun i j => raw15310 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15310step0 raw15310; decide +kernel
      have hl : raw15310step0Labels = raw15310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15310 raw15310Labels permutation346 hz
    mixedMoment B raw15310step0 raw15310step0Labels = mixedMoment B raw15310step1 raw15310step1Labels := by
      have ha : raw15310step1 = (fun i j => raw15310step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15310step1 raw15310step0; decide +kernel
      have hl : raw15310step1Labels = raw15310step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15310step0 raw15310step0Labels permutation87 permutation6
    mixedMoment B raw15310step1 raw15310step1Labels = mixedMoment B raw15310step2 raw15310step2Labels := by
      have ha : raw15310step2 = -raw15310step1 := by apply Matrix.ext; change ∀ i j, raw15310step2 i j = -(raw15310step1 i j); unfold raw15310step2 raw15310step1; decide +kernel
      have hl : raw15310step2Labels = raw15310step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3575 node3575Labels := by rfl

def raw15311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15311 raw15311Labels = mixedMoment B node3527 node3527Labels := by
  calc
    mixedMoment B raw15311 raw15311Labels = mixedMoment B raw15311step0 raw15311step0Labels := by
      have ha : raw15311step0 = (fun i j => raw15311 (permutation457 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15311step0 raw15311; decide +kernel
      have hl : raw15311step0Labels = raw15311Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15311 raw15311Labels permutation457 permutation6
    mixedMoment B raw15311step0 raw15311step0Labels = mixedMoment B raw15311step1 raw15311step1Labels := by
      have ha : raw15311step1 = -raw15311step0 := by apply Matrix.ext; change ∀ i j, raw15311step1 i j = -(raw15311step0 i j); unfold raw15311step1 raw15311step0; decide +kernel
      have hl : raw15311step1Labels = raw15311step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3527 node3527Labels := by rfl

def raw15312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15312step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw15312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw15312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15312 raw15312Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw15312 raw15312Labels = mixedMoment B raw15312step0 raw15312step0Labels := by
      have hz : ∀ j, raw15312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15312step0 = (fun i j => raw15312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15312step0 raw15312; decide +kernel
      have hl : raw15312step0Labels = raw15312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15312 raw15312Labels permutation346 hz
    mixedMoment B raw15312step0 raw15312step0Labels = mixedMoment B raw15312step1 raw15312step1Labels := by
      have ha : raw15312step1 = (fun i j => raw15312step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15312step1 raw15312step0; decide +kernel
      have hl : raw15312step1Labels = raw15312step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15312step0 raw15312step0Labels permutation87 permutation6
    mixedMoment B raw15312step1 raw15312step1Labels = mixedMoment B raw15312step2 raw15312step2Labels := by
      have ha : raw15312step2 = -raw15312step1 := by apply Matrix.ext; change ∀ i j, raw15312step2 i j = -(raw15312step1 i j); unfold raw15312step2 raw15312step1; decide +kernel
      have hl : raw15312step2Labels = raw15312step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw15313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw15313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15313 raw15313Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw15313 raw15313Labels = mixedMoment B raw15313step0 raw15313step0Labels := by
      have hz : ∀ j, raw15313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15313step0 = (fun i j => raw15313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15313step0 raw15313; decide +kernel
      have hl : raw15313step0Labels = raw15313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15313 raw15313Labels permutation346 hz
    mixedMoment B raw15313step0 raw15313step0Labels = mixedMoment B raw15313step1 raw15313step1Labels := by
      have ha : raw15313step1 = (fun i j => raw15313step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15313step1 raw15313step0; decide +kernel
      have hl : raw15313step1Labels = raw15313step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15313step0 raw15313step0Labels permutation87 permutation6
    mixedMoment B raw15313step1 raw15313step1Labels = mixedMoment B raw15313step2 raw15313step2Labels := by
      have ha : raw15313step2 = -raw15313step1 := by apply Matrix.ext; change ∀ i j, raw15313step2 i j = -(raw15313step1 i j); unfold raw15313step2 raw15313step1; decide +kernel
      have hl : raw15313step2Labels = raw15313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw15314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15314Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15314step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15314 raw15314Labels = mixedMoment B node2039 node2039Labels := by
  calc
    mixedMoment B raw15314 raw15314Labels = mixedMoment B raw15314step0 raw15314step0Labels := by
      have hz : ∀ j, raw15314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15314step0 = (fun i j => raw15314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15314step0 raw15314; decide +kernel
      have hl : raw15314step0Labels = raw15314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15314 raw15314Labels permutation346 hz
    mixedMoment B raw15314step0 raw15314step0Labels = mixedMoment B raw15314step1 raw15314step1Labels := by
      have ha : raw15314step1 = (fun i j => raw15314step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15314step1 raw15314step0; decide +kernel
      have hl : raw15314step1Labels = raw15314step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15314step0 raw15314step0Labels permutation32 permutation3
    _ = mixedMoment B node2039 node2039Labels := by rfl

def raw15315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15315 raw15315Labels = mixedMoment B node3699 node3699Labels := by
  calc
    mixedMoment B raw15315 raw15315Labels = mixedMoment B raw15315step0 raw15315step0Labels := by
      have hz : ∀ j, raw15315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15315step0 = (fun i j => raw15315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15315step0 raw15315; decide +kernel
      have hl : raw15315step0Labels = raw15315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15315 raw15315Labels permutation346 hz
    mixedMoment B raw15315step0 raw15315step0Labels = mixedMoment B raw15315step1 raw15315step1Labels := by
      have ha : raw15315step1 = (fun i j => raw15315step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15315step1 raw15315step0; decide +kernel
      have hl : raw15315step1Labels = raw15315step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15315step0 raw15315step0Labels permutation32 permutation3
    _ = mixedMoment B node3699 node3699Labels := by rfl

def raw15316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15316 raw15316Labels = mixedMoment B node3780 node3780Labels := by
  calc
    mixedMoment B raw15316 raw15316Labels = mixedMoment B raw15316step0 raw15316step0Labels := by
      have ha : raw15316step0 = (fun i j => raw15316 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15316step0 raw15316; decide +kernel
      have hl : raw15316step0Labels = raw15316Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15316 raw15316Labels permutation176 permutation3
    _ = mixedMoment B node3780 node3780Labels := by rfl

def raw15317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15317step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15317 raw15317Labels = mixedMoment B node3831 node3831Labels := by
  calc
    mixedMoment B raw15317 raw15317Labels = mixedMoment B raw15317step0 raw15317step0Labels := by
      have hz : ∀ j, raw15317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15317step0 = (fun i j => raw15317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15317step0 raw15317; decide +kernel
      have hl : raw15317step0Labels = raw15317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15317 raw15317Labels permutation346 hz
    mixedMoment B raw15317step0 raw15317step0Labels = mixedMoment B raw15317step1 raw15317step1Labels := by
      have ha : raw15317step1 = (fun i j => raw15317step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15317step1 raw15317step0; decide +kernel
      have hl : raw15317step1Labels = raw15317step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15317step0 raw15317step0Labels permutation32 permutation3
    _ = mixedMoment B node3831 node3831Labels := by rfl

def raw15318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15318step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15318 raw15318Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw15318 raw15318Labels = mixedMoment B raw15318step0 raw15318step0Labels := by
      have hz : ∀ j, raw15318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15318step0 = (fun i j => raw15318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15318step0 raw15318; decide +kernel
      have hl : raw15318step0Labels = raw15318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15318 raw15318Labels permutation346 hz
    mixedMoment B raw15318step0 raw15318step0Labels = mixedMoment B raw15318step1 raw15318step1Labels := by
      have ha : raw15318step1 = (fun i j => raw15318step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15318step1 raw15318step0; decide +kernel
      have hl : raw15318step1Labels = raw15318step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15318step0 raw15318step0Labels permutation33 permutation3
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw15319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw15319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15319 raw15319Labels = mixedMoment B node2032 node2032Labels := by
  calc
    mixedMoment B raw15319 raw15319Labels = mixedMoment B raw15319step0 raw15319step0Labels := by
      have hz : ∀ j, raw15319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15319step0 = (fun i j => raw15319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15319step0 raw15319; decide +kernel
      have hl : raw15319step0Labels = raw15319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15319 raw15319Labels permutation346 hz
    mixedMoment B raw15319step0 raw15319step0Labels = mixedMoment B raw15319step1 raw15319step1Labels := by
      have ha : raw15319step1 = (fun i j => raw15319step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15319step1 raw15319step0; decide +kernel
      have hl : raw15319step1Labels = raw15319step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15319step0 raw15319step0Labels permutation32 permutation3
    _ = mixedMoment B node2032 node2032Labels := by rfl

def raw15320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw15320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15320step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15320 raw15320Labels = mixedMoment B node2608 node2608Labels := by
  calc
    mixedMoment B raw15320 raw15320Labels = mixedMoment B raw15320step0 raw15320step0Labels := by
      have hz : ∀ j, raw15320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15320step0 = (fun i j => raw15320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15320step0 raw15320; decide +kernel
      have hl : raw15320step0Labels = raw15320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15320 raw15320Labels permutation346 hz
    mixedMoment B raw15320step0 raw15320step0Labels = mixedMoment B raw15320step1 raw15320step1Labels := by
      have ha : raw15320step1 = (fun i j => raw15320step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15320step1 raw15320step0; decide +kernel
      have hl : raw15320step1Labels = raw15320step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15320step0 raw15320step0Labels permutation151 permutation3
    mixedMoment B raw15320step1 raw15320step1Labels = mixedMoment B raw15320step2 raw15320step2Labels := by
      have ha : raw15320step2 = -raw15320step1 := by apply Matrix.ext; change ∀ i j, raw15320step2 i j = -(raw15320step1 i j); unfold raw15320step2 raw15320step1; decide +kernel
      have hl : raw15320step2Labels = raw15320step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2608 node2608Labels := by rfl

def raw15321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15321 raw15321Labels = mixedMoment B node2606 node2606Labels := by
  calc
    mixedMoment B raw15321 raw15321Labels = mixedMoment B raw15321step0 raw15321step0Labels := by
      have ha : raw15321step0 = (fun i j => raw15321 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15321step0 raw15321; decide +kernel
      have hl : raw15321step0Labels = raw15321Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15321 raw15321Labels permutation686 permutation3
    mixedMoment B raw15321step0 raw15321step0Labels = mixedMoment B raw15321step1 raw15321step1Labels := by
      have ha : raw15321step1 = -raw15321step0 := by apply Matrix.ext; change ∀ i j, raw15321step1 i j = -(raw15321step0 i j); unfold raw15321step1 raw15321step0; decide +kernel
      have hl : raw15321step1Labels = raw15321step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2606 node2606Labels := by rfl

def raw15322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15322step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw15322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15322 raw15322Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw15322 raw15322Labels = mixedMoment B raw15322step0 raw15322step0Labels := by
      have hz : ∀ j, raw15322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15322step0 = (fun i j => raw15322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15322step0 raw15322; decide +kernel
      have hl : raw15322step0Labels = raw15322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15322 raw15322Labels permutation346 hz
    mixedMoment B raw15322step0 raw15322step0Labels = mixedMoment B raw15322step1 raw15322step1Labels := by
      have ha : raw15322step1 = (fun i j => raw15322step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15322step1 raw15322step0; decide +kernel
      have hl : raw15322step1Labels = raw15322step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15322step0 raw15322step0Labels permutation151 permutation3
    mixedMoment B raw15322step1 raw15322step1Labels = mixedMoment B raw15322step2 raw15322step2Labels := by
      have ha : raw15322step2 = -raw15322step1 := by apply Matrix.ext; change ∀ i j, raw15322step2 i j = -(raw15322step1 i j); unfold raw15322step2 raw15322step1; decide +kernel
      have hl : raw15322step2Labels = raw15322step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2632 node2632Labels := by rfl

def raw15323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15323step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw15323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw15323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15323 raw15323Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw15323 raw15323Labels = mixedMoment B raw15323step0 raw15323step0Labels := by
      have hz : ∀ j, raw15323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15323step0 = (fun i j => raw15323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15323step0 raw15323; decide +kernel
      have hl : raw15323step0Labels = raw15323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15323 raw15323Labels permutation346 hz
    mixedMoment B raw15323step0 raw15323step0Labels = mixedMoment B raw15323step1 raw15323step1Labels := by
      have ha : raw15323step1 = (fun i j => raw15323step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15323step1 raw15323step0; decide +kernel
      have hl : raw15323step1Labels = raw15323step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15323step0 raw15323step0Labels permutation145 permutation3
    mixedMoment B raw15323step1 raw15323step1Labels = mixedMoment B raw15323step2 raw15323step2Labels := by
      have ha : raw15323step2 = -raw15323step1 := by apply Matrix.ext; change ∀ i j, raw15323step2 i j = -(raw15323step1 i j); unfold raw15323step2 raw15323step1; decide +kernel
      have hl : raw15323step2Labels = raw15323step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw15324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15324step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15324 raw15324Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw15324 raw15324Labels = mixedMoment B raw15324step0 raw15324step0Labels := by
      have hz : ∀ j, raw15324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15324step0 = (fun i j => raw15324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15324step0 raw15324; decide +kernel
      have hl : raw15324step0Labels = raw15324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15324 raw15324Labels permutation346 hz
    mixedMoment B raw15324step0 raw15324step0Labels = mixedMoment B raw15324step1 raw15324step1Labels := by
      have ha : raw15324step1 = (fun i j => raw15324step0 (permutation122 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15324step1 raw15324step0; decide +kernel
      have hl : raw15324step1Labels = raw15324step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15324step0 raw15324step0Labels permutation122 permutation7
    mixedMoment B raw15324step1 raw15324step1Labels = mixedMoment B raw15324step2 raw15324step2Labels := by
      have ha : raw15324step2 = raw15324step1 := by apply Matrix.ext; unfold raw15324step2 raw15324step1; decide +kernel
      have hl : raw15324step1Labels = labelEmbedding1 ∘ raw15324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15324step1 raw15324step1Labels raw15324step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw15325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15325step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15325 raw15325Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw15325 raw15325Labels = mixedMoment B raw15325step0 raw15325step0Labels := by
      have ha : raw15325step0 = (fun i j => raw15325 (permutation571 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15325step0 raw15325; decide +kernel
      have hl : raw15325step0Labels = raw15325Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15325 raw15325Labels permutation571 permutation7
    mixedMoment B raw15325step0 raw15325step0Labels = mixedMoment B raw15325step1 raw15325step1Labels := by
      have ha : raw15325step1 = raw15325step0 := by apply Matrix.ext; unfold raw15325step1 raw15325step0; decide +kernel
      have hl : raw15325step0Labels = labelEmbedding1 ∘ raw15325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15325step0 raw15325step0Labels raw15325step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw15326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15326 raw15326Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw15326 raw15326Labels = mixedMoment B raw15326step0 raw15326step0Labels := by
      have hz : ∀ j, raw15326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15326step0 = (fun i j => raw15326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15326step0 raw15326; decide +kernel
      have hl : raw15326step0Labels = raw15326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15326 raw15326Labels permutation346 hz
    mixedMoment B raw15326step0 raw15326step0Labels = mixedMoment B raw15326step1 raw15326step1Labels := by
      have ha : raw15326step1 = (fun i j => raw15326step0 (permutation122 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15326step1 raw15326step0; decide +kernel
      have hl : raw15326step1Labels = raw15326step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15326step0 raw15326step0Labels permutation122 permutation7
    mixedMoment B raw15326step1 raw15326step1Labels = mixedMoment B raw15326step2 raw15326step2Labels := by
      have ha : raw15326step2 = raw15326step1 := by apply Matrix.ext; unfold raw15326step2 raw15326step1; decide +kernel
      have hl : raw15326step1Labels = labelEmbedding1 ∘ raw15326step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15326step1 raw15326step1Labels raw15326step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw15327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15327step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15327 raw15327Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw15327 raw15327Labels = mixedMoment B raw15327step0 raw15327step0Labels := by
      have hz : ∀ j, raw15327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15327step0 = (fun i j => raw15327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15327step0 raw15327; decide +kernel
      have hl : raw15327step0Labels = raw15327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15327 raw15327Labels permutation346 hz
    mixedMoment B raw15327step0 raw15327step0Labels = mixedMoment B raw15327step1 raw15327step1Labels := by
      have ha : raw15327step1 = (fun i j => raw15327step0 (permutation100 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15327step1 raw15327step0; decide +kernel
      have hl : raw15327step1Labels = raw15327step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15327step0 raw15327step0Labels permutation100 permutation5
    mixedMoment B raw15327step1 raw15327step1Labels = mixedMoment B raw15327step2 raw15327step2Labels := by
      have ha : raw15327step2 = raw15327step1 := by apply Matrix.ext; unfold raw15327step2 raw15327step1; decide +kernel
      have hl : raw15327step1Labels = labelEmbedding1 ∘ raw15327step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15327step1 raw15327step1Labels raw15327step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4027 node4027Labels := by rfl

def raw15328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15328step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15328step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15328 raw15328Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw15328 raw15328Labels = mixedMoment B raw15328step0 raw15328step0Labels := by
      have hz : ∀ j, raw15328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15328step0 = (fun i j => raw15328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15328step0 raw15328; decide +kernel
      have hl : raw15328step0Labels = raw15328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15328 raw15328Labels permutation346 hz
    mixedMoment B raw15328step0 raw15328step0Labels = mixedMoment B raw15328step1 raw15328step1Labels := by
      have ha : raw15328step1 = (fun i j => raw15328step0 (permutation122 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15328step1 raw15328step0; decide +kernel
      have hl : raw15328step1Labels = raw15328step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15328step0 raw15328step0Labels permutation122 permutation7
    mixedMoment B raw15328step1 raw15328step1Labels = mixedMoment B raw15328step2 raw15328step2Labels := by
      have ha : raw15328step2 = raw15328step1 := by apply Matrix.ext; unfold raw15328step2 raw15328step1; decide +kernel
      have hl : raw15328step1Labels = labelEmbedding1 ∘ raw15328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15328step1 raw15328step1Labels raw15328step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw15329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15329step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15329step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15329step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15329step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15329 raw15329Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw15329 raw15329Labels = mixedMoment B raw15329step0 raw15329step0Labels := by
      have hz : ∀ j, raw15329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15329step0 = (fun i j => raw15329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15329step0 raw15329; decide +kernel
      have hl : raw15329step0Labels = raw15329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15329 raw15329Labels permutation346 hz
    mixedMoment B raw15329step0 raw15329step0Labels = mixedMoment B raw15329step1 raw15329step1Labels := by
      have ha : raw15329step1 = (fun i j => raw15329step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15329step1 raw15329step0; decide +kernel
      have hl : raw15329step1Labels = raw15329step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15329step0 raw15329step0Labels permutation45 permutation5
    mixedMoment B raw15329step1 raw15329step1Labels = mixedMoment B raw15329step2 raw15329step2Labels := by
      have ha : raw15329step2 = -raw15329step1 := by apply Matrix.ext; change ∀ i j, raw15329step2 i j = -(raw15329step1 i j); unfold raw15329step2 raw15329step1; decide +kernel
      have hl : raw15329step2Labels = raw15329step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15329step2 raw15329step2Labels = mixedMoment B raw15329step3 raw15329step3Labels := by
      have ha : raw15329step3 = raw15329step2 := by apply Matrix.ext; unfold raw15329step3 raw15329step2; decide +kernel
      have hl : raw15329step2Labels = labelEmbedding1 ∘ raw15329step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15329step2 raw15329step2Labels raw15329step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2108 node2108Labels := by rfl

def raw15330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15330step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15330step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15330 raw15330Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw15330 raw15330Labels = mixedMoment B raw15330step0 raw15330step0Labels := by
      have ha : raw15330step0 = (fun i j => raw15330 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15330step0 raw15330; decide +kernel
      have hl : raw15330step0Labels = raw15330Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15330 raw15330Labels permutation189 permutation5
    mixedMoment B raw15330step0 raw15330step0Labels = mixedMoment B raw15330step1 raw15330step1Labels := by
      have ha : raw15330step1 = -raw15330step0 := by apply Matrix.ext; change ∀ i j, raw15330step1 i j = -(raw15330step0 i j); unfold raw15330step1 raw15330step0; decide +kernel
      have hl : raw15330step1Labels = raw15330step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15330step1 raw15330step1Labels = mixedMoment B raw15330step2 raw15330step2Labels := by
      have ha : raw15330step2 = raw15330step1 := by apply Matrix.ext; unfold raw15330step2 raw15330step1; decide +kernel
      have hl : raw15330step1Labels = labelEmbedding1 ∘ raw15330step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15330step1 raw15330step1Labels raw15330step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3788 node3788Labels := by rfl

def raw15331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15331step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15331step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15331step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15331step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15331 raw15331Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw15331 raw15331Labels = mixedMoment B raw15331step0 raw15331step0Labels := by
      have hz : ∀ j, raw15331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15331step0 = (fun i j => raw15331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15331step0 raw15331; decide +kernel
      have hl : raw15331step0Labels = raw15331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15331 raw15331Labels permutation346 hz
    mixedMoment B raw15331step0 raw15331step0Labels = mixedMoment B raw15331step1 raw15331step1Labels := by
      have ha : raw15331step1 = (fun i j => raw15331step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15331step1 raw15331step0; decide +kernel
      have hl : raw15331step1Labels = raw15331step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15331step0 raw15331step0Labels permutation46 permutation5
    mixedMoment B raw15331step1 raw15331step1Labels = mixedMoment B raw15331step2 raw15331step2Labels := by
      have ha : raw15331step2 = -raw15331step1 := by apply Matrix.ext; change ∀ i j, raw15331step2 i j = -(raw15331step1 i j); unfold raw15331step2 raw15331step1; decide +kernel
      have hl : raw15331step2Labels = raw15331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15331step2 raw15331step2Labels = mixedMoment B raw15331step3 raw15331step3Labels := by
      have ha : raw15331step3 = raw15331step2 := by apply Matrix.ext; unfold raw15331step3 raw15331step2; decide +kernel
      have hl : raw15331step2Labels = labelEmbedding1 ∘ raw15331step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15331step2 raw15331step2Labels raw15331step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw15332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15332step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15332step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15332step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15332step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15332step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15332 raw15332Labels = mixedMoment B node3738 node3738Labels := by
  calc
    mixedMoment B raw15332 raw15332Labels = mixedMoment B raw15332step0 raw15332step0Labels := by
      have hz : ∀ j, raw15332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15332step0 = (fun i j => raw15332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15332step0 raw15332; decide +kernel
      have hl : raw15332step0Labels = raw15332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15332 raw15332Labels permutation346 hz
    mixedMoment B raw15332step0 raw15332step0Labels = mixedMoment B raw15332step1 raw15332step1Labels := by
      have ha : raw15332step1 = (fun i j => raw15332step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15332step1 raw15332step0; decide +kernel
      have hl : raw15332step1Labels = raw15332step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15332step0 raw15332step0Labels permutation45 permutation5
    mixedMoment B raw15332step1 raw15332step1Labels = mixedMoment B raw15332step2 raw15332step2Labels := by
      have ha : raw15332step2 = -raw15332step1 := by apply Matrix.ext; change ∀ i j, raw15332step2 i j = -(raw15332step1 i j); unfold raw15332step2 raw15332step1; decide +kernel
      have hl : raw15332step2Labels = raw15332step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15332step2 raw15332step2Labels = mixedMoment B raw15332step3 raw15332step3Labels := by
      have ha : raw15332step3 = raw15332step2 := by apply Matrix.ext; unfold raw15332step3 raw15332step2; decide +kernel
      have hl : raw15332step2Labels = labelEmbedding1 ∘ raw15332step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15332step2 raw15332step2Labels raw15332step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3738 node3738Labels := by rfl

def raw15333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15333step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw15333step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15333step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15333step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15333step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15333 raw15333Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw15333 raw15333Labels = mixedMoment B raw15333step0 raw15333step0Labels := by
      have hz : ∀ j, raw15333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15333step0 = (fun i j => raw15333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15333step0 raw15333; decide +kernel
      have hl : raw15333step0Labels = raw15333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15333 raw15333Labels permutation346 hz
    mixedMoment B raw15333step0 raw15333step0Labels = mixedMoment B raw15333step1 raw15333step1Labels := by
      have ha : raw15333step1 = (fun i j => raw15333step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15333step1 raw15333step0; decide +kernel
      have hl : raw15333step1Labels = raw15333step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15333step0 raw15333step0Labels permutation48 permutation5
    mixedMoment B raw15333step1 raw15333step1Labels = mixedMoment B raw15333step2 raw15333step2Labels := by
      have ha : raw15333step2 = -raw15333step1 := by apply Matrix.ext; change ∀ i j, raw15333step2 i j = -(raw15333step1 i j); unfold raw15333step2 raw15333step1; decide +kernel
      have hl : raw15333step2Labels = raw15333step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15333step2 raw15333step2Labels = mixedMoment B raw15333step3 raw15333step3Labels := by
      have ha : raw15333step3 = raw15333step2 := by apply Matrix.ext; unfold raw15333step3 raw15333step2; decide +kernel
      have hl : raw15333step2Labels = labelEmbedding1 ∘ raw15333step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15333step2 raw15333step2Labels raw15333step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw15334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15334Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15334step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15334step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15334 raw15334Labels = mixedMoment B node2078 node2078Labels := by
  calc
    mixedMoment B raw15334 raw15334Labels = mixedMoment B raw15334step0 raw15334step0Labels := by
      have ha : raw15334step0 = (fun i j => raw15334 (permutation225 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15334step0 raw15334; decide +kernel
      have hl : raw15334step0Labels = raw15334Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15334 raw15334Labels permutation225 permutation5
    mixedMoment B raw15334step0 raw15334step0Labels = mixedMoment B raw15334step1 raw15334step1Labels := by
      have ha : raw15334step1 = -raw15334step0 := by apply Matrix.ext; change ∀ i j, raw15334step1 i j = -(raw15334step0 i j); unfold raw15334step1 raw15334step0; decide +kernel
      have hl : raw15334step1Labels = raw15334step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15334step1 raw15334step1Labels = mixedMoment B raw15334step2 raw15334step2Labels := by
      have ha : raw15334step2 = raw15334step1 := by apply Matrix.ext; unfold raw15334step2 raw15334step1; decide +kernel
      have hl : raw15334step1Labels = labelEmbedding1 ∘ raw15334step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15334step1 raw15334step1Labels raw15334step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2078 node2078Labels := by rfl

def raw15335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15335Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15335step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15335step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15335step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15335 raw15335Labels = mixedMoment B node3752 node3752Labels := by
  calc
    mixedMoment B raw15335 raw15335Labels = mixedMoment B raw15335step0 raw15335step0Labels := by
      have ha : raw15335step0 = (fun i j => raw15335 (permutation165 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15335step0 raw15335; decide +kernel
      have hl : raw15335step0Labels = raw15335Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15335 raw15335Labels permutation165 permutation5
    mixedMoment B raw15335step0 raw15335step0Labels = mixedMoment B raw15335step1 raw15335step1Labels := by
      have ha : raw15335step1 = -raw15335step0 := by apply Matrix.ext; change ∀ i j, raw15335step1 i j = -(raw15335step0 i j); unfold raw15335step1 raw15335step0; decide +kernel
      have hl : raw15335step1Labels = raw15335step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15335step1 raw15335step1Labels = mixedMoment B raw15335step2 raw15335step2Labels := by
      have ha : raw15335step2 = raw15335step1 := by apply Matrix.ext; unfold raw15335step2 raw15335step1; decide +kernel
      have hl : raw15335step1Labels = labelEmbedding1 ∘ raw15335step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15335step1 raw15335step1Labels raw15335step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3752 node3752Labels := by rfl

def raw15336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15336step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15336step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15336step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15336step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15336 raw15336Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw15336 raw15336Labels = mixedMoment B raw15336step0 raw15336step0Labels := by
      have ha : raw15336step0 = (fun i j => raw15336 (permutation226 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15336step0 raw15336; decide +kernel
      have hl : raw15336step0Labels = raw15336Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15336 raw15336Labels permutation226 permutation5
    mixedMoment B raw15336step0 raw15336step0Labels = mixedMoment B raw15336step1 raw15336step1Labels := by
      have ha : raw15336step1 = -raw15336step0 := by apply Matrix.ext; change ∀ i j, raw15336step1 i j = -(raw15336step0 i j); unfold raw15336step1 raw15336step0; decide +kernel
      have hl : raw15336step1Labels = raw15336step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15336step1 raw15336step1Labels = mixedMoment B raw15336step2 raw15336step2Labels := by
      have ha : raw15336step2 = raw15336step1 := by apply Matrix.ext; unfold raw15336step2 raw15336step1; decide +kernel
      have hl : raw15336step1Labels = labelEmbedding1 ∘ raw15336step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15336step1 raw15336step1Labels raw15336step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw15337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15337Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15337step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15337step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15337step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15337 raw15337Labels = mixedMoment B node3722 node3722Labels := by
  calc
    mixedMoment B raw15337 raw15337Labels = mixedMoment B raw15337step0 raw15337step0Labels := by
      have ha : raw15337step0 = (fun i j => raw15337 (permutation225 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15337step0 raw15337; decide +kernel
      have hl : raw15337step0Labels = raw15337Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15337 raw15337Labels permutation225 permutation5
    mixedMoment B raw15337step0 raw15337step0Labels = mixedMoment B raw15337step1 raw15337step1Labels := by
      have ha : raw15337step1 = -raw15337step0 := by apply Matrix.ext; change ∀ i j, raw15337step1 i j = -(raw15337step0 i j); unfold raw15337step1 raw15337step0; decide +kernel
      have hl : raw15337step1Labels = raw15337step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15337step1 raw15337step1Labels = mixedMoment B raw15337step2 raw15337step2Labels := by
      have ha : raw15337step2 = raw15337step1 := by apply Matrix.ext; unfold raw15337step2 raw15337step1; decide +kernel
      have hl : raw15337step1Labels = labelEmbedding1 ∘ raw15337step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15337step1 raw15337step1Labels raw15337step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3722 node3722Labels := by rfl

def raw15338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15338Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15338step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15338step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15338step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15338 raw15338Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw15338 raw15338Labels = mixedMoment B raw15338step0 raw15338step0Labels := by
      have ha : raw15338step0 = (fun i j => raw15338 (permutation228 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15338step0 raw15338; decide +kernel
      have hl : raw15338step0Labels = raw15338Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15338 raw15338Labels permutation228 permutation5
    mixedMoment B raw15338step0 raw15338step0Labels = mixedMoment B raw15338step1 raw15338step1Labels := by
      have ha : raw15338step1 = -raw15338step0 := by apply Matrix.ext; change ∀ i j, raw15338step1 i j = -(raw15338step0 i j); unfold raw15338step1 raw15338step0; decide +kernel
      have hl : raw15338step1Labels = raw15338step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15338step1 raw15338step1Labels = mixedMoment B raw15338step2 raw15338step2Labels := by
      have ha : raw15338step2 = raw15338step1 := by apply Matrix.ext; unfold raw15338step2 raw15338step1; decide +kernel
      have hl : raw15338step1Labels = labelEmbedding1 ∘ raw15338step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15338step1 raw15338step1Labels raw15338step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw15339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15339Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15339step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw15339step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15339step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15339step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15339step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15339 raw15339Labels = mixedMoment B node2080 node2080Labels := by
  calc
    mixedMoment B raw15339 raw15339Labels = mixedMoment B raw15339step0 raw15339step0Labels := by
      have hz : ∀ j, raw15339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15339step0 = (fun i j => raw15339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15339step0 raw15339; decide +kernel
      have hl : raw15339step0Labels = raw15339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15339 raw15339Labels permutation346 hz
    mixedMoment B raw15339step0 raw15339step0Labels = mixedMoment B raw15339step1 raw15339step1Labels := by
      have ha : raw15339step1 = (fun i j => raw15339step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15339step1 raw15339step0; decide +kernel
      have hl : raw15339step1Labels = raw15339step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15339step0 raw15339step0Labels permutation45 permutation5
    mixedMoment B raw15339step1 raw15339step1Labels = mixedMoment B raw15339step2 raw15339step2Labels := by
      have ha : raw15339step2 = -raw15339step1 := by apply Matrix.ext; change ∀ i j, raw15339step2 i j = -(raw15339step1 i j); unfold raw15339step2 raw15339step1; decide +kernel
      have hl : raw15339step2Labels = raw15339step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15339step2 raw15339step2Labels = mixedMoment B raw15339step3 raw15339step3Labels := by
      have ha : raw15339step3 = raw15339step2 := by apply Matrix.ext; unfold raw15339step3 raw15339step2; decide +kernel
      have hl : raw15339step2Labels = labelEmbedding1 ∘ raw15339step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15339step2 raw15339step2Labels raw15339step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2080 node2080Labels := by rfl

def raw15340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15340Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15340step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15340step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15340 raw15340Labels = mixedMoment B node2876 node2876Labels := by
  calc
    mixedMoment B raw15340 raw15340Labels = mixedMoment B raw15340step0 raw15340step0Labels := by
      have hz : ∀ j, raw15340 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15340step0 = (fun i j => raw15340 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15340step0 raw15340; decide +kernel
      have hl : raw15340step0Labels = raw15340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15340 raw15340Labels permutation346 hz
    mixedMoment B raw15340step0 raw15340step0Labels = mixedMoment B raw15340step1 raw15340step1Labels := by
      have ha : raw15340step1 = (fun i j => raw15340step0 (permutation103 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15340step1 raw15340step0; decide +kernel
      have hl : raw15340step1Labels = raw15340step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15340step0 raw15340step0Labels permutation103 permutation5
    mixedMoment B raw15340step1 raw15340step1Labels = mixedMoment B raw15340step2 raw15340step2Labels := by
      have ha : raw15340step2 = raw15340step1 := by apply Matrix.ext; unfold raw15340step2 raw15340step1; decide +kernel
      have hl : raw15340step1Labels = labelEmbedding1 ∘ raw15340step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15340step1 raw15340step1Labels raw15340step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2876 node2876Labels := by rfl

def raw15341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15341Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15341step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15341 raw15341Labels = mixedMoment B node2860 node2860Labels := by
  calc
    mixedMoment B raw15341 raw15341Labels = mixedMoment B raw15341step0 raw15341step0Labels := by
      have ha : raw15341step0 = (fun i j => raw15341 (permutation511 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15341step0 raw15341; decide +kernel
      have hl : raw15341step0Labels = raw15341Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15341 raw15341Labels permutation511 permutation5
    mixedMoment B raw15341step0 raw15341step0Labels = mixedMoment B raw15341step1 raw15341step1Labels := by
      have ha : raw15341step1 = raw15341step0 := by apply Matrix.ext; unfold raw15341step1 raw15341step0; decide +kernel
      have hl : raw15341step0Labels = labelEmbedding1 ∘ raw15341step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15341step0 raw15341step0Labels raw15341step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2860 node2860Labels := by rfl

def raw15342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15342Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw15342step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15342step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15342 raw15342Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw15342 raw15342Labels = mixedMoment B raw15342step0 raw15342step0Labels := by
      have hz : ∀ j, raw15342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15342step0 = (fun i j => raw15342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15342step0 raw15342; decide +kernel
      have hl : raw15342step0Labels = raw15342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15342 raw15342Labels permutation346 hz
    mixedMoment B raw15342step0 raw15342step0Labels = mixedMoment B raw15342step1 raw15342step1Labels := by
      have ha : raw15342step1 = (fun i j => raw15342step0 (permutation101 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15342step1 raw15342step0; decide +kernel
      have hl : raw15342step1Labels = raw15342step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15342step0 raw15342step0Labels permutation101 permutation5
    mixedMoment B raw15342step1 raw15342step1Labels = mixedMoment B raw15342step2 raw15342step2Labels := by
      have ha : raw15342step2 = raw15342step1 := by apply Matrix.ext; unfold raw15342step2 raw15342step1; decide +kernel
      have hl : raw15342step1Labels = labelEmbedding1 ∘ raw15342step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15342step1 raw15342step1Labels raw15342step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2867 node2867Labels := by rfl

def raw15343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15343Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw15343step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15343step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15343step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15343 raw15343Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw15343 raw15343Labels = mixedMoment B raw15343step0 raw15343step0Labels := by
      have hz : ∀ j, raw15343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15343step0 = (fun i j => raw15343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15343step0 raw15343; decide +kernel
      have hl : raw15343step0Labels = raw15343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15343 raw15343Labels permutation346 hz
    mixedMoment B raw15343step0 raw15343step0Labels = mixedMoment B raw15343step1 raw15343step1Labels := by
      have ha : raw15343step1 = (fun i j => raw15343step0 (permutation101 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15343step1 raw15343step0; decide +kernel
      have hl : raw15343step1Labels = raw15343step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15343step0 raw15343step0Labels permutation101 permutation5
    mixedMoment B raw15343step1 raw15343step1Labels = mixedMoment B raw15343step2 raw15343step2Labels := by
      have ha : raw15343step2 = raw15343step1 := by apply Matrix.ext; unfold raw15343step2 raw15343step1; decide +kernel
      have hl : raw15343step1Labels = labelEmbedding1 ∘ raw15343step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15343step1 raw15343step1Labels raw15343step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw15344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15344Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15344step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw15344step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15344step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15344step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15344step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15344step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15344 raw15344Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw15344 raw15344Labels = mixedMoment B raw15344step0 raw15344step0Labels := by
      have hz : ∀ j, raw15344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15344step0 = (fun i j => raw15344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15344step0 raw15344; decide +kernel
      have hl : raw15344step0Labels = raw15344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15344 raw15344Labels permutation346 hz
    mixedMoment B raw15344step0 raw15344step0Labels = mixedMoment B raw15344step1 raw15344step1Labels := by
      have ha : raw15344step1 = (fun i j => raw15344step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15344step1 raw15344step0; decide +kernel
      have hl : raw15344step1Labels = raw15344step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15344step0 raw15344step0Labels permutation35 permutation5
    mixedMoment B raw15344step1 raw15344step1Labels = mixedMoment B raw15344step2 raw15344step2Labels := by
      have ha : raw15344step2 = -raw15344step1 := by apply Matrix.ext; change ∀ i j, raw15344step2 i j = -(raw15344step1 i j); unfold raw15344step2 raw15344step1; decide +kernel
      have hl : raw15344step2Labels = raw15344step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15344step2 raw15344step2Labels = mixedMoment B raw15344step3 raw15344step3Labels := by
      have ha : raw15344step3 = raw15344step2 := by apply Matrix.ext; unfold raw15344step3 raw15344step2; decide +kernel
      have hl : raw15344step2Labels = labelEmbedding1 ∘ raw15344step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15344step2 raw15344step2Labels raw15344step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw15345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15345Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15345step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw15345step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15345step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15345step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15345step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15345 raw15345Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw15345 raw15345Labels = mixedMoment B raw15345step0 raw15345step0Labels := by
      have hz : ∀ j, raw15345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15345step0 = (fun i j => raw15345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15345step0 raw15345; decide +kernel
      have hl : raw15345step0Labels = raw15345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15345 raw15345Labels permutation346 hz
    mixedMoment B raw15345step0 raw15345step0Labels = mixedMoment B raw15345step1 raw15345step1Labels := by
      have ha : raw15345step1 = (fun i j => raw15345step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15345step1 raw15345step0; decide +kernel
      have hl : raw15345step1Labels = raw15345step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15345step0 raw15345step0Labels permutation35 permutation5
    mixedMoment B raw15345step1 raw15345step1Labels = mixedMoment B raw15345step2 raw15345step2Labels := by
      have ha : raw15345step2 = -raw15345step1 := by apply Matrix.ext; change ∀ i j, raw15345step2 i j = -(raw15345step1 i j); unfold raw15345step2 raw15345step1; decide +kernel
      have hl : raw15345step2Labels = raw15345step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15345step2 raw15345step2Labels = mixedMoment B raw15345step3 raw15345step3Labels := by
      have ha : raw15345step3 = raw15345step2 := by apply Matrix.ext; unfold raw15345step3 raw15345step2; decide +kernel
      have hl : raw15345step2Labels = labelEmbedding1 ∘ raw15345step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15345step2 raw15345step2Labels raw15345step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3772 node3772Labels := by rfl

def raw15346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15346Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15346step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15346 raw15346Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw15346 raw15346Labels = mixedMoment B raw15346step0 raw15346step0Labels := by
      have ha : raw15346step0 = (fun i j => raw15346 (permutation580 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15346step0 raw15346; decide +kernel
      have hl : raw15346step0Labels = raw15346Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15346 raw15346Labels permutation580 permutation7
    mixedMoment B raw15346step0 raw15346step0Labels = mixedMoment B raw15346step1 raw15346step1Labels := by
      have ha : raw15346step1 = raw15346step0 := by apply Matrix.ext; unfold raw15346step1 raw15346step0; decide +kernel
      have hl : raw15346step0Labels = labelEmbedding1 ∘ raw15346step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15346step0 raw15346step0Labels raw15346step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw15347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15347Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15347step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15347step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw15347step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15347 raw15347Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw15347 raw15347Labels = mixedMoment B raw15347step0 raw15347step0Labels := by
      have hz : ∀ j, raw15347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15347step0 = (fun i j => raw15347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15347step0 raw15347; decide +kernel
      have hl : raw15347step0Labels = raw15347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15347 raw15347Labels permutation346 hz
    mixedMoment B raw15347step0 raw15347step0Labels = mixedMoment B raw15347step1 raw15347step1Labels := by
      have ha : raw15347step1 = (fun i j => raw15347step0 (permutation122 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15347step1 raw15347step0; decide +kernel
      have hl : raw15347step1Labels = raw15347step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15347step0 raw15347step0Labels permutation122 permutation7
    mixedMoment B raw15347step1 raw15347step1Labels = mixedMoment B raw15347step2 raw15347step2Labels := by
      have ha : raw15347step2 = raw15347step1 := by apply Matrix.ext; unfold raw15347step2 raw15347step1; decide +kernel
      have hl : raw15347step1Labels = labelEmbedding1 ∘ raw15347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15347step1 raw15347step1Labels raw15347step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3771 node3771Labels := by rfl

def raw15348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15348Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw15348step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15348step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15348step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15348 raw15348Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw15348 raw15348Labels = mixedMoment B raw15348step0 raw15348step0Labels := by
      have hz : ∀ j, raw15348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15348step0 = (fun i j => raw15348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15348step0 raw15348; decide +kernel
      have hl : raw15348step0Labels = raw15348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15348 raw15348Labels permutation346 hz
    mixedMoment B raw15348step0 raw15348step0Labels = mixedMoment B raw15348step1 raw15348step1Labels := by
      have ha : raw15348step1 = (fun i j => raw15348step0 (permutation122 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15348step1 raw15348step0; decide +kernel
      have hl : raw15348step1Labels = raw15348step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15348step0 raw15348step0Labels permutation122 permutation7
    mixedMoment B raw15348step1 raw15348step1Labels = mixedMoment B raw15348step2 raw15348step2Labels := by
      have ha : raw15348step2 = raw15348step1 := by apply Matrix.ext; unfold raw15348step2 raw15348step1; decide +kernel
      have hl : raw15348step1Labels = labelEmbedding1 ∘ raw15348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15348step1 raw15348step1Labels raw15348step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw15349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15349Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15349step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw15349step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw15349step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15349step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw15349step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15349 raw15349Labels = mixedMoment B node2081 node2081Labels := by
  calc
    mixedMoment B raw15349 raw15349Labels = mixedMoment B raw15349step0 raw15349step0Labels := by
      have hz : ∀ j, raw15349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15349step0 = (fun i j => raw15349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15349step0 raw15349; decide +kernel
      have hl : raw15349step0Labels = raw15349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15349 raw15349Labels permutation346 hz
    mixedMoment B raw15349step0 raw15349step0Labels = mixedMoment B raw15349step1 raw15349step1Labels := by
      have ha : raw15349step1 = (fun i j => raw15349step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15349step1 raw15349step0; decide +kernel
      have hl : raw15349step1Labels = raw15349step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15349step0 raw15349step0Labels permutation44 permutation5
    mixedMoment B raw15349step1 raw15349step1Labels = mixedMoment B raw15349step2 raw15349step2Labels := by
      have ha : raw15349step2 = -raw15349step1 := by apply Matrix.ext; change ∀ i j, raw15349step2 i j = -(raw15349step1 i j); unfold raw15349step2 raw15349step1; decide +kernel
      have hl : raw15349step2Labels = raw15349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15349step2 raw15349step2Labels = mixedMoment B raw15349step3 raw15349step3Labels := by
      have ha : raw15349step3 = raw15349step2 := by apply Matrix.ext; unfold raw15349step3 raw15349step2; decide +kernel
      have hl : raw15349step2Labels = labelEmbedding1 ∘ raw15349step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15349step2 raw15349step2Labels raw15349step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2081 node2081Labels := by rfl

def raw15350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15350Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15350step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15350step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15350 raw15350Labels = mixedMoment B node3386 node3386Labels := by
  calc
    mixedMoment B raw15350 raw15350Labels = mixedMoment B raw15350step0 raw15350step0Labels := by
      have hz : ∀ j, raw15350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15350step0 = (fun i j => raw15350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15350step0 raw15350; decide +kernel
      have hl : raw15350step0Labels = raw15350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15350 raw15350Labels permutation346 hz
    mixedMoment B raw15350step0 raw15350step0Labels = mixedMoment B raw15350step1 raw15350step1Labels := by
      have ha : raw15350step1 = (fun i j => raw15350step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15350step1 raw15350step0; decide +kernel
      have hl : raw15350step1Labels = raw15350step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15350step0 raw15350step0Labels permutation145 permutation5
    mixedMoment B raw15350step1 raw15350step1Labels = mixedMoment B raw15350step2 raw15350step2Labels := by
      have ha : raw15350step2 = raw15350step1 := by apply Matrix.ext; unfold raw15350step2 raw15350step1; decide +kernel
      have hl : raw15350step1Labels = labelEmbedding1 ∘ raw15350step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15350step1 raw15350step1Labels raw15350step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3386 node3386Labels := by rfl

def raw15351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15351Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15351step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15351 raw15351Labels = mixedMoment B node3374 node3374Labels := by
  calc
    mixedMoment B raw15351 raw15351Labels = mixedMoment B raw15351step0 raw15351step0Labels := by
      have ha : raw15351step0 = (fun i j => raw15351 (permutation654 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15351step0 raw15351; decide +kernel
      have hl : raw15351step0Labels = raw15351Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15351 raw15351Labels permutation654 permutation5
    mixedMoment B raw15351step0 raw15351step0Labels = mixedMoment B raw15351step1 raw15351step1Labels := by
      have ha : raw15351step1 = raw15351step0 := by apply Matrix.ext; unfold raw15351step1 raw15351step0; decide +kernel
      have hl : raw15351step0Labels = labelEmbedding1 ∘ raw15351step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15351step0 raw15351step0Labels raw15351step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3374 node3374Labels := by rfl

def raw15352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15352step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15352step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15352 raw15352Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw15352 raw15352Labels = mixedMoment B raw15352step0 raw15352step0Labels := by
      have hz : ∀ j, raw15352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15352step0 = (fun i j => raw15352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15352step0 raw15352; decide +kernel
      have hl : raw15352step0Labels = raw15352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15352 raw15352Labels permutation346 hz
    mixedMoment B raw15352step0 raw15352step0Labels = mixedMoment B raw15352step1 raw15352step1Labels := by
      have ha : raw15352step1 = (fun i j => raw15352step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15352step1 raw15352step0; decide +kernel
      have hl : raw15352step1Labels = raw15352step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15352step0 raw15352step0Labels permutation143 permutation5
    mixedMoment B raw15352step1 raw15352step1Labels = mixedMoment B raw15352step2 raw15352step2Labels := by
      have ha : raw15352step2 = raw15352step1 := by apply Matrix.ext; unfold raw15352step2 raw15352step1; decide +kernel
      have hl : raw15352step1Labels = labelEmbedding1 ∘ raw15352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15352step1 raw15352step1Labels raw15352step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw15353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15353Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw15353step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15353step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15353 raw15353Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw15353 raw15353Labels = mixedMoment B raw15353step0 raw15353step0Labels := by
      have hz : ∀ j, raw15353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15353step0 = (fun i j => raw15353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15353step0 raw15353; decide +kernel
      have hl : raw15353step0Labels = raw15353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15353 raw15353Labels permutation346 hz
    mixedMoment B raw15353step0 raw15353step0Labels = mixedMoment B raw15353step1 raw15353step1Labels := by
      have ha : raw15353step1 = (fun i j => raw15353step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15353step1 raw15353step0; decide +kernel
      have hl : raw15353step1Labels = raw15353step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15353step0 raw15353step0Labels permutation143 permutation5
    mixedMoment B raw15353step1 raw15353step1Labels = mixedMoment B raw15353step2 raw15353step2Labels := by
      have ha : raw15353step2 = raw15353step1 := by apply Matrix.ext; unfold raw15353step2 raw15353step1; decide +kernel
      have hl : raw15353step1Labels = labelEmbedding1 ∘ raw15353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15353step1 raw15353step1Labels raw15353step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3379 node3379Labels := by rfl

def raw15354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15354 raw15354Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw15354 raw15354Labels = mixedMoment B raw15354step0 raw15354step0Labels := by
      have hz : ∀ j, raw15354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15354step0 = (fun i j => raw15354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15354step0 raw15354; decide +kernel
      have hl : raw15354step0Labels = raw15354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15354 raw15354Labels permutation346 hz
    mixedMoment B raw15354step0 raw15354step0Labels = mixedMoment B raw15354step1 raw15354step1Labels := by
      have ha : raw15354step1 = (fun i j => raw15354step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15354step1 raw15354step0; decide +kernel
      have hl : raw15354step1Labels = raw15354step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15354step0 raw15354step0Labels permutation101 permutation4
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw15355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15355 raw15355Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw15355 raw15355Labels = mixedMoment B raw15355step0 raw15355step0Labels := by
      have hz : ∀ j, raw15355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15355step0 = (fun i j => raw15355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15355step0 raw15355; decide +kernel
      have hl : raw15355step0Labels = raw15355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15355 raw15355Labels permutation346 hz
    mixedMoment B raw15355step0 raw15355step0Labels = mixedMoment B raw15355step1 raw15355step1Labels := by
      have ha : raw15355step1 = (fun i j => raw15355step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15355step1 raw15355step0; decide +kernel
      have hl : raw15355step1Labels = raw15355step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15355step0 raw15355step0Labels permutation48 permutation4
    mixedMoment B raw15355step1 raw15355step1Labels = mixedMoment B raw15355step2 raw15355step2Labels := by
      have ha : raw15355step2 = -raw15355step1 := by apply Matrix.ext; change ∀ i j, raw15355step2 i j = -(raw15355step1 i j); unfold raw15355step2 raw15355step1; decide +kernel
      have hl : raw15355step2Labels = raw15355step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw15356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw15356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15356 raw15356Labels = mixedMoment B node3175 node3175Labels := by
  calc
    mixedMoment B raw15356 raw15356Labels = mixedMoment B raw15356step0 raw15356step0Labels := by
      have ha : raw15356step0 = (fun i j => raw15356 (permutation228 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15356step0 raw15356; decide +kernel
      have hl : raw15356step0Labels = raw15356Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15356 raw15356Labels permutation228 permutation4
    mixedMoment B raw15356step0 raw15356step0Labels = mixedMoment B raw15356step1 raw15356step1Labels := by
      have ha : raw15356step1 = -raw15356step0 := by apply Matrix.ext; change ∀ i j, raw15356step1 i j = -(raw15356step0 i j); unfold raw15356step1 raw15356step0; decide +kernel
      have hl : raw15356step1Labels = raw15356step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3175 node3175Labels := by rfl

def raw15357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw15357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw15357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15357 raw15357Labels = mixedMoment B node2619 node2619Labels := by
  calc
    mixedMoment B raw15357 raw15357Labels = mixedMoment B raw15357step0 raw15357step0Labels := by
      have hz : ∀ j, raw15357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15357step0 = (fun i j => raw15357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15357step0 raw15357; decide +kernel
      have hl : raw15357step0Labels = raw15357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15357 raw15357Labels permutation346 hz
    mixedMoment B raw15357step0 raw15357step0Labels = mixedMoment B raw15357step1 raw15357step1Labels := by
      have ha : raw15357step1 = (fun i j => raw15357step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15357step1 raw15357step0; decide +kernel
      have hl : raw15357step1Labels = raw15357step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15357step0 raw15357step0Labels permutation101 permutation4
    _ = mixedMoment B node2619 node2619Labels := by rfl

def raw15358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw15358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw15358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15358 raw15358Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw15358 raw15358Labels = mixedMoment B raw15358step0 raw15358step0Labels := by
      have hz : ∀ j, raw15358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15358step0 = (fun i j => raw15358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15358step0 raw15358; decide +kernel
      have hl : raw15358step0Labels = raw15358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15358 raw15358Labels permutation346 hz
    mixedMoment B raw15358step0 raw15358step0Labels = mixedMoment B raw15358step1 raw15358step1Labels := by
      have ha : raw15358step1 = (fun i j => raw15358step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15358step1 raw15358step0; decide +kernel
      have hl : raw15358step1Labels = raw15358step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15358step0 raw15358step0Labels permutation33 permutation2
    _ = mixedMoment B node3198 node3198Labels := by rfl

def raw15359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw15359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw15359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15359step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw15359step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15359 raw15359Labels = mixedMoment B node2872 node2872Labels := by
  calc
    mixedMoment B raw15359 raw15359Labels = mixedMoment B raw15359step0 raw15359step0Labels := by
      have hz : ∀ j, raw15359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15359step0 = (fun i j => raw15359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15359step0 raw15359; decide +kernel
      have hl : raw15359step0Labels = raw15359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15359 raw15359Labels permutation346 hz
    mixedMoment B raw15359step0 raw15359step0Labels = mixedMoment B raw15359step1 raw15359step1Labels := by
      have ha : raw15359step1 = (fun i j => raw15359step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15359step1 raw15359step0; decide +kernel
      have hl : raw15359step1Labels = raw15359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15359step0 raw15359step0Labels permutation151 permutation2
    mixedMoment B raw15359step1 raw15359step1Labels = mixedMoment B raw15359step2 raw15359step2Labels := by
      have ha : raw15359step2 = -raw15359step1 := by apply Matrix.ext; change ∀ i j, raw15359step2 i j = -(raw15359step1 i j); unfold raw15359step2 raw15359step1; decide +kernel
      have hl : raw15359step2Labels = raw15359step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2872 node2872Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
