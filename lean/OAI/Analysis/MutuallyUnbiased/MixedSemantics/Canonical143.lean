import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18304 raw18304Labels = mixedMoment B node5415 node5415Labels := by
  calc
    _ = mixedMoment B node5415 node5415Labels := by rfl

def raw18305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18305 raw18305Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw18305 raw18305Labels = mixedMoment B raw18305step0 raw18305step0Labels := by
      have hz : ∀ j, raw18305 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18305step0 = (fun i j => raw18305 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18305step0 raw18305; decide +kernel
      have hl : raw18305step0Labels = raw18305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18305 raw18305Labels permutation520 hz
    mixedMoment B raw18305step0 raw18305step0Labels = mixedMoment B raw18305step1 raw18305step1Labels := by
      have hz : ∀ j, raw18305step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18305step1 = (fun i j => raw18305step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18305step1 raw18305step0; decide +kernel
      have hl : raw18305step1Labels = raw18305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18305step0 raw18305step0Labels permutation80 hz
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw18306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18306step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18306 raw18306Labels = mixedMoment B node5389 node5389Labels := by
  calc
    mixedMoment B raw18306 raw18306Labels = mixedMoment B raw18306step0 raw18306step0Labels := by
      have hz : ∀ j, raw18306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18306step0 = (fun i j => raw18306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18306step0 raw18306; decide +kernel
      have hl : raw18306step0Labels = raw18306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18306 raw18306Labels permutation434 hz
    mixedMoment B raw18306step0 raw18306step0Labels = mixedMoment B raw18306step1 raw18306step1Labels := by
      have hz : ∀ j, raw18306step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18306step1 = (fun i j => raw18306step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18306step1 raw18306step0; decide +kernel
      have hl : raw18306step1Labels = raw18306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18306step0 raw18306step0Labels permutation80 hz
    _ = mixedMoment B node5389 node5389Labels := by rfl

def raw18307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18307step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18307 raw18307Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw18307 raw18307Labels = mixedMoment B raw18307step0 raw18307step0Labels := by
      have hz : ∀ j, raw18307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18307step0 = (fun i j => raw18307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18307step0 raw18307; decide +kernel
      have hl : raw18307step0Labels = raw18307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18307 raw18307Labels permutation434 hz
    mixedMoment B raw18307step0 raw18307step0Labels = mixedMoment B raw18307step1 raw18307step1Labels := by
      have ha : raw18307step1 = (fun i j => raw18307step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18307step1 raw18307step0; decide +kernel
      have hl : raw18307step1Labels = raw18307step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18307step0 raw18307step0Labels permutation149 permutation2
    mixedMoment B raw18307step1 raw18307step1Labels = mixedMoment B raw18307step2 raw18307step2Labels := by
      have ha : raw18307step2 = -raw18307step1 := by apply Matrix.ext; change ∀ i j, raw18307step2 i j = -(raw18307step1 i j); unfold raw18307step2 raw18307step1; decide +kernel
      have hl : raw18307step2Labels = raw18307step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw18308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18308step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18308 raw18308Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw18308 raw18308Labels = mixedMoment B raw18308step0 raw18308step0Labels := by
      have hz : ∀ j, raw18308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18308step0 = (fun i j => raw18308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18308step0 raw18308; decide +kernel
      have hl : raw18308step0Labels = raw18308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18308 raw18308Labels permutation346 hz
    mixedMoment B raw18308step0 raw18308step0Labels = mixedMoment B raw18308step1 raw18308step1Labels := by
      have ha : raw18308step1 = (fun i j => raw18308step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18308step1 raw18308step0; decide +kernel
      have hl : raw18308step1Labels = raw18308step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18308step0 raw18308step0Labels permutation149 permutation2
    mixedMoment B raw18308step1 raw18308step1Labels = mixedMoment B raw18308step2 raw18308step2Labels := by
      have ha : raw18308step2 = -raw18308step1 := by apply Matrix.ext; change ∀ i j, raw18308step2 i j = -(raw18308step1 i j); unfold raw18308step2 raw18308step1; decide +kernel
      have hl : raw18308step2Labels = raw18308step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw18309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18309step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18309step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18309 raw18309Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw18309 raw18309Labels = mixedMoment B raw18309step0 raw18309step0Labels := by
      have hz : ∀ j, raw18309 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18309step0 = (fun i j => raw18309 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18309step0 raw18309; decide +kernel
      have hl : raw18309step0Labels = raw18309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18309 raw18309Labels permutation434 hz
    mixedMoment B raw18309step0 raw18309step0Labels = mixedMoment B raw18309step1 raw18309step1Labels := by
      have hz : ∀ j, raw18309step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18309step1 = (fun i j => raw18309step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18309step1 raw18309step0; decide +kernel
      have hl : raw18309step1Labels = raw18309step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18309step0 raw18309step0Labels permutation80 hz
    mixedMoment B raw18309step1 raw18309step1Labels = mixedMoment B raw18309step2 raw18309step2Labels := by
      have ha : raw18309step2 = (fun i j => raw18309step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18309step2 raw18309step1; decide +kernel
      have hl : raw18309step2Labels = raw18309step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18309step1 raw18309step1Labels permutation9 permutation2
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw18310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw18310step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18310step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18310 raw18310Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw18310 raw18310Labels = mixedMoment B raw18310step0 raw18310step0Labels := by
      have hz : ∀ j, raw18310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18310step0 = (fun i j => raw18310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18310step0 raw18310; decide +kernel
      have hl : raw18310step0Labels = raw18310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18310 raw18310Labels permutation434 hz
    mixedMoment B raw18310step0 raw18310step0Labels = mixedMoment B raw18310step1 raw18310step1Labels := by
      have hz : ∀ j, raw18310step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18310step1 = (fun i j => raw18310step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18310step1 raw18310step0; decide +kernel
      have hl : raw18310step1Labels = raw18310step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18310step0 raw18310step0Labels permutation80 hz
    mixedMoment B raw18310step1 raw18310step1Labels = mixedMoment B raw18310step2 raw18310step2Labels := by
      have ha : raw18310step2 = (fun i j => raw18310step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18310step2 raw18310step1; decide +kernel
      have hl : raw18310step2Labels = raw18310step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18310step1 raw18310step1Labels permutation31 permutation2
    mixedMoment B raw18310step2 raw18310step2Labels = mixedMoment B raw18310step3 raw18310step3Labels := by
      have ha : raw18310step3 = -raw18310step2 := by apply Matrix.ext; change ∀ i j, raw18310step3 i j = -(raw18310step2 i j); unfold raw18310step3 raw18310step2; decide +kernel
      have hl : raw18310step3Labels = raw18310step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw18311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18311step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18311step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18311 raw18311Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw18311 raw18311Labels = mixedMoment B raw18311step0 raw18311step0Labels := by
      have hz : ∀ j, raw18311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18311step0 = (fun i j => raw18311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18311step0 raw18311; decide +kernel
      have hl : raw18311step0Labels = raw18311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18311 raw18311Labels permutation434 hz
    mixedMoment B raw18311step0 raw18311step0Labels = mixedMoment B raw18311step1 raw18311step1Labels := by
      have ha : raw18311step1 = (fun i j => raw18311step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18311step1 raw18311step0; decide +kernel
      have hl : raw18311step1Labels = raw18311step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18311step0 raw18311step0Labels permutation149 permutation2
    mixedMoment B raw18311step1 raw18311step1Labels = mixedMoment B raw18311step2 raw18311step2Labels := by
      have ha : raw18311step2 = -raw18311step1 := by apply Matrix.ext; change ∀ i j, raw18311step2 i j = -(raw18311step1 i j); unfold raw18311step2 raw18311step1; decide +kernel
      have hl : raw18311step2Labels = raw18311step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw18312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18312step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18312 raw18312Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw18312 raw18312Labels = mixedMoment B raw18312step0 raw18312step0Labels := by
      have hz : ∀ j, raw18312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18312step0 = (fun i j => raw18312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18312step0 raw18312; decide +kernel
      have hl : raw18312step0Labels = raw18312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18312 raw18312Labels permutation346 hz
    mixedMoment B raw18312step0 raw18312step0Labels = mixedMoment B raw18312step1 raw18312step1Labels := by
      have ha : raw18312step1 = (fun i j => raw18312step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18312step1 raw18312step0; decide +kernel
      have hl : raw18312step1Labels = raw18312step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18312step0 raw18312step0Labels permutation149 permutation2
    mixedMoment B raw18312step1 raw18312step1Labels = mixedMoment B raw18312step2 raw18312step2Labels := by
      have ha : raw18312step2 = -raw18312step1 := by apply Matrix.ext; change ∀ i j, raw18312step2 i j = -(raw18312step1 i j); unfold raw18312step2 raw18312step1; decide +kernel
      have hl : raw18312step2Labels = raw18312step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw18313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18313step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18313 raw18313Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18313 raw18313Labels = mixedMoment B raw18313step0 raw18313step0Labels := by
      have hz : ∀ j, raw18313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18313step0 = (fun i j => raw18313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18313step0 raw18313; decide +kernel
      have hl : raw18313step0Labels = raw18313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18313 raw18313Labels permutation346 hz
    mixedMoment B raw18313step0 raw18313step0Labels = mixedMoment B raw18313step1 raw18313step1Labels := by
      have ha : raw18313step1 = (fun i j => raw18313step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18313step1 raw18313step0; decide +kernel
      have hl : raw18313step1Labels = raw18313step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18313step0 raw18313step0Labels permutation150 permutation2
    mixedMoment B raw18313step1 raw18313step1Labels = mixedMoment B raw18313step2 raw18313step2Labels := by
      have ha : raw18313step2 = -raw18313step1 := by apply Matrix.ext; change ∀ i j, raw18313step2 i j = -(raw18313step1 i j); unfold raw18313step2 raw18313step1; decide +kernel
      have hl : raw18313step2Labels = raw18313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw18314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18314step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18314step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18314 raw18314Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw18314 raw18314Labels = mixedMoment B raw18314step0 raw18314step0Labels := by
      have ha : raw18314step0 = (fun i j => raw18314 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18314step0 raw18314; decide +kernel
      have hl : raw18314step0Labels = raw18314Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18314 raw18314Labels permutation674 permutation7
    mixedMoment B raw18314step0 raw18314step0Labels = mixedMoment B raw18314step1 raw18314step1Labels := by
      have ha : raw18314step1 = raw18314step0 := by apply Matrix.ext; unfold raw18314step1 raw18314step0; decide +kernel
      have hl : raw18314step0Labels = labelEmbedding10 ∘ raw18314step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18314step0 raw18314step0Labels raw18314step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw18315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18315step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18315step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18315 raw18315Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw18315 raw18315Labels = mixedMoment B raw18315step0 raw18315step0Labels := by
      have hz : ∀ j, raw18315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18315step0 = (fun i j => raw18315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18315step0 raw18315; decide +kernel
      have hl : raw18315step0Labels = raw18315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18315 raw18315Labels permutation346 hz
    mixedMoment B raw18315step0 raw18315step0Labels = mixedMoment B raw18315step1 raw18315step1Labels := by
      have ha : raw18315step1 = (fun i j => raw18315step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18315step1 raw18315step0; decide +kernel
      have hl : raw18315step1Labels = raw18315step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18315step0 raw18315step0Labels permutation149 permutation7
    mixedMoment B raw18315step1 raw18315step1Labels = mixedMoment B raw18315step2 raw18315step2Labels := by
      have ha : raw18315step2 = raw18315step1 := by apply Matrix.ext; unfold raw18315step2 raw18315step1; decide +kernel
      have hl : raw18315step1Labels = labelEmbedding10 ∘ raw18315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18315step1 raw18315step1Labels raw18315step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw18316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18316step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18316step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18316 raw18316Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18316 raw18316Labels = mixedMoment B raw18316step0 raw18316step0Labels := by
      have hz : ∀ j, raw18316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18316step0 = (fun i j => raw18316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18316step0 raw18316; decide +kernel
      have hl : raw18316step0Labels = raw18316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18316 raw18316Labels permutation346 hz
    mixedMoment B raw18316step0 raw18316step0Labels = mixedMoment B raw18316step1 raw18316step1Labels := by
      have ha : raw18316step1 = (fun i j => raw18316step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18316step1 raw18316step0; decide +kernel
      have hl : raw18316step1Labels = raw18316step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18316step0 raw18316step0Labels permutation149 permutation7
    mixedMoment B raw18316step1 raw18316step1Labels = mixedMoment B raw18316step2 raw18316step2Labels := by
      have ha : raw18316step2 = raw18316step1 := by apply Matrix.ext; unfold raw18316step2 raw18316step1; decide +kernel
      have hl : raw18316step1Labels = labelEmbedding10 ∘ raw18316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18316step1 raw18316step1Labels raw18316step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw18317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18317step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18317step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18317step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18317 raw18317Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw18317 raw18317Labels = mixedMoment B raw18317step0 raw18317step0Labels := by
      have hz : ∀ j, raw18317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18317step0 = (fun i j => raw18317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18317step0 raw18317; decide +kernel
      have hl : raw18317step0Labels = raw18317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18317 raw18317Labels permutation346 hz
    mixedMoment B raw18317step0 raw18317step0Labels = mixedMoment B raw18317step1 raw18317step1Labels := by
      have ha : raw18317step1 = (fun i j => raw18317step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18317step1 raw18317step0; decide +kernel
      have hl : raw18317step1Labels = raw18317step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18317step0 raw18317step0Labels permutation38 permutation6
    mixedMoment B raw18317step1 raw18317step1Labels = mixedMoment B raw18317step2 raw18317step2Labels := by
      have ha : raw18317step2 = -raw18317step1 := by apply Matrix.ext; change ∀ i j, raw18317step2 i j = -(raw18317step1 i j); unfold raw18317step2 raw18317step1; decide +kernel
      have hl : raw18317step2Labels = raw18317step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18317step2 raw18317step2Labels = mixedMoment B raw18317step3 raw18317step3Labels := by
      have ha : raw18317step3 = raw18317step2 := by apply Matrix.ext; unfold raw18317step3 raw18317step2; decide +kernel
      have hl : raw18317step2Labels = labelEmbedding9 ∘ raw18317step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18317step2 raw18317step2Labels raw18317step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw18318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18318step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18318 raw18318Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw18318 raw18318Labels = mixedMoment B raw18318step0 raw18318step0Labels := by
      have hz : ∀ j, raw18318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18318step0 = (fun i j => raw18318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18318step0 raw18318; decide +kernel
      have hl : raw18318step0Labels = raw18318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18318 raw18318Labels permutation346 hz
    mixedMoment B raw18318step0 raw18318step0Labels = mixedMoment B raw18318step1 raw18318step1Labels := by
      have hz : ∀ j, raw18318step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw18318step1 = (fun i j => raw18318step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw18318step1 raw18318step0; decide +kernel
      have hl : raw18318step1Labels = raw18318step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18318step0 raw18318step0Labels permutation56 hz
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw18319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18319 raw18319Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18319 raw18319Labels = mixedMoment B raw18319step0 raw18319step0Labels := by
      have ha : raw18319step0 = (fun i j => raw18319 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18319step0 raw18319; decide +kernel
      have hl : raw18319step0Labels = raw18319Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18319 raw18319Labels permutation158 permutation2
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw18320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18320 raw18320Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw18320 raw18320Labels = mixedMoment B raw18320step0 raw18320step0Labels := by
      have ha : raw18320step0 = (fun i j => raw18320 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18320step0 raw18320; decide +kernel
      have hl : raw18320step0Labels = raw18320Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18320 raw18320Labels permutation200 permutation2
    _ = mixedMoment B node5394 node5394Labels := by rfl

def raw18321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18321 raw18321Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw18321 raw18321Labels = mixedMoment B raw18321step0 raw18321step0Labels := by
      have ha : raw18321step0 = (fun i j => raw18321 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18321step0 raw18321; decide +kernel
      have hl : raw18321step0Labels = raw18321Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18321 raw18321Labels permutation160 permutation2
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw18322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18322step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18322step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18322step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18322step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18322 raw18322Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18322 raw18322Labels = mixedMoment B raw18322step0 raw18322step0Labels := by
      have ha : raw18322step0 = (fun i j => raw18322 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18322step0 raw18322; decide +kernel
      have hl : raw18322step0Labels = raw18322Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18322 raw18322Labels permutation200 permutation7
    mixedMoment B raw18322step0 raw18322step0Labels = mixedMoment B raw18322step1 raw18322step1Labels := by
      have ha : raw18322step1 = -raw18322step0 := by apply Matrix.ext; change ∀ i j, raw18322step1 i j = -(raw18322step0 i j); unfold raw18322step1 raw18322step0; decide +kernel
      have hl : raw18322step1Labels = raw18322step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18322step1 raw18322step1Labels = mixedMoment B raw18322step2 raw18322step2Labels := by
      have ha : raw18322step2 = raw18322step1 := by apply Matrix.ext; unfold raw18322step2 raw18322step1; decide +kernel
      have hl : raw18322step1Labels = labelEmbedding10 ∘ raw18322step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18322step1 raw18322step1Labels raw18322step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw18323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18323 raw18323Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18323 raw18323Labels = mixedMoment B raw18323step0 raw18323step0Labels := by
      have hz : ∀ j, raw18323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18323step0 = (fun i j => raw18323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18323step0 raw18323; decide +kernel
      have hl : raw18323step0Labels = raw18323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18323 raw18323Labels permutation346 hz
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw18324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18324step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18324 raw18324Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw18324 raw18324Labels = mixedMoment B raw18324step0 raw18324step0Labels := by
      have ha : raw18324step0 = (fun i j => raw18324 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18324step0 raw18324; decide +kernel
      have hl : raw18324step0Labels = raw18324Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18324 raw18324Labels permutation686 permutation2
    mixedMoment B raw18324step0 raw18324step0Labels = mixedMoment B raw18324step1 raw18324step1Labels := by
      have ha : raw18324step1 = -raw18324step0 := by apply Matrix.ext; change ∀ i j, raw18324step1 i j = -(raw18324step0 i j); unfold raw18324step1 raw18324step0; decide +kernel
      have hl : raw18324step1Labels = raw18324step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw18325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18325 raw18325Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw18325 raw18325Labels = mixedMoment B raw18325step0 raw18325step0Labels := by
      have hz : ∀ j, raw18325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18325step0 = (fun i j => raw18325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18325step0 raw18325; decide +kernel
      have hl : raw18325step0Labels = raw18325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18325 raw18325Labels permutation346 hz
    mixedMoment B raw18325step0 raw18325step0Labels = mixedMoment B raw18325step1 raw18325step1Labels := by
      have ha : raw18325step1 = (fun i j => raw18325step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18325step1 raw18325step0; decide +kernel
      have hl : raw18325step1Labels = raw18325step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18325step0 raw18325step0Labels permutation34 permutation2
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw18326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18326 raw18326Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18326 raw18326Labels = mixedMoment B raw18326step0 raw18326step0Labels := by
      have hz : ∀ j, raw18326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18326step0 = (fun i j => raw18326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18326step0 raw18326; decide +kernel
      have hl : raw18326step0Labels = raw18326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18326 raw18326Labels permutation346 hz
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw18327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18327step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18327 raw18327Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw18327 raw18327Labels = mixedMoment B raw18327step0 raw18327step0Labels := by
      have hz : ∀ j, raw18327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18327step0 = (fun i j => raw18327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18327step0 raw18327; decide +kernel
      have hl : raw18327step0Labels = raw18327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18327 raw18327Labels permutation346 hz
    mixedMoment B raw18327step0 raw18327step0Labels = mixedMoment B raw18327step1 raw18327step1Labels := by
      have ha : raw18327step1 = (fun i j => raw18327step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18327step1 raw18327step0; decide +kernel
      have hl : raw18327step1Labels = raw18327step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18327step0 raw18327step0Labels permutation151 permutation2
    mixedMoment B raw18327step1 raw18327step1Labels = mixedMoment B raw18327step2 raw18327step2Labels := by
      have ha : raw18327step2 = -raw18327step1 := by apply Matrix.ext; change ∀ i j, raw18327step2 i j = -(raw18327step1 i j); unfold raw18327step2 raw18327step1; decide +kernel
      have hl : raw18327step2Labels = raw18327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw18328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18328step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18328 raw18328Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw18328 raw18328Labels = mixedMoment B raw18328step0 raw18328step0Labels := by
      have ha : raw18328step0 = (fun i j => raw18328 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18328step0 raw18328; decide +kernel
      have hl : raw18328step0Labels = raw18328Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18328 raw18328Labels permutation686 permutation2
    mixedMoment B raw18328step0 raw18328step0Labels = mixedMoment B raw18328step1 raw18328step1Labels := by
      have ha : raw18328step1 = -raw18328step0 := by apply Matrix.ext; change ∀ i j, raw18328step1 i j = -(raw18328step0 i j); unfold raw18328step1 raw18328step0; decide +kernel
      have hl : raw18328step1Labels = raw18328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw18329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw18329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18329step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18329 raw18329Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw18329 raw18329Labels = mixedMoment B raw18329step0 raw18329step0Labels := by
      have hz : ∀ j, raw18329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18329step0 = (fun i j => raw18329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18329step0 raw18329; decide +kernel
      have hl : raw18329step0Labels = raw18329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18329 raw18329Labels permutation346 hz
    mixedMoment B raw18329step0 raw18329step0Labels = mixedMoment B raw18329step1 raw18329step1Labels := by
      have ha : raw18329step1 = (fun i j => raw18329step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18329step1 raw18329step0; decide +kernel
      have hl : raw18329step1Labels = raw18329step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18329step0 raw18329step0Labels permutation149 permutation2
    mixedMoment B raw18329step1 raw18329step1Labels = mixedMoment B raw18329step2 raw18329step2Labels := by
      have ha : raw18329step2 = -raw18329step1 := by apply Matrix.ext; change ∀ i j, raw18329step2 i j = -(raw18329step1 i j); unfold raw18329step2 raw18329step1; decide +kernel
      have hl : raw18329step2Labels = raw18329step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw18330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw18330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw18330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18330 raw18330Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw18330 raw18330Labels = mixedMoment B raw18330step0 raw18330step0Labels := by
      have hz : ∀ j, raw18330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18330step0 = (fun i j => raw18330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18330step0 raw18330; decide +kernel
      have hl : raw18330step0Labels = raw18330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18330 raw18330Labels permutation346 hz
    mixedMoment B raw18330step0 raw18330step0Labels = mixedMoment B raw18330step1 raw18330step1Labels := by
      have ha : raw18330step1 = (fun i j => raw18330step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18330step1 raw18330step0; decide +kernel
      have hl : raw18330step1Labels = raw18330step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18330step0 raw18330step0Labels permutation33 permutation2
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw18331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18331step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18331 raw18331Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw18331 raw18331Labels = mixedMoment B raw18331step0 raw18331step0Labels := by
      have hz : ∀ j, raw18331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18331step0 = (fun i j => raw18331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18331step0 raw18331; decide +kernel
      have hl : raw18331step0Labels = raw18331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18331 raw18331Labels permutation346 hz
    mixedMoment B raw18331step0 raw18331step0Labels = mixedMoment B raw18331step1 raw18331step1Labels := by
      have ha : raw18331step1 = (fun i j => raw18331step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18331step1 raw18331step0; decide +kernel
      have hl : raw18331step1Labels = raw18331step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18331step0 raw18331step0Labels permutation151 permutation2
    mixedMoment B raw18331step1 raw18331step1Labels = mixedMoment B raw18331step2 raw18331step2Labels := by
      have ha : raw18331step2 = -raw18331step1 := by apply Matrix.ext; change ∀ i j, raw18331step2 i j = -(raw18331step1 i j); unfold raw18331step2 raw18331step1; decide +kernel
      have hl : raw18331step2Labels = raw18331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw18332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18332 raw18332Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw18332 raw18332Labels = mixedMoment B raw18332step0 raw18332step0Labels := by
      have ha : raw18332step0 = (fun i j => raw18332 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18332step0 raw18332; decide +kernel
      have hl : raw18332step0Labels = raw18332Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18332 raw18332Labels permutation686 permutation2
    mixedMoment B raw18332step0 raw18332step0Labels = mixedMoment B raw18332step1 raw18332step1Labels := by
      have ha : raw18332step1 = -raw18332step0 := by apply Matrix.ext; change ∀ i j, raw18332step1 i j = -(raw18332step0 i j); unfold raw18332step1 raw18332step0; decide +kernel
      have hl : raw18332step1Labels = raw18332step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5072 node5072Labels := by rfl

def raw18333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw18333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18333step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18333 raw18333Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw18333 raw18333Labels = mixedMoment B raw18333step0 raw18333step0Labels := by
      have hz : ∀ j, raw18333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18333step0 = (fun i j => raw18333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18333step0 raw18333; decide +kernel
      have hl : raw18333step0Labels = raw18333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18333 raw18333Labels permutation346 hz
    mixedMoment B raw18333step0 raw18333step0Labels = mixedMoment B raw18333step1 raw18333step1Labels := by
      have ha : raw18333step1 = (fun i j => raw18333step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18333step1 raw18333step0; decide +kernel
      have hl : raw18333step1Labels = raw18333step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18333step0 raw18333step0Labels permutation149 permutation2
    mixedMoment B raw18333step1 raw18333step1Labels = mixedMoment B raw18333step2 raw18333step2Labels := by
      have ha : raw18333step2 = -raw18333step1 := by apply Matrix.ext; change ∀ i j, raw18333step2 i j = -(raw18333step1 i j); unfold raw18333step2 raw18333step1; decide +kernel
      have hl : raw18333step2Labels = raw18333step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw18334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw18334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw18334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18334step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18334 raw18334Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw18334 raw18334Labels = mixedMoment B raw18334step0 raw18334step0Labels := by
      have hz : ∀ j, raw18334 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18334step0 = (fun i j => raw18334 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18334step0 raw18334; decide +kernel
      have hl : raw18334step0Labels = raw18334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18334 raw18334Labels permutation346 hz
    mixedMoment B raw18334step0 raw18334step0Labels = mixedMoment B raw18334step1 raw18334step1Labels := by
      have ha : raw18334step1 = (fun i j => raw18334step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18334step1 raw18334step0; decide +kernel
      have hl : raw18334step1Labels = raw18334step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18334step0 raw18334step0Labels permutation151 permutation2
    mixedMoment B raw18334step1 raw18334step1Labels = mixedMoment B raw18334step2 raw18334step2Labels := by
      have ha : raw18334step2 = -raw18334step1 := by apply Matrix.ext; change ∀ i j, raw18334step2 i j = -(raw18334step1 i j); unfold raw18334step2 raw18334step1; decide +kernel
      have hl : raw18334step2Labels = raw18334step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw18335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18335step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw18335step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical18335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18335 raw18335Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw18335 raw18335Labels = mixedMoment B raw18335step0 raw18335step0Labels := by
      have hz : ∀ j, raw18335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18335step0 = (fun i j => raw18335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18335step0 raw18335; decide +kernel
      have hl : raw18335step0Labels = raw18335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18335 raw18335Labels permutation434 hz
    mixedMoment B raw18335step0 raw18335step0Labels = mixedMoment B raw18335step1 raw18335step1Labels := by
      have hz : ∀ i, raw18335step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18335step1 = (fun i j => raw18335step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18335step1 raw18335step0; decide +kernel
      have hl : raw18335step1Labels = (fun j => raw18335step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18335step0 raw18335step0Labels permutation6 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw18336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18336step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw18336step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18336step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw18336step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical18336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18336 raw18336Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw18336 raw18336Labels = mixedMoment B raw18336step0 raw18336step0Labels := by
      have hz : ∀ i, raw18336 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18336step0 = (fun i j => raw18336 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18336step0 raw18336; decide +kernel
      have hl : raw18336step0Labels = (fun j => raw18336Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18336 raw18336Labels permutation6 hz
    mixedMoment B raw18336step0 raw18336step0Labels = mixedMoment B raw18336step1 raw18336step1Labels := by
      have ha : raw18336step1 = (fun i j => raw18336step0 (permutation158 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18336step1 raw18336step0; decide +kernel
      have hl : raw18336step1Labels = raw18336step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18336step0 raw18336step0Labels permutation158 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw18337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18337step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw18337step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical18337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18337 raw18337Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw18337 raw18337Labels = mixedMoment B raw18337step0 raw18337step0Labels := by
      have hz : ∀ j, raw18337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18337step0 = (fun i j => raw18337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18337step0 raw18337; decide +kernel
      have hl : raw18337step0Labels = raw18337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18337 raw18337Labels permutation346 hz
    mixedMoment B raw18337step0 raw18337step0Labels = mixedMoment B raw18337step1 raw18337step1Labels := by
      have hz : ∀ i, raw18337step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18337step1 = (fun i j => raw18337step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18337step1 raw18337step0; decide +kernel
      have hl : raw18337step1Labels = (fun j => raw18337step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18337step0 raw18337step0Labels permutation6 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw18338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18338step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw18338step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical18338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18338 raw18338Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw18338 raw18338Labels = mixedMoment B raw18338step0 raw18338step0Labels := by
      have hz : ∀ i, raw18338 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18338step0 = (fun i j => raw18338 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18338step0 raw18338; decide +kernel
      have hl : raw18338step0Labels = (fun j => raw18338Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18338 raw18338Labels permutation6 hz
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw18339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18339step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18339step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw18339step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical18339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18339 raw18339Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw18339 raw18339Labels = mixedMoment B raw18339step0 raw18339step0Labels := by
      have hz : ∀ j, raw18339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18339step0 = (fun i j => raw18339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18339step0 raw18339; decide +kernel
      have hl : raw18339step0Labels = raw18339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18339 raw18339Labels permutation434 hz
    mixedMoment B raw18339step0 raw18339step0Labels = mixedMoment B raw18339step1 raw18339step1Labels := by
      have hz : ∀ j, raw18339step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18339step1 = (fun i j => raw18339step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18339step1 raw18339step0; decide +kernel
      have hl : raw18339step1Labels = raw18339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18339step0 raw18339step0Labels permutation80 hz
    mixedMoment B raw18339step1 raw18339step1Labels = mixedMoment B raw18339step2 raw18339step2Labels := by
      have hz : ∀ i, raw18339step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18339step2 = (fun i j => raw18339step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18339step2 raw18339step1; decide +kernel
      have hl : raw18339step2Labels = (fun j => raw18339step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18339step1 raw18339step1Labels permutation6 hz
    _ = mixedMoment B node4089 node4089Labels := by rfl

def raw18340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18340step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw18340step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18340step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw18340step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18340step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw18340step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical18340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18340 raw18340Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw18340 raw18340Labels = mixedMoment B raw18340step0 raw18340step0Labels := by
      have hz : ∀ j, raw18340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18340step0 = (fun i j => raw18340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18340step0 raw18340; decide +kernel
      have hl : raw18340step0Labels = raw18340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18340 raw18340Labels permutation434 hz
    mixedMoment B raw18340step0 raw18340step0Labels = mixedMoment B raw18340step1 raw18340step1Labels := by
      have hz : ∀ i, raw18340step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18340step1 = (fun i j => raw18340step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18340step1 raw18340step0; decide +kernel
      have hl : raw18340step1Labels = (fun j => raw18340step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18340step0 raw18340step0Labels permutation6 hz
    mixedMoment B raw18340step1 raw18340step1Labels = mixedMoment B raw18340step2 raw18340step2Labels := by
      have ha : raw18340step2 = (fun i j => raw18340step1 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18340step2 raw18340step1; decide +kernel
      have hl : raw18340step2Labels = raw18340step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18340step1 raw18340step1Labels permutation125 permutation0
    mixedMoment B raw18340step2 raw18340step2Labels = mixedMoment B raw18340step3 raw18340step3Labels := by
      have ha : raw18340step3 = -raw18340step2 := by apply Matrix.ext; change ∀ i j, raw18340step3 i j = -(raw18340step2 i j); unfold raw18340step3 raw18340step2; decide +kernel
      have hl : raw18340step3Labels = raw18340step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw18341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18341step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18341step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw18341step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18341step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw18341step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18341step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw18341step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical18341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18341 raw18341Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw18341 raw18341Labels = mixedMoment B raw18341step0 raw18341step0Labels := by
      have hz : ∀ j, raw18341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18341step0 = (fun i j => raw18341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18341step0 raw18341; decide +kernel
      have hl : raw18341step0Labels = raw18341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18341 raw18341Labels permutation346 hz
    mixedMoment B raw18341step0 raw18341step0Labels = mixedMoment B raw18341step1 raw18341step1Labels := by
      have hz : ∀ i, raw18341step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18341step1 = (fun i j => raw18341step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18341step1 raw18341step0; decide +kernel
      have hl : raw18341step1Labels = (fun j => raw18341step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18341step0 raw18341step0Labels permutation6 hz
    mixedMoment B raw18341step1 raw18341step1Labels = mixedMoment B raw18341step2 raw18341step2Labels := by
      have ha : raw18341step2 = (fun i j => raw18341step1 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18341step2 raw18341step1; decide +kernel
      have hl : raw18341step2Labels = raw18341step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18341step1 raw18341step1Labels permutation125 permutation0
    mixedMoment B raw18341step2 raw18341step2Labels = mixedMoment B raw18341step3 raw18341step3Labels := by
      have ha : raw18341step3 = -raw18341step2 := by apply Matrix.ext; change ∀ i j, raw18341step3 i j = -(raw18341step2 i j); unfold raw18341step3 raw18341step2; decide +kernel
      have hl : raw18341step3Labels = raw18341step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw18342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18342step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18342step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18342step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw18342step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18342step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw18342step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18342step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw18342step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical18342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18342 raw18342Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw18342 raw18342Labels = mixedMoment B raw18342step0 raw18342step0Labels := by
      have hz : ∀ j, raw18342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18342step0 = (fun i j => raw18342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18342step0 raw18342; decide +kernel
      have hl : raw18342step0Labels = raw18342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18342 raw18342Labels permutation434 hz
    mixedMoment B raw18342step0 raw18342step0Labels = mixedMoment B raw18342step1 raw18342step1Labels := by
      have hz : ∀ j, raw18342step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18342step1 = (fun i j => raw18342step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18342step1 raw18342step0; decide +kernel
      have hl : raw18342step1Labels = raw18342step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18342step0 raw18342step0Labels permutation80 hz
    mixedMoment B raw18342step1 raw18342step1Labels = mixedMoment B raw18342step2 raw18342step2Labels := by
      have hz : ∀ i, raw18342step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18342step2 = (fun i j => raw18342step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18342step2 raw18342step1; decide +kernel
      have hl : raw18342step2Labels = (fun j => raw18342step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18342step1 raw18342step1Labels permutation6 hz
    mixedMoment B raw18342step2 raw18342step2Labels = mixedMoment B raw18342step3 raw18342step3Labels := by
      have ha : raw18342step3 = (fun i j => raw18342step2 (permutation30 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18342step3 raw18342step2; decide +kernel
      have hl : raw18342step3Labels = raw18342step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18342step2 raw18342step2Labels permutation30 permutation0
    mixedMoment B raw18342step3 raw18342step3Labels = mixedMoment B raw18342step4 raw18342step4Labels := by
      have ha : raw18342step4 = -raw18342step3 := by apply Matrix.ext; change ∀ i j, raw18342step4 i j = -(raw18342step3 i j); unfold raw18342step4 raw18342step3; decide +kernel
      have hl : raw18342step4Labels = raw18342step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw18343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18343step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18343step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw18343step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18343step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw18343step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18343step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw18343step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical18343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18343 raw18343Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw18343 raw18343Labels = mixedMoment B raw18343step0 raw18343step0Labels := by
      have hz : ∀ j, raw18343 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18343step0 = (fun i j => raw18343 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18343step0 raw18343; decide +kernel
      have hl : raw18343step0Labels = raw18343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18343 raw18343Labels permutation434 hz
    mixedMoment B raw18343step0 raw18343step0Labels = mixedMoment B raw18343step1 raw18343step1Labels := by
      have hz : ∀ i, raw18343step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18343step1 = (fun i j => raw18343step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18343step1 raw18343step0; decide +kernel
      have hl : raw18343step1Labels = (fun j => raw18343step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18343step0 raw18343step0Labels permutation6 hz
    mixedMoment B raw18343step1 raw18343step1Labels = mixedMoment B raw18343step2 raw18343step2Labels := by
      have ha : raw18343step2 = (fun i j => raw18343step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18343step2 raw18343step1; decide +kernel
      have hl : raw18343step2Labels = raw18343step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18343step1 raw18343step1Labels permutation149 permutation0
    mixedMoment B raw18343step2 raw18343step2Labels = mixedMoment B raw18343step3 raw18343step3Labels := by
      have ha : raw18343step3 = -raw18343step2 := by apply Matrix.ext; change ∀ i j, raw18343step3 i j = -(raw18343step2 i j); unfold raw18343step3 raw18343step2; decide +kernel
      have hl : raw18343step3Labels = raw18343step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw18344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18344step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw18344step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18344step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw18344step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18344step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw18344step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical18344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18344 raw18344Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw18344 raw18344Labels = mixedMoment B raw18344step0 raw18344step0Labels := by
      have hz : ∀ j, raw18344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18344step0 = (fun i j => raw18344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18344step0 raw18344; decide +kernel
      have hl : raw18344step0Labels = raw18344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18344 raw18344Labels permutation346 hz
    mixedMoment B raw18344step0 raw18344step0Labels = mixedMoment B raw18344step1 raw18344step1Labels := by
      have hz : ∀ i, raw18344step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw18344step1 = (fun i j => raw18344step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw18344step1 raw18344step0; decide +kernel
      have hl : raw18344step1Labels = (fun j => raw18344step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw18344step0 raw18344step0Labels permutation6 hz
    mixedMoment B raw18344step1 raw18344step1Labels = mixedMoment B raw18344step2 raw18344step2Labels := by
      have ha : raw18344step2 = (fun i j => raw18344step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18344step2 raw18344step1; decide +kernel
      have hl : raw18344step2Labels = raw18344step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18344step1 raw18344step1Labels permutation149 permutation0
    mixedMoment B raw18344step2 raw18344step2Labels = mixedMoment B raw18344step3 raw18344step3Labels := by
      have ha : raw18344step3 = -raw18344step2 := by apply Matrix.ext; change ∀ i j, raw18344step3 i j = -(raw18344step2 i j); unfold raw18344step3 raw18344step2; decide +kernel
      have hl : raw18344step3Labels = raw18344step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw18345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18345step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18345step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18345 raw18345Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw18345 raw18345Labels = mixedMoment B raw18345step0 raw18345step0Labels := by
      have hz : ∀ j, raw18345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18345step0 = (fun i j => raw18345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18345step0 raw18345; decide +kernel
      have hl : raw18345step0Labels = raw18345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18345 raw18345Labels permutation346 hz
    mixedMoment B raw18345step0 raw18345step0Labels = mixedMoment B raw18345step1 raw18345step1Labels := by
      have ha : raw18345step1 = (fun i j => raw18345step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18345step1 raw18345step0; decide +kernel
      have hl : raw18345step1Labels = raw18345step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18345step0 raw18345step0Labels permutation60 permutation3
    mixedMoment B raw18345step1 raw18345step1Labels = mixedMoment B raw18345step2 raw18345step2Labels := by
      have ha : raw18345step2 = raw18345step1 := by apply Matrix.ext; unfold raw18345step2 raw18345step1; decide +kernel
      have hl : raw18345step1Labels = labelEmbedding6 ∘ raw18345step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18345step1 raw18345step1Labels raw18345step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw18346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw18346step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw18346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18346 raw18346Labels = mixedMoment B node5488 node5488Labels := by
  calc
    mixedMoment B raw18346 raw18346Labels = mixedMoment B raw18346step0 raw18346step0Labels := by
      have ha : raw18346step0 = (fun i j => raw18346 (permutation609 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18346step0 raw18346; decide +kernel
      have hl : raw18346step0Labels = raw18346Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18346 raw18346Labels permutation609 permutation6
    mixedMoment B raw18346step0 raw18346step0Labels = mixedMoment B raw18346step1 raw18346step1Labels := by
      have ha : raw18346step1 = raw18346step0 := by apply Matrix.ext; unfold raw18346step1 raw18346step0; decide +kernel
      have hl : raw18346step0Labels = labelEmbedding9 ∘ raw18346step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18346step0 raw18346step0Labels raw18346step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5488 node5488Labels := by rfl

def raw18347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18347step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18347step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18347step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18347step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18347step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18347 raw18347Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw18347 raw18347Labels = mixedMoment B raw18347step0 raw18347step0Labels := by
      have hz : ∀ j, raw18347 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18347step0 = (fun i j => raw18347 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18347step0 raw18347; decide +kernel
      have hl : raw18347step0Labels = raw18347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18347 raw18347Labels permutation520 hz
    mixedMoment B raw18347step0 raw18347step0Labels = mixedMoment B raw18347step1 raw18347step1Labels := by
      have hz : ∀ j, raw18347step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18347step1 = (fun i j => raw18347step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18347step1 raw18347step0; decide +kernel
      have hl : raw18347step1Labels = raw18347step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18347step0 raw18347step0Labels permutation80 hz
    mixedMoment B raw18347step1 raw18347step1Labels = mixedMoment B raw18347step2 raw18347step2Labels := by
      have ha : raw18347step2 = (fun i j => raw18347step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18347step2 raw18347step1; decide +kernel
      have hl : raw18347step2Labels = raw18347step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18347step1 raw18347step1Labels permutation29 permutation6
    mixedMoment B raw18347step2 raw18347step2Labels = mixedMoment B raw18347step3 raw18347step3Labels := by
      have ha : raw18347step3 = raw18347step2 := by apply Matrix.ext; unfold raw18347step3 raw18347step2; decide +kernel
      have hl : raw18347step2Labels = labelEmbedding9 ∘ raw18347step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18347step2 raw18347step2Labels raw18347step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw18348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18348step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18348step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18348step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18348step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18348 raw18348Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18348 raw18348Labels = mixedMoment B raw18348step0 raw18348step0Labels := by
      have hz : ∀ j, raw18348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18348step0 = (fun i j => raw18348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18348step0 raw18348; decide +kernel
      have hl : raw18348step0Labels = raw18348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18348 raw18348Labels permutation346 hz
    mixedMoment B raw18348step0 raw18348step0Labels = mixedMoment B raw18348step1 raw18348step1Labels := by
      have ha : raw18348step1 = (fun i j => raw18348step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18348step1 raw18348step0; decide +kernel
      have hl : raw18348step1Labels = raw18348step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18348step0 raw18348step0Labels permutation137 permutation4
    mixedMoment B raw18348step1 raw18348step1Labels = mixedMoment B raw18348step2 raw18348step2Labels := by
      have ha : raw18348step2 = -raw18348step1 := by apply Matrix.ext; change ∀ i j, raw18348step2 i j = -(raw18348step1 i j); unfold raw18348step2 raw18348step1; decide +kernel
      have hl : raw18348step2Labels = raw18348step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18348step2 raw18348step2Labels = mixedMoment B raw18348step3 raw18348step3Labels := by
      have ha : raw18348step3 = raw18348step2 := by apply Matrix.ext; unfold raw18348step3 raw18348step2; decide +kernel
      have hl : raw18348step2Labels = labelEmbedding7 ∘ raw18348step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18348step2 raw18348step2Labels raw18348step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18349step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18349step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18349 raw18349Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw18349 raw18349Labels = mixedMoment B raw18349step0 raw18349step0Labels := by
      have ha : raw18349step0 = (fun i j => raw18349 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18349step0 raw18349; decide +kernel
      have hl : raw18349step0Labels = raw18349Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18349 raw18349Labels permutation283 permutation3
    mixedMoment B raw18349step0 raw18349step0Labels = mixedMoment B raw18349step1 raw18349step1Labels := by
      have ha : raw18349step1 = raw18349step0 := by apply Matrix.ext; unfold raw18349step1 raw18349step0; decide +kernel
      have hl : raw18349step0Labels = labelEmbedding6 ∘ raw18349step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18349step0 raw18349step0Labels raw18349step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

def raw18350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18350 raw18350Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18350 raw18350Labels = mixedMoment B raw18350step0 raw18350step0Labels := by
      have hz : ∀ j, raw18350 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18350step0 = (fun i j => raw18350 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18350step0 raw18350; decide +kernel
      have hl : raw18350step0Labels = raw18350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18350 raw18350Labels permutation520 hz
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18351 raw18351Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw18351 raw18351Labels = mixedMoment B raw18351step0 raw18351step0Labels := by
      have ha : raw18351step0 = (fun i j => raw18351 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18351step0 raw18351; decide +kernel
      have hl : raw18351step0Labels = raw18351Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18351 raw18351Labels permutation170 permutation2
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw18352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18352step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18352 raw18352Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18352 raw18352Labels = mixedMoment B raw18352step0 raw18352step0Labels := by
      have hz : ∀ j, raw18352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18352step0 = (fun i j => raw18352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18352step0 raw18352; decide +kernel
      have hl : raw18352step0Labels = raw18352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18352 raw18352Labels permutation346 hz
    mixedMoment B raw18352step0 raw18352step0Labels = mixedMoment B raw18352step1 raw18352step1Labels := by
      have ha : raw18352step1 = (fun i j => raw18352step0 (permutation61 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18352step1 raw18352step0; decide +kernel
      have hl : raw18352step1Labels = raw18352step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18352step0 raw18352step0Labels permutation61 permutation3
    mixedMoment B raw18352step1 raw18352step1Labels = mixedMoment B raw18352step2 raw18352step2Labels := by
      have ha : raw18352step2 = raw18352step1 := by apply Matrix.ext; unfold raw18352step2 raw18352step1; decide +kernel
      have hl : raw18352step1Labels = labelEmbedding6 ∘ raw18352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18352step1 raw18352step1Labels raw18352step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw18353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18353step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18353step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18353step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18353 raw18353Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw18353 raw18353Labels = mixedMoment B raw18353step0 raw18353step0Labels := by
      have ha : raw18353step0 = (fun i j => raw18353 (permutation502 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18353step0 raw18353; decide +kernel
      have hl : raw18353step0Labels = raw18353Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18353 raw18353Labels permutation502 permutation3
    mixedMoment B raw18353step0 raw18353step0Labels = mixedMoment B raw18353step1 raw18353step1Labels := by
      have ha : raw18353step1 = -raw18353step0 := by apply Matrix.ext; change ∀ i j, raw18353step1 i j = -(raw18353step0 i j); unfold raw18353step1 raw18353step0; decide +kernel
      have hl : raw18353step1Labels = raw18353step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18353step1 raw18353step1Labels = mixedMoment B raw18353step2 raw18353step2Labels := by
      have ha : raw18353step2 = raw18353step1 := by apply Matrix.ext; unfold raw18353step2 raw18353step1; decide +kernel
      have hl : raw18353step1Labels = labelEmbedding6 ∘ raw18353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18353step1 raw18353step1Labels raw18353step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw18354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18354step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18354 raw18354Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw18354 raw18354Labels = mixedMoment B raw18354step0 raw18354step0Labels := by
      have hz : ∀ j, raw18354 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18354step0 = (fun i j => raw18354 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18354step0 raw18354; decide +kernel
      have hl : raw18354step0Labels = raw18354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18354 raw18354Labels permutation520 hz
    mixedMoment B raw18354step0 raw18354step0Labels = mixedMoment B raw18354step1 raw18354step1Labels := by
      have hz : ∀ j, raw18354step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18354step1 = (fun i j => raw18354step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18354step1 raw18354step0; decide +kernel
      have hl : raw18354step1Labels = raw18354step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18354step0 raw18354step0Labels permutation80 hz
    mixedMoment B raw18354step1 raw18354step1Labels = mixedMoment B raw18354step2 raw18354step2Labels := by
      have ha : raw18354step2 = (fun i j => raw18354step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18354step2 raw18354step1; decide +kernel
      have hl : raw18354step2Labels = raw18354step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18354step1 raw18354step1Labels permutation9 permutation2
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw18355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18355step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18355step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18355step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18355step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18355 raw18355Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18355 raw18355Labels = mixedMoment B raw18355step0 raw18355step0Labels := by
      have hz : ∀ j, raw18355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18355step0 = (fun i j => raw18355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18355step0 raw18355; decide +kernel
      have hl : raw18355step0Labels = raw18355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18355 raw18355Labels permutation346 hz
    mixedMoment B raw18355step0 raw18355step0Labels = mixedMoment B raw18355step1 raw18355step1Labels := by
      have ha : raw18355step1 = (fun i j => raw18355step0 (permutation97 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18355step1 raw18355step0; decide +kernel
      have hl : raw18355step1Labels = raw18355step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18355step0 raw18355step0Labels permutation97 permutation3
    mixedMoment B raw18355step1 raw18355step1Labels = mixedMoment B raw18355step2 raw18355step2Labels := by
      have ha : raw18355step2 = -raw18355step1 := by apply Matrix.ext; change ∀ i j, raw18355step2 i j = -(raw18355step1 i j); unfold raw18355step2 raw18355step1; decide +kernel
      have hl : raw18355step2Labels = raw18355step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18355step2 raw18355step2Labels = mixedMoment B raw18355step3 raw18355step3Labels := by
      have ha : raw18355step3 = raw18355step2 := by apply Matrix.ext; unfold raw18355step3 raw18355step2; decide +kernel
      have hl : raw18355step2Labels = labelEmbedding6 ∘ raw18355step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18355step2 raw18355step2Labels raw18355step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw18356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18356step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18356 raw18356Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18356 raw18356Labels = mixedMoment B raw18356step0 raw18356step0Labels := by
      have hz : ∀ j, raw18356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18356step0 = (fun i j => raw18356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18356step0 raw18356; decide +kernel
      have hl : raw18356step0Labels = raw18356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18356 raw18356Labels permutation346 hz
    mixedMoment B raw18356step0 raw18356step0Labels = mixedMoment B raw18356step1 raw18356step1Labels := by
      have ha : raw18356step1 = (fun i j => raw18356step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18356step1 raw18356step0; decide +kernel
      have hl : raw18356step1Labels = raw18356step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18356step0 raw18356step0Labels permutation60 permutation3
    mixedMoment B raw18356step1 raw18356step1Labels = mixedMoment B raw18356step2 raw18356step2Labels := by
      have ha : raw18356step2 = raw18356step1 := by apply Matrix.ext; unfold raw18356step2 raw18356step1; decide +kernel
      have hl : raw18356step1Labels = labelEmbedding6 ∘ raw18356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18356step1 raw18356step1Labels raw18356step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw18357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18357step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18357step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18357step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18357step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18357 raw18357Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw18357 raw18357Labels = mixedMoment B raw18357step0 raw18357step0Labels := by
      have ha : raw18357step0 = (fun i j => raw18357 (permutation566 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18357step0 raw18357; decide +kernel
      have hl : raw18357step0Labels = raw18357Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18357 raw18357Labels permutation566 permutation3
    mixedMoment B raw18357step0 raw18357step0Labels = mixedMoment B raw18357step1 raw18357step1Labels := by
      have ha : raw18357step1 = -raw18357step0 := by apply Matrix.ext; change ∀ i j, raw18357step1 i j = -(raw18357step0 i j); unfold raw18357step1 raw18357step0; decide +kernel
      have hl : raw18357step1Labels = raw18357step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18357step1 raw18357step1Labels = mixedMoment B raw18357step2 raw18357step2Labels := by
      have ha : raw18357step2 = raw18357step1 := by apply Matrix.ext; unfold raw18357step2 raw18357step1; decide +kernel
      have hl : raw18357step1Labels = labelEmbedding6 ∘ raw18357step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18357step1 raw18357step1Labels raw18357step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw18358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18358step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18358step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18358step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18358step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18358 raw18358Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18358 raw18358Labels = mixedMoment B raw18358step0 raw18358step0Labels := by
      have hz : ∀ j, raw18358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18358step0 = (fun i j => raw18358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18358step0 raw18358; decide +kernel
      have hl : raw18358step0Labels = raw18358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18358 raw18358Labels permutation346 hz
    mixedMoment B raw18358step0 raw18358step0Labels = mixedMoment B raw18358step1 raw18358step1Labels := by
      have ha : raw18358step1 = (fun i j => raw18358step0 (permutation121 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18358step1 raw18358step0; decide +kernel
      have hl : raw18358step1Labels = raw18358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18358step0 raw18358step0Labels permutation121 permutation3
    mixedMoment B raw18358step1 raw18358step1Labels = mixedMoment B raw18358step2 raw18358step2Labels := by
      have ha : raw18358step2 = -raw18358step1 := by apply Matrix.ext; change ∀ i j, raw18358step2 i j = -(raw18358step1 i j); unfold raw18358step2 raw18358step1; decide +kernel
      have hl : raw18358step2Labels = raw18358step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18358step2 raw18358step2Labels = mixedMoment B raw18358step3 raw18358step3Labels := by
      have ha : raw18358step3 = raw18358step2 := by apply Matrix.ext; unfold raw18358step3 raw18358step2; decide +kernel
      have hl : raw18358step2Labels = labelEmbedding6 ∘ raw18358step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18358step2 raw18358step2Labels raw18358step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw18359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18359step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18359step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18359step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18359step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18359 raw18359Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18359 raw18359Labels = mixedMoment B raw18359step0 raw18359step0Labels := by
      have ha : raw18359step0 = (fun i j => raw18359 (permutation303 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18359step0 raw18359; decide +kernel
      have hl : raw18359step0Labels = raw18359Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18359 raw18359Labels permutation303 permutation5
    mixedMoment B raw18359step0 raw18359step0Labels = mixedMoment B raw18359step1 raw18359step1Labels := by
      have ha : raw18359step1 = -raw18359step0 := by apply Matrix.ext; change ∀ i j, raw18359step1 i j = -(raw18359step0 i j); unfold raw18359step1 raw18359step0; decide +kernel
      have hl : raw18359step1Labels = raw18359step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18359step1 raw18359step1Labels = mixedMoment B raw18359step2 raw18359step2Labels := by
      have ha : raw18359step2 = raw18359step1 := by apply Matrix.ext; unfold raw18359step2 raw18359step1; decide +kernel
      have hl : raw18359step1Labels = labelEmbedding8 ∘ raw18359step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18359step1 raw18359step1Labels raw18359step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw18360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18360step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18360step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18360step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18360step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18360step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18360 raw18360Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw18360 raw18360Labels = mixedMoment B raw18360step0 raw18360step0Labels := by
      have ha : raw18360step0 = (fun i j => raw18360 (permutation379 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18360step0 raw18360; decide +kernel
      have hl : raw18360step0Labels = raw18360Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18360 raw18360Labels permutation379 permutation5
    mixedMoment B raw18360step0 raw18360step0Labels = mixedMoment B raw18360step1 raw18360step1Labels := by
      have ha : raw18360step1 = -raw18360step0 := by apply Matrix.ext; change ∀ i j, raw18360step1 i j = -(raw18360step0 i j); unfold raw18360step1 raw18360step0; decide +kernel
      have hl : raw18360step1Labels = raw18360step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18360step1 raw18360step1Labels = mixedMoment B raw18360step2 raw18360step2Labels := by
      have ha : raw18360step2 = raw18360step1 := by apply Matrix.ext; unfold raw18360step2 raw18360step1; decide +kernel
      have hl : raw18360step1Labels = labelEmbedding8 ∘ raw18360step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18360step1 raw18360step1Labels raw18360step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw18361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18361step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18361step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18361step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18361step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18361 raw18361Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18361 raw18361Labels = mixedMoment B raw18361step0 raw18361step0Labels := by
      have hz : ∀ j, raw18361 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18361step0 = (fun i j => raw18361 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18361step0 raw18361; decide +kernel
      have hl : raw18361step0Labels = raw18361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18361 raw18361Labels permutation434 hz
    mixedMoment B raw18361step0 raw18361step0Labels = mixedMoment B raw18361step1 raw18361step1Labels := by
      have ha : raw18361step1 = (fun i j => raw18361step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18361step1 raw18361step0; decide +kernel
      have hl : raw18361step1Labels = raw18361step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18361step0 raw18361step0Labels permutation45 permutation6
    mixedMoment B raw18361step1 raw18361step1Labels = mixedMoment B raw18361step2 raw18361step2Labels := by
      have ha : raw18361step2 = -raw18361step1 := by apply Matrix.ext; change ∀ i j, raw18361step2 i j = -(raw18361step1 i j); unfold raw18361step2 raw18361step1; decide +kernel
      have hl : raw18361step2Labels = raw18361step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18361step2 raw18361step2Labels = mixedMoment B raw18361step3 raw18361step3Labels := by
      have ha : raw18361step3 = raw18361step2 := by apply Matrix.ext; unfold raw18361step3 raw18361step2; decide +kernel
      have hl : raw18361step2Labels = labelEmbedding9 ∘ raw18361step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18361step2 raw18361step2Labels raw18361step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw18362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18362step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18362step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18362step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18362step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18362 raw18362Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18362 raw18362Labels = mixedMoment B raw18362step0 raw18362step0Labels := by
      have hz : ∀ j, raw18362 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18362step0 = (fun i j => raw18362 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18362step0 raw18362; decide +kernel
      have hl : raw18362step0Labels = raw18362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18362 raw18362Labels permutation520 hz
    mixedMoment B raw18362step0 raw18362step0Labels = mixedMoment B raw18362step1 raw18362step1Labels := by
      have ha : raw18362step1 = (fun i j => raw18362step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18362step1 raw18362step0; decide +kernel
      have hl : raw18362step1Labels = raw18362step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18362step0 raw18362step0Labels permutation45 permutation6
    mixedMoment B raw18362step1 raw18362step1Labels = mixedMoment B raw18362step2 raw18362step2Labels := by
      have ha : raw18362step2 = -raw18362step1 := by apply Matrix.ext; change ∀ i j, raw18362step2 i j = -(raw18362step1 i j); unfold raw18362step2 raw18362step1; decide +kernel
      have hl : raw18362step2Labels = raw18362step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18362step2 raw18362step2Labels = mixedMoment B raw18362step3 raw18362step3Labels := by
      have ha : raw18362step3 = raw18362step2 := by apply Matrix.ext; unfold raw18362step3 raw18362step2; decide +kernel
      have hl : raw18362step2Labels = labelEmbedding9 ∘ raw18362step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18362step2 raw18362step2Labels raw18362step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw18363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18363step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18363step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18363step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18363step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18363step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18363 raw18363Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw18363 raw18363Labels = mixedMoment B raw18363step0 raw18363step0Labels := by
      have ha : raw18363step0 = (fun i j => raw18363 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18363step0 raw18363; decide +kernel
      have hl : raw18363step0Labels = raw18363Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18363 raw18363Labels permutation212 permutation6
    mixedMoment B raw18363step0 raw18363step0Labels = mixedMoment B raw18363step1 raw18363step1Labels := by
      have ha : raw18363step1 = -raw18363step0 := by apply Matrix.ext; change ∀ i j, raw18363step1 i j = -(raw18363step0 i j); unfold raw18363step1 raw18363step0; decide +kernel
      have hl : raw18363step1Labels = raw18363step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18363step1 raw18363step1Labels = mixedMoment B raw18363step2 raw18363step2Labels := by
      have ha : raw18363step2 = raw18363step1 := by apply Matrix.ext; unfold raw18363step2 raw18363step1; decide +kernel
      have hl : raw18363step1Labels = labelEmbedding9 ∘ raw18363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18363step1 raw18363step1Labels raw18363step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw18364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18364 raw18364Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw18364 raw18364Labels = mixedMoment B raw18364step0 raw18364step0Labels := by
      have hz : ∀ j, raw18364 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18364step0 = (fun i j => raw18364 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18364step0 raw18364; decide +kernel
      have hl : raw18364step0Labels = raw18364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18364 raw18364Labels permutation265 hz
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw18365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18365 raw18365Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw18365 raw18365Labels = mixedMoment B raw18365step0 raw18365step0Labels := by
      have ha : raw18365step0 = (fun i j => raw18365 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18365step0 raw18365; decide +kernel
      have hl : raw18365step0Labels = raw18365Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18365 raw18365Labels permutation160 permutation2
    _ = mixedMoment B node5386 node5386Labels := by rfl

def raw18366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18366step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18366step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18366 raw18366Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw18366 raw18366Labels = mixedMoment B raw18366step0 raw18366step0Labels := by
      have hz : ∀ j, raw18366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18366step0 = (fun i j => raw18366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18366step0 raw18366; decide +kernel
      have hl : raw18366step0Labels = raw18366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18366 raw18366Labels permutation434 hz
    mixedMoment B raw18366step0 raw18366step0Labels = mixedMoment B raw18366step1 raw18366step1Labels := by
      have ha : raw18366step1 = (fun i j => raw18366step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18366step1 raw18366step0; decide +kernel
      have hl : raw18366step1Labels = raw18366step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18366step0 raw18366step0Labels permutation34 permutation2
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw18367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18367step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18367step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18367 raw18367Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw18367 raw18367Labels = mixedMoment B raw18367step0 raw18367step0Labels := by
      have hz : ∀ j, raw18367 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18367step0 = (fun i j => raw18367 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18367step0 raw18367; decide +kernel
      have hl : raw18367step0Labels = raw18367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18367 raw18367Labels permutation520 hz
    mixedMoment B raw18367step0 raw18367step0Labels = mixedMoment B raw18367step1 raw18367step1Labels := by
      have ha : raw18367step1 = (fun i j => raw18367step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18367step1 raw18367step0; decide +kernel
      have hl : raw18367step1Labels = raw18367step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18367step0 raw18367step0Labels permutation34 permutation2
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw18368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18368step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18368 raw18368Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18368 raw18368Labels = mixedMoment B raw18368step0 raw18368step0Labels := by
      have ha : raw18368step0 = (fun i j => raw18368 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18368step0 raw18368; decide +kernel
      have hl : raw18368step0Labels = raw18368Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18368 raw18368Labels permutation173 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18369step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18369step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18369 raw18369Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18369 raw18369Labels = mixedMoment B raw18369step0 raw18369step0Labels := by
      have ha : raw18369step0 = (fun i j => raw18369 (permutation270 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18369step0 raw18369; decide +kernel
      have hl : raw18369step0Labels = raw18369Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18369 raw18369Labels permutation270 permutation3
    mixedMoment B raw18369step0 raw18369step0Labels = mixedMoment B raw18369step1 raw18369step1Labels := by
      have ha : raw18369step1 = raw18369step0 := by apply Matrix.ext; unfold raw18369step1 raw18369step0; decide +kernel
      have hl : raw18369step0Labels = labelEmbedding6 ∘ raw18369step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18369step0 raw18369step0Labels raw18369step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw18370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18370step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18370step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18370step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18370step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18370 raw18370Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw18370 raw18370Labels = mixedMoment B raw18370step0 raw18370step0Labels := by
      have ha : raw18370step0 = (fun i j => raw18370 (permutation502 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18370step0 raw18370; decide +kernel
      have hl : raw18370step0Labels = raw18370Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18370 raw18370Labels permutation502 permutation3
    mixedMoment B raw18370step0 raw18370step0Labels = mixedMoment B raw18370step1 raw18370step1Labels := by
      have ha : raw18370step1 = -raw18370step0 := by apply Matrix.ext; change ∀ i j, raw18370step1 i j = -(raw18370step0 i j); unfold raw18370step1 raw18370step0; decide +kernel
      have hl : raw18370step1Labels = raw18370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18370step1 raw18370step1Labels = mixedMoment B raw18370step2 raw18370step2Labels := by
      have ha : raw18370step2 = raw18370step1 := by apply Matrix.ext; unfold raw18370step2 raw18370step1; decide +kernel
      have hl : raw18370step1Labels = labelEmbedding6 ∘ raw18370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18370step1 raw18370step1Labels raw18370step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw18371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw18371step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18371step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18371 raw18371Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw18371 raw18371Labels = mixedMoment B raw18371step0 raw18371step0Labels := by
      have hz : ∀ j, raw18371 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18371step0 = (fun i j => raw18371 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18371step0 raw18371; decide +kernel
      have hl : raw18371step0Labels = raw18371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18371 raw18371Labels permutation520 hz
    mixedMoment B raw18371step0 raw18371step0Labels = mixedMoment B raw18371step1 raw18371step1Labels := by
      have ha : raw18371step1 = (fun i j => raw18371step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18371step1 raw18371step0; decide +kernel
      have hl : raw18371step1Labels = raw18371step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18371step0 raw18371step0Labels permutation33 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw18372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18372step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18372step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18372step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18372step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18372 raw18372Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18372 raw18372Labels = mixedMoment B raw18372step0 raw18372step0Labels := by
      have ha : raw18372step0 = (fun i j => raw18372 (permutation498 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18372step0 raw18372; decide +kernel
      have hl : raw18372step0Labels = raw18372Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18372 raw18372Labels permutation498 permutation3
    mixedMoment B raw18372step0 raw18372step0Labels = mixedMoment B raw18372step1 raw18372step1Labels := by
      have ha : raw18372step1 = -raw18372step0 := by apply Matrix.ext; change ∀ i j, raw18372step1 i j = -(raw18372step0 i j); unfold raw18372step1 raw18372step0; decide +kernel
      have hl : raw18372step1Labels = raw18372step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18372step1 raw18372step1Labels = mixedMoment B raw18372step2 raw18372step2Labels := by
      have ha : raw18372step2 = raw18372step1 := by apply Matrix.ext; unfold raw18372step2 raw18372step1; decide +kernel
      have hl : raw18372step1Labels = labelEmbedding6 ∘ raw18372step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18372step1 raw18372step1Labels raw18372step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw18373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18373step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18373step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18373 raw18373Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18373 raw18373Labels = mixedMoment B raw18373step0 raw18373step0Labels := by
      have ha : raw18373step0 = (fun i j => raw18373 (permutation269 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18373step0 raw18373; decide +kernel
      have hl : raw18373step0Labels = raw18373Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18373 raw18373Labels permutation269 permutation3
    mixedMoment B raw18373step0 raw18373step0Labels = mixedMoment B raw18373step1 raw18373step1Labels := by
      have ha : raw18373step1 = raw18373step0 := by apply Matrix.ext; unfold raw18373step1 raw18373step0; decide +kernel
      have hl : raw18373step0Labels = labelEmbedding6 ∘ raw18373step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18373step0 raw18373step0Labels raw18373step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw18374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18374step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18374step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18374step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18374 raw18374Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw18374 raw18374Labels = mixedMoment B raw18374step0 raw18374step0Labels := by
      have ha : raw18374step0 = (fun i j => raw18374 (permutation566 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18374step0 raw18374; decide +kernel
      have hl : raw18374step0Labels = raw18374Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18374 raw18374Labels permutation566 permutation3
    mixedMoment B raw18374step0 raw18374step0Labels = mixedMoment B raw18374step1 raw18374step1Labels := by
      have ha : raw18374step1 = -raw18374step0 := by apply Matrix.ext; change ∀ i j, raw18374step1 i j = -(raw18374step0 i j); unfold raw18374step1 raw18374step0; decide +kernel
      have hl : raw18374step1Labels = raw18374step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18374step1 raw18374step1Labels = mixedMoment B raw18374step2 raw18374step2Labels := by
      have ha : raw18374step2 = raw18374step1 := by apply Matrix.ext; unfold raw18374step2 raw18374step1; decide +kernel
      have hl : raw18374step1Labels = labelEmbedding6 ∘ raw18374step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18374step1 raw18374step1Labels raw18374step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw18375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw18375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18375 raw18375Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw18375 raw18375Labels = mixedMoment B raw18375step0 raw18375step0Labels := by
      have hz : ∀ j, raw18375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18375step0 = (fun i j => raw18375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18375step0 raw18375; decide +kernel
      have hl : raw18375step0Labels = raw18375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18375 raw18375Labels permutation434 hz
    mixedMoment B raw18375step0 raw18375step0Labels = mixedMoment B raw18375step1 raw18375step1Labels := by
      have ha : raw18375step1 = (fun i j => raw18375step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18375step1 raw18375step0; decide +kernel
      have hl : raw18375step1Labels = raw18375step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18375step0 raw18375step0Labels permutation33 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw18376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw18376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18376step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18376step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18376step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18376step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18376 raw18376Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18376 raw18376Labels = mixedMoment B raw18376step0 raw18376step0Labels := by
      have ha : raw18376step0 = (fun i j => raw18376 (permutation562 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18376step0 raw18376; decide +kernel
      have hl : raw18376step0Labels = raw18376Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18376 raw18376Labels permutation562 permutation3
    mixedMoment B raw18376step0 raw18376step0Labels = mixedMoment B raw18376step1 raw18376step1Labels := by
      have ha : raw18376step1 = -raw18376step0 := by apply Matrix.ext; change ∀ i j, raw18376step1 i j = -(raw18376step0 i j); unfold raw18376step1 raw18376step0; decide +kernel
      have hl : raw18376step1Labels = raw18376step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18376step1 raw18376step1Labels = mixedMoment B raw18376step2 raw18376step2Labels := by
      have ha : raw18376step2 = raw18376step1 := by apply Matrix.ext; unfold raw18376step2 raw18376step1; decide +kernel
      have hl : raw18376step1Labels = labelEmbedding6 ∘ raw18376step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18376step1 raw18376step1Labels raw18376step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw18377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18377step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18377 raw18377Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw18377 raw18377Labels = mixedMoment B raw18377step0 raw18377step0Labels := by
      have ha : raw18377step0 = (fun i j => raw18377 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18377step0 raw18377; decide +kernel
      have hl : raw18377step0Labels = raw18377Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18377 raw18377Labels permutation265 permutation3
    mixedMoment B raw18377step0 raw18377step0Labels = mixedMoment B raw18377step1 raw18377step1Labels := by
      have ha : raw18377step1 = raw18377step0 := by apply Matrix.ext; unfold raw18377step1 raw18377step0; decide +kernel
      have hl : raw18377step0Labels = labelEmbedding6 ∘ raw18377step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18377step0 raw18377step0Labels raw18377step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw18378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18378 raw18378Labels = mixedMoment B node5422 node5422Labels := by
  calc
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw18379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18379 raw18379Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18379 raw18379Labels = mixedMoment B raw18379step0 raw18379step0Labels := by
      have hz : ∀ j, raw18379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18379step0 = (fun i j => raw18379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18379step0 raw18379; decide +kernel
      have hl : raw18379step0Labels = raw18379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18379 raw18379Labels permutation434 hz
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw18380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw18380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18380 raw18380Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18380 raw18380Labels = mixedMoment B raw18380step0 raw18380step0Labels := by
      have hz : ∀ j, raw18380 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18380step0 = (fun i j => raw18380 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18380step0 raw18380; decide +kernel
      have hl : raw18380step0Labels = raw18380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18380 raw18380Labels permutation520 hz
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw18381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18381step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18381step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18381 raw18381Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18381 raw18381Labels = mixedMoment B raw18381step0 raw18381step0Labels := by
      have ha : raw18381step0 = (fun i j => raw18381 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18381step0 raw18381; decide +kernel
      have hl : raw18381step0Labels = raw18381Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18381 raw18381Labels permutation265 permutation3
    mixedMoment B raw18381step0 raw18381step0Labels = mixedMoment B raw18381step1 raw18381step1Labels := by
      have ha : raw18381step1 = raw18381step0 := by apply Matrix.ext; unfold raw18381step1 raw18381step0; decide +kernel
      have hl : raw18381step0Labels = labelEmbedding6 ∘ raw18381step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18381step0 raw18381step0Labels raw18381step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw18382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18382 raw18382Labels = mixedMoment B node5497 node5497Labels := by
  calc
    mixedMoment B raw18382 raw18382Labels = mixedMoment B raw18382step0 raw18382step0Labels := by
      have ha : raw18382step0 = (fun i j => raw18382 (permutation293 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18382step0 raw18382; decide +kernel
      have hl : raw18382step0Labels = raw18382Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18382 raw18382Labels permutation293 permutation2
    _ = mixedMoment B node5497 node5497Labels := by rfl

def raw18383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18383 raw18383Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw18383 raw18383Labels = mixedMoment B raw18383step0 raw18383step0Labels := by
      have ha : raw18383step0 = (fun i j => raw18383 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18383step0 raw18383; decide +kernel
      have hl : raw18383step0Labels = raw18383Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18383 raw18383Labels permutation268 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

def raw18384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18384 raw18384Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw18384 raw18384Labels = mixedMoment B raw18384step0 raw18384step0Labels := by
      have hz : ∀ j, raw18384 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18384step0 = (fun i j => raw18384 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18384step0 raw18384; decide +kernel
      have hl : raw18384step0Labels = raw18384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18384 raw18384Labels permutation590 hz
    mixedMoment B raw18384step0 raw18384step0Labels = mixedMoment B raw18384step1 raw18384step1Labels := by
      have ha : raw18384step1 = (fun i j => raw18384step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18384step1 raw18384step0; decide +kernel
      have hl : raw18384step1Labels = raw18384step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18384step0 raw18384step0Labels permutation126 permutation2
    mixedMoment B raw18384step1 raw18384step1Labels = mixedMoment B raw18384step2 raw18384step2Labels := by
      have ha : raw18384step2 = -raw18384step1 := by apply Matrix.ext; change ∀ i j, raw18384step2 i j = -(raw18384step1 i j); unfold raw18384step2 raw18384step1; decide +kernel
      have hl : raw18384step2Labels = raw18384step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw18385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18385step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18385step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18385 raw18385Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw18385 raw18385Labels = mixedMoment B raw18385step0 raw18385step0Labels := by
      have ha : raw18385step0 = (fun i j => raw18385 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18385step0 raw18385; decide +kernel
      have hl : raw18385step0Labels = raw18385Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18385 raw18385Labels permutation152 permutation3
    mixedMoment B raw18385step0 raw18385step0Labels = mixedMoment B raw18385step1 raw18385step1Labels := by
      have ha : raw18385step1 = raw18385step0 := by apply Matrix.ext; unfold raw18385step1 raw18385step0; decide +kernel
      have hl : raw18385step0Labels = labelEmbedding6 ∘ raw18385step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18385step0 raw18385step0Labels raw18385step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw18386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18386step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18386 raw18386Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18386 raw18386Labels = mixedMoment B raw18386step0 raw18386step0Labels := by
      have ha : raw18386step0 = (fun i j => raw18386 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18386step0 raw18386; decide +kernel
      have hl : raw18386step0Labels = raw18386Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18386 raw18386Labels permutation176 permutation3
    mixedMoment B raw18386step0 raw18386step0Labels = mixedMoment B raw18386step1 raw18386step1Labels := by
      have ha : raw18386step1 = raw18386step0 := by apply Matrix.ext; unfold raw18386step1 raw18386step0; decide +kernel
      have hl : raw18386step0Labels = labelEmbedding6 ∘ raw18386step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18386step0 raw18386step0Labels raw18386step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18387step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18387step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18387step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18387step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18387 raw18387Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18387 raw18387Labels = mixedMoment B raw18387step0 raw18387step0Labels := by
      have ha : raw18387step0 = (fun i j => raw18387 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18387step0 raw18387; decide +kernel
      have hl : raw18387step0Labels = raw18387Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18387 raw18387Labels permutation234 permutation5
    mixedMoment B raw18387step0 raw18387step0Labels = mixedMoment B raw18387step1 raw18387step1Labels := by
      have ha : raw18387step1 = -raw18387step0 := by apply Matrix.ext; change ∀ i j, raw18387step1 i j = -(raw18387step0 i j); unfold raw18387step1 raw18387step0; decide +kernel
      have hl : raw18387step1Labels = raw18387step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18387step1 raw18387step1Labels = mixedMoment B raw18387step2 raw18387step2Labels := by
      have ha : raw18387step2 = raw18387step1 := by apply Matrix.ext; unfold raw18387step2 raw18387step1; decide +kernel
      have hl : raw18387step1Labels = labelEmbedding8 ∘ raw18387step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18387step1 raw18387step1Labels raw18387step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18388step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18388step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18388 raw18388Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw18388 raw18388Labels = mixedMoment B raw18388step0 raw18388step0Labels := by
      have hz : ∀ j, raw18388 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18388step0 = (fun i j => raw18388 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18388step0 raw18388; decide +kernel
      have hl : raw18388step0Labels = raw18388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18388 raw18388Labels permutation590 hz
    mixedMoment B raw18388step0 raw18388step0Labels = mixedMoment B raw18388step1 raw18388step1Labels := by
      have ha : raw18388step1 = (fun i j => raw18388step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18388step1 raw18388step0; decide +kernel
      have hl : raw18388step1Labels = raw18388step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18388step0 raw18388step0Labels permutation32 permutation3
    mixedMoment B raw18388step1 raw18388step1Labels = mixedMoment B raw18388step2 raw18388step2Labels := by
      have ha : raw18388step2 = raw18388step1 := by apply Matrix.ext; unfold raw18388step2 raw18388step1; decide +kernel
      have hl : raw18388step1Labels = labelEmbedding6 ∘ raw18388step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18388step1 raw18388step1Labels raw18388step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw18389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18389step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18389 raw18389Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw18389 raw18389Labels = mixedMoment B raw18389step0 raw18389step0Labels := by
      have ha : raw18389step0 = (fun i j => raw18389 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18389step0 raw18389; decide +kernel
      have hl : raw18389step0Labels = raw18389Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18389 raw18389Labels permutation161 permutation3
    mixedMoment B raw18389step0 raw18389step0Labels = mixedMoment B raw18389step1 raw18389step1Labels := by
      have ha : raw18389step1 = raw18389step0 := by apply Matrix.ext; unfold raw18389step1 raw18389step0; decide +kernel
      have hl : raw18389step0Labels = labelEmbedding6 ∘ raw18389step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18389step0 raw18389step0Labels raw18389step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw18390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18390step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18390 raw18390Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw18390 raw18390Labels = mixedMoment B raw18390step0 raw18390step0Labels := by
      have ha : raw18390step0 = (fun i j => raw18390 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18390step0 raw18390; decide +kernel
      have hl : raw18390step0Labels = raw18390Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18390 raw18390Labels permutation161 permutation3
    mixedMoment B raw18390step0 raw18390step0Labels = mixedMoment B raw18390step1 raw18390step1Labels := by
      have ha : raw18390step1 = raw18390step0 := by apply Matrix.ext; unfold raw18390step1 raw18390step0; decide +kernel
      have hl : raw18390step0Labels = labelEmbedding6 ∘ raw18390step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18390step0 raw18390step0Labels raw18390step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw18391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18391step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18391step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18391step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18391 raw18391Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18391 raw18391Labels = mixedMoment B raw18391step0 raw18391step0Labels := by
      have ha : raw18391step0 = (fun i j => raw18391 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18391step0 raw18391; decide +kernel
      have hl : raw18391step0Labels = raw18391Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18391 raw18391Labels permutation227 permutation5
    mixedMoment B raw18391step0 raw18391step0Labels = mixedMoment B raw18391step1 raw18391step1Labels := by
      have ha : raw18391step1 = -raw18391step0 := by apply Matrix.ext; change ∀ i j, raw18391step1 i j = -(raw18391step0 i j); unfold raw18391step1 raw18391step0; decide +kernel
      have hl : raw18391step1Labels = raw18391step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18391step1 raw18391step1Labels = mixedMoment B raw18391step2 raw18391step2Labels := by
      have ha : raw18391step2 = raw18391step1 := by apply Matrix.ext; unfold raw18391step2 raw18391step1; decide +kernel
      have hl : raw18391step1Labels = labelEmbedding8 ∘ raw18391step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18391step1 raw18391step1Labels raw18391step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw18392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18392step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18392step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18392step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18392 raw18392Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18392 raw18392Labels = mixedMoment B raw18392step0 raw18392step0Labels := by
      have hz : ∀ j, raw18392 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18392step0 = (fun i j => raw18392 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18392step0 raw18392; decide +kernel
      have hl : raw18392step0Labels = raw18392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18392 raw18392Labels permutation590 hz
    mixedMoment B raw18392step0 raw18392step0Labels = mixedMoment B raw18392step1 raw18392step1Labels := by
      have ha : raw18392step1 = (fun i j => raw18392step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18392step1 raw18392step0; decide +kernel
      have hl : raw18392step1Labels = raw18392step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18392step0 raw18392step0Labels permutation35 permutation3
    mixedMoment B raw18392step1 raw18392step1Labels = mixedMoment B raw18392step2 raw18392step2Labels := by
      have ha : raw18392step2 = raw18392step1 := by apply Matrix.ext; unfold raw18392step2 raw18392step1; decide +kernel
      have hl : raw18392step1Labels = labelEmbedding6 ∘ raw18392step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18392step1 raw18392step1Labels raw18392step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18393step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18393 raw18393Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw18393 raw18393Labels = mixedMoment B raw18393step0 raw18393step0Labels := by
      have ha : raw18393step0 = (fun i j => raw18393 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18393step0 raw18393; decide +kernel
      have hl : raw18393step0Labels = raw18393Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18393 raw18393Labels permutation155 permutation3
    mixedMoment B raw18393step0 raw18393step0Labels = mixedMoment B raw18393step1 raw18393step1Labels := by
      have ha : raw18393step1 = raw18393step0 := by apply Matrix.ext; unfold raw18393step1 raw18393step0; decide +kernel
      have hl : raw18393step0Labels = labelEmbedding6 ∘ raw18393step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18393step0 raw18393step0Labels raw18393step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw18394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18394step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18394 raw18394Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw18394 raw18394Labels = mixedMoment B raw18394step0 raw18394step0Labels := by
      have ha : raw18394step0 = (fun i j => raw18394 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18394step0 raw18394; decide +kernel
      have hl : raw18394step0Labels = raw18394Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18394 raw18394Labels permutation155 permutation3
    mixedMoment B raw18394step0 raw18394step0Labels = mixedMoment B raw18394step1 raw18394step1Labels := by
      have ha : raw18394step1 = raw18394step0 := by apply Matrix.ext; unfold raw18394step1 raw18394step0; decide +kernel
      have hl : raw18394step0Labels = labelEmbedding6 ∘ raw18394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18394step0 raw18394step0Labels raw18394step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw18395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18395step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18395 raw18395Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw18395 raw18395Labels = mixedMoment B raw18395step0 raw18395step0Labels := by
      have ha : raw18395step0 = (fun i j => raw18395 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18395step0 raw18395; decide +kernel
      have hl : raw18395step0Labels = raw18395Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18395 raw18395Labels permutation155 permutation3
    mixedMoment B raw18395step0 raw18395step0Labels = mixedMoment B raw18395step1 raw18395step1Labels := by
      have ha : raw18395step1 = raw18395step0 := by apply Matrix.ext; unfold raw18395step1 raw18395step0; decide +kernel
      have hl : raw18395step0Labels = labelEmbedding6 ∘ raw18395step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18395step0 raw18395step0Labels raw18395step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw18396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18396step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18396 raw18396Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18396 raw18396Labels = mixedMoment B raw18396step0 raw18396step0Labels := by
      have ha : raw18396step0 = (fun i j => raw18396 (permutation165 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18396step0 raw18396; decide +kernel
      have hl : raw18396step0Labels = raw18396Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18396 raw18396Labels permutation165 permutation3
    mixedMoment B raw18396step0 raw18396step0Labels = mixedMoment B raw18396step1 raw18396step1Labels := by
      have ha : raw18396step1 = raw18396step0 := by apply Matrix.ext; unfold raw18396step1 raw18396step0; decide +kernel
      have hl : raw18396step0Labels = labelEmbedding6 ∘ raw18396step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18396step0 raw18396step0Labels raw18396step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw18397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw18397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18397step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18397step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18397 raw18397Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18397 raw18397Labels = mixedMoment B raw18397step0 raw18397step0Labels := by
      have hz : ∀ j, raw18397 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18397step0 = (fun i j => raw18397 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18397step0 raw18397; decide +kernel
      have hl : raw18397step0Labels = raw18397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18397 raw18397Labels permutation590 hz
    mixedMoment B raw18397step0 raw18397step0Labels = mixedMoment B raw18397step1 raw18397step1Labels := by
      have ha : raw18397step1 = (fun i j => raw18397step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18397step1 raw18397step0; decide +kernel
      have hl : raw18397step1Labels = raw18397step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18397step0 raw18397step0Labels permutation33 permutation3
    mixedMoment B raw18397step1 raw18397step1Labels = mixedMoment B raw18397step2 raw18397step2Labels := by
      have ha : raw18397step2 = raw18397step1 := by apply Matrix.ext; unfold raw18397step2 raw18397step1; decide +kernel
      have hl : raw18397step1Labels = labelEmbedding6 ∘ raw18397step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18397step1 raw18397step1Labels raw18397step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw18398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18398step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18398 raw18398Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw18398 raw18398Labels = mixedMoment B raw18398step0 raw18398step0Labels := by
      have ha : raw18398step0 = (fun i j => raw18398 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18398step0 raw18398; decide +kernel
      have hl : raw18398step0Labels = raw18398Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18398 raw18398Labels permutation153 permutation3
    mixedMoment B raw18398step0 raw18398step0Labels = mixedMoment B raw18398step1 raw18398step1Labels := by
      have ha : raw18398step1 = raw18398step0 := by apply Matrix.ext; unfold raw18398step1 raw18398step0; decide +kernel
      have hl : raw18398step0Labels = labelEmbedding6 ∘ raw18398step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18398step0 raw18398step0Labels raw18398step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw18399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18399step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18399step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18399 raw18399Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw18399 raw18399Labels = mixedMoment B raw18399step0 raw18399step0Labels := by
      have ha : raw18399step0 = (fun i j => raw18399 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18399step0 raw18399; decide +kernel
      have hl : raw18399step0Labels = raw18399Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18399 raw18399Labels permutation153 permutation3
    mixedMoment B raw18399step0 raw18399step0Labels = mixedMoment B raw18399step1 raw18399step1Labels := by
      have ha : raw18399step1 = raw18399step0 := by apply Matrix.ext; unfold raw18399step1 raw18399step0; decide +kernel
      have hl : raw18399step0Labels = labelEmbedding6 ∘ raw18399step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18399step0 raw18399step0Labels raw18399step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw18400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18400step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18400 raw18400Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw18400 raw18400Labels = mixedMoment B raw18400step0 raw18400step0Labels := by
      have ha : raw18400step0 = (fun i j => raw18400 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18400step0 raw18400; decide +kernel
      have hl : raw18400step0Labels = raw18400Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18400 raw18400Labels permutation153 permutation3
    mixedMoment B raw18400step0 raw18400step0Labels = mixedMoment B raw18400step1 raw18400step1Labels := by
      have ha : raw18400step1 = raw18400step0 := by apply Matrix.ext; unfold raw18400step1 raw18400step0; decide +kernel
      have hl : raw18400step0Labels = labelEmbedding6 ∘ raw18400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18400step0 raw18400step0Labels raw18400step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw18401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw18401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18401step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18401step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18401 raw18401Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18401 raw18401Labels = mixedMoment B raw18401step0 raw18401step0Labels := by
      have hz : ∀ j, raw18401 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18401step0 = (fun i j => raw18401 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18401step0 raw18401; decide +kernel
      have hl : raw18401step0Labels = raw18401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18401 raw18401Labels permutation590 hz
    mixedMoment B raw18401step0 raw18401step0Labels = mixedMoment B raw18401step1 raw18401step1Labels := by
      have ha : raw18401step1 = (fun i j => raw18401step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18401step1 raw18401step0; decide +kernel
      have hl : raw18401step1Labels = raw18401step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18401step0 raw18401step0Labels permutation32 permutation3
    mixedMoment B raw18401step1 raw18401step1Labels = mixedMoment B raw18401step2 raw18401step2Labels := by
      have ha : raw18401step2 = raw18401step1 := by apply Matrix.ext; unfold raw18401step2 raw18401step1; decide +kernel
      have hl : raw18401step1Labels = labelEmbedding6 ∘ raw18401step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18401step1 raw18401step1Labels raw18401step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw18402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18402step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18402step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18402 raw18402Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw18402 raw18402Labels = mixedMoment B raw18402step0 raw18402step0Labels := by
      have ha : raw18402step0 = (fun i j => raw18402 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18402step0 raw18402; decide +kernel
      have hl : raw18402step0Labels = raw18402Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18402 raw18402Labels permutation158 permutation3
    mixedMoment B raw18402step0 raw18402step0Labels = mixedMoment B raw18402step1 raw18402step1Labels := by
      have ha : raw18402step1 = raw18402step0 := by apply Matrix.ext; unfold raw18402step1 raw18402step0; decide +kernel
      have hl : raw18402step0Labels = labelEmbedding6 ∘ raw18402step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18402step0 raw18402step0Labels raw18402step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw18403 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18403step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18403 raw18403Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18403 raw18403Labels = mixedMoment B raw18403step0 raw18403step0Labels := by
      have ha : raw18403step0 = (fun i j => raw18403 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18403step0 raw18403; decide +kernel
      have hl : raw18403step0Labels = raw18403Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18403 raw18403Labels permutation152 permutation6
    mixedMoment B raw18403step0 raw18403step0Labels = mixedMoment B raw18403step1 raw18403step1Labels := by
      have ha : raw18403step1 = raw18403step0 := by apply Matrix.ext; unfold raw18403step1 raw18403step0; decide +kernel
      have hl : raw18403step0Labels = labelEmbedding9 ∘ raw18403step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18403step0 raw18403step0Labels raw18403step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw18404 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18404step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18404step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18404 raw18404Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw18404 raw18404Labels = mixedMoment B raw18404step0 raw18404step0Labels := by
      have hz : ∀ j, raw18404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18404step0 = (fun i j => raw18404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18404step0 raw18404; decide +kernel
      have hl : raw18404step0Labels = raw18404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18404 raw18404Labels permutation346 hz
    mixedMoment B raw18404step0 raw18404step0Labels = mixedMoment B raw18404step1 raw18404step1Labels := by
      have ha : raw18404step1 = (fun i j => raw18404step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18404step1 raw18404step0; decide +kernel
      have hl : raw18404step1Labels = raw18404step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18404step0 raw18404step0Labels permutation36 permutation7
    mixedMoment B raw18404step1 raw18404step1Labels = mixedMoment B raw18404step2 raw18404step2Labels := by
      have ha : raw18404step2 = raw18404step1 := by apply Matrix.ext; unfold raw18404step2 raw18404step1; decide +kernel
      have hl : raw18404step1Labels = labelEmbedding10 ∘ raw18404step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18404step1 raw18404step1Labels raw18404step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw18405 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18405 raw18405Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw18405 raw18405Labels = mixedMoment B raw18405step0 raw18405step0Labels := by
      have ha : raw18405step0 = (fun i j => raw18405 (permutation504 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18405step0 raw18405; decide +kernel
      have hl : raw18405step0Labels = raw18405Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18405 raw18405Labels permutation504 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw18406 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18406step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18406 raw18406Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw18406 raw18406Labels = mixedMoment B raw18406step0 raw18406step0Labels := by
      have ha : raw18406step0 = (fun i j => raw18406 (permutation568 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18406step0 raw18406; decide +kernel
      have hl : raw18406step0Labels = raw18406Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18406 raw18406Labels permutation568 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw18407 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18407step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18407 raw18407Labels = mixedMoment B node5479 node5479Labels := by
  calc
    mixedMoment B raw18407 raw18407Labels = mixedMoment B raw18407step0 raw18407step0Labels := by
      have ha : raw18407step0 = (fun i j => raw18407 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18407step0 raw18407; decide +kernel
      have hl : raw18407step0Labels = raw18407Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18407 raw18407Labels permutation152 permutation7
    mixedMoment B raw18407step0 raw18407step0Labels = mixedMoment B raw18407step1 raw18407step1Labels := by
      have ha : raw18407step1 = raw18407step0 := by apply Matrix.ext; unfold raw18407step1 raw18407step0; decide +kernel
      have hl : raw18407step0Labels = labelEmbedding10 ∘ raw18407step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18407step0 raw18407step0Labels raw18407step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5479 node5479Labels := by rfl

def raw18408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18408step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18408step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18408step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18408 raw18408Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw18408 raw18408Labels = mixedMoment B raw18408step0 raw18408step0Labels := by
      have ha : raw18408step0 = (fun i j => raw18408 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18408step0 raw18408; decide +kernel
      have hl : raw18408step0Labels = raw18408Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18408 raw18408Labels permutation212 permutation4
    mixedMoment B raw18408step0 raw18408step0Labels = mixedMoment B raw18408step1 raw18408step1Labels := by
      have ha : raw18408step1 = -raw18408step0 := by apply Matrix.ext; change ∀ i j, raw18408step1 i j = -(raw18408step0 i j); unfold raw18408step1 raw18408step0; decide +kernel
      have hl : raw18408step1Labels = raw18408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18408step1 raw18408step1Labels = mixedMoment B raw18408step2 raw18408step2Labels := by
      have ha : raw18408step2 = raw18408step1 := by apply Matrix.ext; unfold raw18408step2 raw18408step1; decide +kernel
      have hl : raw18408step1Labels = labelEmbedding7 ∘ raw18408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18408step1 raw18408step1Labels raw18408step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw18409 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18409step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18409step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18409 raw18409Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18409 raw18409Labels = mixedMoment B raw18409step0 raw18409step0Labels := by
      have hz : ∀ j, raw18409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18409step0 = (fun i j => raw18409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18409step0 raw18409; decide +kernel
      have hl : raw18409step0Labels = raw18409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18409 raw18409Labels permutation346 hz
    mixedMoment B raw18409step0 raw18409step0Labels = mixedMoment B raw18409step1 raw18409step1Labels := by
      have ha : raw18409step1 = (fun i j => raw18409step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18409step1 raw18409step0; decide +kernel
      have hl : raw18409step1Labels = raw18409step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18409step0 raw18409step0Labels permutation32 permutation6
    mixedMoment B raw18409step1 raw18409step1Labels = mixedMoment B raw18409step2 raw18409step2Labels := by
      have ha : raw18409step2 = raw18409step1 := by apply Matrix.ext; unfold raw18409step2 raw18409step1; decide +kernel
      have hl : raw18409step1Labels = labelEmbedding9 ∘ raw18409step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18409step1 raw18409step1Labels raw18409step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw18410 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18410step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18410step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18410step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18410step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18410 raw18410Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18410 raw18410Labels = mixedMoment B raw18410step0 raw18410step0Labels := by
      have ha : raw18410step0 = (fun i j => raw18410 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18410step0 raw18410; decide +kernel
      have hl : raw18410step0Labels = raw18410Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18410 raw18410Labels permutation212 permutation4
    mixedMoment B raw18410step0 raw18410step0Labels = mixedMoment B raw18410step1 raw18410step1Labels := by
      have ha : raw18410step1 = -raw18410step0 := by apply Matrix.ext; change ∀ i j, raw18410step1 i j = -(raw18410step0 i j); unfold raw18410step1 raw18410step0; decide +kernel
      have hl : raw18410step1Labels = raw18410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18410step1 raw18410step1Labels = mixedMoment B raw18410step2 raw18410step2Labels := by
      have ha : raw18410step2 = raw18410step1 := by apply Matrix.ext; unfold raw18410step2 raw18410step1; decide +kernel
      have hl : raw18410step1Labels = labelEmbedding7 ∘ raw18410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18410step1 raw18410step1Labels raw18410step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw18411 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18411step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18411step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18411step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18411step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18411 raw18411Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18411 raw18411Labels = mixedMoment B raw18411step0 raw18411step0Labels := by
      have ha : raw18411step0 = (fun i j => raw18411 (permutation234 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18411step0 raw18411; decide +kernel
      have hl : raw18411step0Labels = raw18411Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18411 raw18411Labels permutation234 permutation4
    mixedMoment B raw18411step0 raw18411step0Labels = mixedMoment B raw18411step1 raw18411step1Labels := by
      have ha : raw18411step1 = -raw18411step0 := by apply Matrix.ext; change ∀ i j, raw18411step1 i j = -(raw18411step0 i j); unfold raw18411step1 raw18411step0; decide +kernel
      have hl : raw18411step1Labels = raw18411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18411step1 raw18411step1Labels = mixedMoment B raw18411step2 raw18411step2Labels := by
      have ha : raw18411step2 = raw18411step1 := by apply Matrix.ext; unfold raw18411step2 raw18411step1; decide +kernel
      have hl : raw18411step1Labels = labelEmbedding7 ∘ raw18411step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18411step1 raw18411step1Labels raw18411step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw18412 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18412step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18412step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18412 raw18412Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw18412 raw18412Labels = mixedMoment B raw18412step0 raw18412step0Labels := by
      have ha : raw18412step0 = (fun i j => raw18412 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18412step0 raw18412; decide +kernel
      have hl : raw18412step0Labels = raw18412Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18412 raw18412Labels permutation152 permutation6
    mixedMoment B raw18412step0 raw18412step0Labels = mixedMoment B raw18412step1 raw18412step1Labels := by
      have ha : raw18412step1 = raw18412step0 := by apply Matrix.ext; unfold raw18412step1 raw18412step0; decide +kernel
      have hl : raw18412step0Labels = labelEmbedding9 ∘ raw18412step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18412step0 raw18412step0Labels raw18412step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw18413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18413step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18413step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18413step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18413step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18413 raw18413Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw18413 raw18413Labels = mixedMoment B raw18413step0 raw18413step0Labels := by
      have ha : raw18413step0 = (fun i j => raw18413 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18413step0 raw18413; decide +kernel
      have hl : raw18413step0Labels = raw18413Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18413 raw18413Labels permutation161 permutation4
    mixedMoment B raw18413step0 raw18413step0Labels = mixedMoment B raw18413step1 raw18413step1Labels := by
      have ha : raw18413step1 = -raw18413step0 := by apply Matrix.ext; change ∀ i j, raw18413step1 i j = -(raw18413step0 i j); unfold raw18413step1 raw18413step0; decide +kernel
      have hl : raw18413step1Labels = raw18413step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18413step1 raw18413step1Labels = mixedMoment B raw18413step2 raw18413step2Labels := by
      have ha : raw18413step2 = raw18413step1 := by apply Matrix.ext; unfold raw18413step2 raw18413step1; decide +kernel
      have hl : raw18413step1Labels = labelEmbedding7 ∘ raw18413step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18413step1 raw18413step1Labels raw18413step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw18414 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18414step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18414step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18414step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18414step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18414 raw18414Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18414 raw18414Labels = mixedMoment B raw18414step0 raw18414step0Labels := by
      have ha : raw18414step0 = (fun i j => raw18414 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18414step0 raw18414; decide +kernel
      have hl : raw18414step0Labels = raw18414Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18414 raw18414Labels permutation161 permutation4
    mixedMoment B raw18414step0 raw18414step0Labels = mixedMoment B raw18414step1 raw18414step1Labels := by
      have ha : raw18414step1 = -raw18414step0 := by apply Matrix.ext; change ∀ i j, raw18414step1 i j = -(raw18414step0 i j); unfold raw18414step1 raw18414step0; decide +kernel
      have hl : raw18414step1Labels = raw18414step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18414step1 raw18414step1Labels = mixedMoment B raw18414step2 raw18414step2Labels := by
      have ha : raw18414step2 = raw18414step1 := by apply Matrix.ext; unfold raw18414step2 raw18414step1; decide +kernel
      have hl : raw18414step1Labels = labelEmbedding7 ∘ raw18414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18414step1 raw18414step1Labels raw18414step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw18415 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18415step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18415step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18415 raw18415Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18415 raw18415Labels = mixedMoment B raw18415step0 raw18415step0Labels := by
      have ha : raw18415step0 = (fun i j => raw18415 (permutation423 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18415step0 raw18415; decide +kernel
      have hl : raw18415step0Labels = raw18415Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18415 raw18415Labels permutation423 permutation5
    mixedMoment B raw18415step0 raw18415step0Labels = mixedMoment B raw18415step1 raw18415step1Labels := by
      have ha : raw18415step1 = raw18415step0 := by apply Matrix.ext; unfold raw18415step1 raw18415step0; decide +kernel
      have hl : raw18415step0Labels = labelEmbedding8 ∘ raw18415step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18415step0 raw18415step0Labels raw18415step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw18416 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18416step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18416 raw18416Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18416 raw18416Labels = mixedMoment B raw18416step0 raw18416step0Labels := by
      have ha : raw18416step0 = (fun i j => raw18416 (permutation421 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18416step0 raw18416; decide +kernel
      have hl : raw18416step0Labels = raw18416Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18416 raw18416Labels permutation421 permutation5
    mixedMoment B raw18416step0 raw18416step0Labels = mixedMoment B raw18416step1 raw18416step1Labels := by
      have ha : raw18416step1 = raw18416step0 := by apply Matrix.ext; unfold raw18416step1 raw18416step0; decide +kernel
      have hl : raw18416step0Labels = labelEmbedding8 ∘ raw18416step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18416step0 raw18416step0Labels raw18416step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw18417 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw18417step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18417step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18417step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18417 raw18417Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw18417 raw18417Labels = mixedMoment B raw18417step0 raw18417step0Labels := by
      have ha : raw18417step0 = (fun i j => raw18417 (permutation367 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18417step0 raw18417; decide +kernel
      have hl : raw18417step0Labels = raw18417Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18417 raw18417Labels permutation367 permutation3
    mixedMoment B raw18417step0 raw18417step0Labels = mixedMoment B raw18417step1 raw18417step1Labels := by
      have ha : raw18417step1 = -raw18417step0 := by apply Matrix.ext; change ∀ i j, raw18417step1 i j = -(raw18417step0 i j); unfold raw18417step1 raw18417step0; decide +kernel
      have hl : raw18417step1Labels = raw18417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18417step1 raw18417step1Labels = mixedMoment B raw18417step2 raw18417step2Labels := by
      have ha : raw18417step2 = raw18417step1 := by apply Matrix.ext; unfold raw18417step2 raw18417step1; decide +kernel
      have hl : raw18417step1Labels = labelEmbedding6 ∘ raw18417step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18417step1 raw18417step1Labels raw18417step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw18418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18418step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18418step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18418step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18418step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18418 raw18418Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw18418 raw18418Labels = mixedMoment B raw18418step0 raw18418step0Labels := by
      have ha : raw18418step0 = (fun i j => raw18418 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18418step0 raw18418; decide +kernel
      have hl : raw18418step0Labels = raw18418Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18418 raw18418Labels permutation164 permutation4
    mixedMoment B raw18418step0 raw18418step0Labels = mixedMoment B raw18418step1 raw18418step1Labels := by
      have ha : raw18418step1 = -raw18418step0 := by apply Matrix.ext; change ∀ i j, raw18418step1 i j = -(raw18418step0 i j); unfold raw18418step1 raw18418step0; decide +kernel
      have hl : raw18418step1Labels = raw18418step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18418step1 raw18418step1Labels = mixedMoment B raw18418step2 raw18418step2Labels := by
      have ha : raw18418step2 = raw18418step1 := by apply Matrix.ext; unfold raw18418step2 raw18418step1; decide +kernel
      have hl : raw18418step1Labels = labelEmbedding7 ∘ raw18418step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18418step1 raw18418step1Labels raw18418step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw18419 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18419step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18419step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18419step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18419step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18419 raw18419Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw18419 raw18419Labels = mixedMoment B raw18419step0 raw18419step0Labels := by
      have ha : raw18419step0 = (fun i j => raw18419 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18419step0 raw18419; decide +kernel
      have hl : raw18419step0Labels = raw18419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18419 raw18419Labels permutation164 permutation4
    mixedMoment B raw18419step0 raw18419step0Labels = mixedMoment B raw18419step1 raw18419step1Labels := by
      have ha : raw18419step1 = -raw18419step0 := by apply Matrix.ext; change ∀ i j, raw18419step1 i j = -(raw18419step0 i j); unfold raw18419step1 raw18419step0; decide +kernel
      have hl : raw18419step1Labels = raw18419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18419step1 raw18419step1Labels = mixedMoment B raw18419step2 raw18419step2Labels := by
      have ha : raw18419step2 = raw18419step1 := by apply Matrix.ext; unfold raw18419step2 raw18419step1; decide +kernel
      have hl : raw18419step1Labels = labelEmbedding7 ∘ raw18419step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18419step1 raw18419step1Labels raw18419step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw18420 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18420step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18420 raw18420Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw18420 raw18420Labels = mixedMoment B raw18420step0 raw18420step0Labels := by
      have hz : ∀ j, raw18420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18420step0 = (fun i j => raw18420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18420step0 raw18420; decide +kernel
      have hl : raw18420step0Labels = raw18420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18420 raw18420Labels permutation346 hz
    mixedMoment B raw18420step0 raw18420step0Labels = mixedMoment B raw18420step1 raw18420step1Labels := by
      have ha : raw18420step1 = (fun i j => raw18420step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18420step1 raw18420step0; decide +kernel
      have hl : raw18420step1Labels = raw18420step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18420step0 raw18420step0Labels permutation34 permutation6
    mixedMoment B raw18420step1 raw18420step1Labels = mixedMoment B raw18420step2 raw18420step2Labels := by
      have ha : raw18420step2 = raw18420step1 := by apply Matrix.ext; unfold raw18420step2 raw18420step1; decide +kernel
      have hl : raw18420step1Labels = labelEmbedding9 ∘ raw18420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18420step1 raw18420step1Labels raw18420step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw18421 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18421step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18421 raw18421Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18421 raw18421Labels = mixedMoment B raw18421step0 raw18421step0Labels := by
      have ha : raw18421step0 = (fun i j => raw18421 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18421step0 raw18421; decide +kernel
      have hl : raw18421step0Labels = raw18421Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18421 raw18421Labels permutation154 permutation6
    mixedMoment B raw18421step0 raw18421step0Labels = mixedMoment B raw18421step1 raw18421step1Labels := by
      have ha : raw18421step1 = raw18421step0 := by apply Matrix.ext; unfold raw18421step1 raw18421step0; decide +kernel
      have hl : raw18421step0Labels = labelEmbedding9 ∘ raw18421step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18421step0 raw18421step0Labels raw18421step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw18422 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18422step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18422 raw18422Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18422 raw18422Labels = mixedMoment B raw18422step0 raw18422step0Labels := by
      have ha : raw18422step0 = (fun i j => raw18422 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18422step0 raw18422; decide +kernel
      have hl : raw18422step0Labels = raw18422Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18422 raw18422Labels permutation155 permutation6
    mixedMoment B raw18422step0 raw18422step0Labels = mixedMoment B raw18422step1 raw18422step1Labels := by
      have ha : raw18422step1 = raw18422step0 := by apply Matrix.ext; unfold raw18422step1 raw18422step0; decide +kernel
      have hl : raw18422step0Labels = labelEmbedding9 ∘ raw18422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18422step0 raw18422step0Labels raw18422step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18423step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18423step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18423step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18423step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18423 raw18423Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw18423 raw18423Labels = mixedMoment B raw18423step0 raw18423step0Labels := by
      have ha : raw18423step0 = (fun i j => raw18423 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18423step0 raw18423; decide +kernel
      have hl : raw18423step0Labels = raw18423Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18423 raw18423Labels permutation158 permutation4
    mixedMoment B raw18423step0 raw18423step0Labels = mixedMoment B raw18423step1 raw18423step1Labels := by
      have ha : raw18423step1 = -raw18423step0 := by apply Matrix.ext; change ∀ i j, raw18423step1 i j = -(raw18423step0 i j); unfold raw18423step1 raw18423step0; decide +kernel
      have hl : raw18423step1Labels = raw18423step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18423step1 raw18423step1Labels = mixedMoment B raw18423step2 raw18423step2Labels := by
      have ha : raw18423step2 = raw18423step1 := by apply Matrix.ext; unfold raw18423step2 raw18423step1; decide +kernel
      have hl : raw18423step1Labels = labelEmbedding7 ∘ raw18423step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18423step1 raw18423step1Labels raw18423step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw18424 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18424step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18424step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18424step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18424step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18424 raw18424Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw18424 raw18424Labels = mixedMoment B raw18424step0 raw18424step0Labels := by
      have ha : raw18424step0 = (fun i j => raw18424 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18424step0 raw18424; decide +kernel
      have hl : raw18424step0Labels = raw18424Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18424 raw18424Labels permutation158 permutation4
    mixedMoment B raw18424step0 raw18424step0Labels = mixedMoment B raw18424step1 raw18424step1Labels := by
      have ha : raw18424step1 = -raw18424step0 := by apply Matrix.ext; change ∀ i j, raw18424step1 i j = -(raw18424step0 i j); unfold raw18424step1 raw18424step0; decide +kernel
      have hl : raw18424step1Labels = raw18424step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18424step1 raw18424step1Labels = mixedMoment B raw18424step2 raw18424step2Labels := by
      have ha : raw18424step2 = raw18424step1 := by apply Matrix.ext; unfold raw18424step2 raw18424step1; decide +kernel
      have hl : raw18424step1Labels = labelEmbedding7 ∘ raw18424step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18424step1 raw18424step1Labels raw18424step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw18425 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18425step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18425step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18425 raw18425Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw18425 raw18425Labels = mixedMoment B raw18425step0 raw18425step0Labels := by
      have hz : ∀ j, raw18425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18425step0 = (fun i j => raw18425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18425step0 raw18425; decide +kernel
      have hl : raw18425step0Labels = raw18425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18425 raw18425Labels permutation346 hz
    mixedMoment B raw18425step0 raw18425step0Labels = mixedMoment B raw18425step1 raw18425step1Labels := by
      have ha : raw18425step1 = (fun i j => raw18425step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18425step1 raw18425step0; decide +kernel
      have hl : raw18425step1Labels = raw18425step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18425step0 raw18425step0Labels permutation32 permutation6
    mixedMoment B raw18425step1 raw18425step1Labels = mixedMoment B raw18425step2 raw18425step2Labels := by
      have ha : raw18425step2 = raw18425step1 := by apply Matrix.ext; unfold raw18425step2 raw18425step1; decide +kernel
      have hl : raw18425step1Labels = labelEmbedding9 ∘ raw18425step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18425step1 raw18425step1Labels raw18425step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw18426 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18426step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18426 raw18426Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18426 raw18426Labels = mixedMoment B raw18426step0 raw18426step0Labels := by
      have ha : raw18426step0 = (fun i j => raw18426 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18426step0 raw18426; decide +kernel
      have hl : raw18426step0Labels = raw18426Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18426 raw18426Labels permutation152 permutation6
    mixedMoment B raw18426step0 raw18426step0Labels = mixedMoment B raw18426step1 raw18426step1Labels := by
      have ha : raw18426step1 = raw18426step0 := by apply Matrix.ext; unfold raw18426step1 raw18426step0; decide +kernel
      have hl : raw18426step0Labels = labelEmbedding9 ∘ raw18426step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18426step0 raw18426step0Labels raw18426step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw18427 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18427step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18427 raw18427Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18427 raw18427Labels = mixedMoment B raw18427step0 raw18427step0Labels := by
      have ha : raw18427step0 = (fun i j => raw18427 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18427step0 raw18427; decide +kernel
      have hl : raw18427step0Labels = raw18427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18427 raw18427Labels permutation153 permutation6
    mixedMoment B raw18427step0 raw18427step0Labels = mixedMoment B raw18427step1 raw18427step1Labels := by
      have ha : raw18427step1 = raw18427step0 := by apply Matrix.ext; unfold raw18427step1 raw18427step0; decide +kernel
      have hl : raw18427step0Labels = labelEmbedding9 ∘ raw18427step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18427step0 raw18427step0Labels raw18427step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18428step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18428step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18428step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18428 raw18428Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw18428 raw18428Labels = mixedMoment B raw18428step0 raw18428step0Labels := by
      have ha : raw18428step0 = (fun i j => raw18428 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18428step0 raw18428; decide +kernel
      have hl : raw18428step0Labels = raw18428Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18428 raw18428Labels permutation160 permutation4
    mixedMoment B raw18428step0 raw18428step0Labels = mixedMoment B raw18428step1 raw18428step1Labels := by
      have ha : raw18428step1 = -raw18428step0 := by apply Matrix.ext; change ∀ i j, raw18428step1 i j = -(raw18428step0 i j); unfold raw18428step1 raw18428step0; decide +kernel
      have hl : raw18428step1Labels = raw18428step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18428step1 raw18428step1Labels = mixedMoment B raw18428step2 raw18428step2Labels := by
      have ha : raw18428step2 = raw18428step1 := by apply Matrix.ext; unfold raw18428step2 raw18428step1; decide +kernel
      have hl : raw18428step1Labels = labelEmbedding7 ∘ raw18428step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18428step1 raw18428step1Labels raw18428step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw18429 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18429step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18429step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18429step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18429 raw18429Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw18429 raw18429Labels = mixedMoment B raw18429step0 raw18429step0Labels := by
      have ha : raw18429step0 = (fun i j => raw18429 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18429step0 raw18429; decide +kernel
      have hl : raw18429step0Labels = raw18429Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18429 raw18429Labels permutation160 permutation4
    mixedMoment B raw18429step0 raw18429step0Labels = mixedMoment B raw18429step1 raw18429step1Labels := by
      have ha : raw18429step1 = -raw18429step0 := by apply Matrix.ext; change ∀ i j, raw18429step1 i j = -(raw18429step0 i j); unfold raw18429step1 raw18429step0; decide +kernel
      have hl : raw18429step1Labels = raw18429step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18429step1 raw18429step1Labels = mixedMoment B raw18429step2 raw18429step2Labels := by
      have ha : raw18429step2 = raw18429step1 := by apply Matrix.ext; unfold raw18429step2 raw18429step1; decide +kernel
      have hl : raw18429step1Labels = labelEmbedding7 ∘ raw18429step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18429step1 raw18429step1Labels raw18429step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw18430 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18430step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18430 raw18430Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18430 raw18430Labels = mixedMoment B raw18430step0 raw18430step0Labels := by
      have hz : ∀ j, raw18430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18430step0 = (fun i j => raw18430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18430step0 raw18430; decide +kernel
      have hl : raw18430step0Labels = raw18430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18430 raw18430Labels permutation346 hz
    mixedMoment B raw18430step0 raw18430step0Labels = mixedMoment B raw18430step1 raw18430step1Labels := by
      have ha : raw18430step1 = (fun i j => raw18430step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18430step1 raw18430step0; decide +kernel
      have hl : raw18430step1Labels = raw18430step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18430step0 raw18430step0Labels permutation32 permutation6
    mixedMoment B raw18430step1 raw18430step1Labels = mixedMoment B raw18430step2 raw18430step2Labels := by
      have ha : raw18430step2 = raw18430step1 := by apply Matrix.ext; unfold raw18430step2 raw18430step1; decide +kernel
      have hl : raw18430step1Labels = labelEmbedding9 ∘ raw18430step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18430step1 raw18430step1Labels raw18430step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18431 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18431step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18431 raw18431Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18431 raw18431Labels = mixedMoment B raw18431step0 raw18431step0Labels := by
      have ha : raw18431step0 = (fun i j => raw18431 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18431step0 raw18431; decide +kernel
      have hl : raw18431step0Labels = raw18431Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18431 raw18431Labels permutation152 permutation6
    mixedMoment B raw18431step0 raw18431step0Labels = mixedMoment B raw18431step1 raw18431step1Labels := by
      have ha : raw18431step1 = raw18431step0 := by apply Matrix.ext; unfold raw18431step1 raw18431step0; decide +kernel
      have hl : raw18431step0Labels = labelEmbedding9 ∘ raw18431step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18431step0 raw18431step0Labels raw18431step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
