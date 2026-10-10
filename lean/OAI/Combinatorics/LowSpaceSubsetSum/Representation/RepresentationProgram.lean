import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScheduleWitness

namespace OAI

/-! # Representation runtime data without a supplied solution

The zero-target wrapper supplies layout and domain facts. Its
solution and target do not enter the runtime's input, signs or signed target.
-/

noncomputable section

namespace LowSpaceSubsetSum

structure RepresentationData (n : ℕ) where
  input : Instance n
  mixers : Fin 3 → Finset (Fin n)
  disjoint : ∀ i j, i ≠ j → Disjoint (mixers i) (mixers j)
  card : ∀ i, (mixers i).card = mixerSize n

namespace RepresentationData

variable {n : ℕ} (D : RepresentationData n)

def zeroSetup : RepresentationSetup n where
  input := { D.input with target := 0 }
  solution := ∅
  solution_weight := by simp
  mixers := D.mixers
  disjoint := D.disjoint
  card := D.card

/-- All fields are determined by the input and the random draw history. In
particular, the second layout coordinate is the actual sign mask. -/
def scheduleData (h : D.zeroSetup.PrimeHistory) (r : D.zeroSetup.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (q : ℕ) (hq : 0 < q) : RepresentationScheduleData n (2 * RepresentationSetup.blockHalf n 0) where
  input := D.input
  signs := h.1.1.1.2
  leaves := D.zeroSetup.rawLeaf h.1.1.1 h.1.1.2 h.1.2
    (D.zeroSetup.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
  lowModuli j := prefixModulus h.2.val j.succ
  firstResidues j := if j = 0 then r.2.1.val else r.2.2.val
  p0 := prefixModulus h.2.val 0
  p0_positive := prefixModulus_pos h.2 0
  q := q
  q_positive := hq
  rho0 := r.1
  capacity := compressionDictionaryCapacity n
  coordinates := D.zeroSetup.topCoordinates h.1.1.1 h.1.2
  topOrder := (D.zeroSetup.orderedMixers h.1.1.1 0).sort (· ≤ ·)

def trial (h : D.zeroSetup.PrimeHistory) (r : D.zeroSetup.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (q : ℕ) (hq : 0 < q) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin (2 * RepresentationSetup.blockHalf n 0)))) : Bool :=
  (D.scheduleData h r hn hlog q hq).run B families

end RepresentationData

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

def runtimeData : RepresentationData n := ⟨R.input, R.mixers, R.disjoint, R.card⟩

/-- Convert the successful-analysis coordinates to the actual random signs.
The finite partition and prime choices do not depend on the fixed solution. -/
def runtimeHistory (h : R.PrimeHistory) : R.runtimeData.zeroSetup.PrimeHistory :=
  ⟨⟨⟨(h.1.1.1.1, R.signMask h.1.1.1), h.1.1.2⟩, h.1.2⟩, h.2⟩

theorem runtime_schedule_eq (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (q : ℕ) (hq : 0 < q) :
    R.runtimeData.scheduleData (R.runtimeHistory h) r hn hlog q hq =
      R.scheduleData h r hn hlog q hq := by
  rfl

theorem runtime_trial_eq (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (q : ℕ) (hq : 0 < q) (B : ℕ)
    (families : Fin 4 → Array (Finset (Fin (2 * blockHalf n 0)))) :
    R.runtimeData.trial (R.runtimeHistory h) r hn hlog q hq B families =
      (R.scheduleData h r hn hlog q hq).run B families := by
  unfold RepresentationData.trial
  rw [R.runtime_schedule_eq]

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
