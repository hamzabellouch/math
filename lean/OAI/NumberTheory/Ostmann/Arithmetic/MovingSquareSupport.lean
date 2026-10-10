import OAI.NumberTheory.Ostmann.Arithmetic.MovingPairwiseSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOccurrenceUnits

namespace OAI

/-! # The explicit prime-square tests for the full moving history -/

namespace Ostmann

def MovingSlotData.CompensationPrimeData {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node s _ _ U left right =>
      (∀ b ∈ U.map value, b.Prime) ∧ (U.map value).Pairwise Nat.Coprime ∧
      (∀ b ∈ U.map value, ¬ b ∣ s.natAbs) ∧
      left.CompensationPrimeData value ∧ right.CompensationPrimeData value

/-- Equality patterns may identify samples at different nodes; only the
entries made together in one compensation vector have to be distinct. -/
def MovingSlotData.CompensationDistinct {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node _ _ _ U left right =>
      (U.map value).Pairwise Nat.Coprime ∧
      left.CompensationDistinct value ∧ right.CompensationDistinct value

def MovingSampleSlots.DistinctCompensations {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSampleSlots σ n → Prop
  | _, .leaf => True
  | n + 1, .node samples left right =>
      ((flattenMovingSlots n (movingCompensationSlots n samples)).map value).Pairwise Nat.Coprime ∧
      left.DistinctCompensations value ∧ right.DistinctCompensations value

theorem buildMovingSlotData_compensation_distinct {σ : Type*} (value : σ → ℕ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (h : samples.DistinctCompensations value) :
    (buildMovingSlotData n t small bulk samples).CompensationDistinct value := by
  induction samples with
  | leaf => trivial
  | node samples left right ihL ihR =>
    exact ⟨h.1, ihL _ _ _ h.2.1, ihR _ _ _ h.2.2⟩

/-- The manuscript's size separation proves the frequency-prime coprimality
required by the square tests. It is not an additional analytic input. -/
theorem MovingSlotData.compensationPrimeData_of_ranges {σ : Type*} (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (V : ℕ) (hlarge : ∀ i, V < value i)
    {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (hV : T.Frequencies (fun s => s.natAbs ≤ V))
    (hdistinct : T.CompensationDistinct value) : T.CompensationPrimeData value := by
  induction T with
  | leaf => trivial
  | node s CL CR U left right ihL ihR =>
    refine ⟨?_, hdistinct.1, ?_, ihL hf.2.1 hV.2.1 hdistinct.2.1,
      ihR hf.2.2 hV.2.2 hdistinct.2.2⟩
    · intro b hb
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      exact hprime i
    · intro b hb
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      exact Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hf.1) (hV.1.trans_lt (hlarge i))

/-- The numerator at every node is tested before division by the node's
frequency or by its compensation product. -/
def MovingSlotData.PrimeSquareTests {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, .leaf _ _, _, _ => True
  | _, .node s CL CR U left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      (∀ b ∈ U.map value, ¬ (b : ℤ) ^ 2 ∣
        left.frequency * ((XR * MovingSlotReversal.naturalProduct value CR : ℕ) : ℤ) -
        right.frequency * ((XL * MovingSlotReversal.naturalProduct value CL : ℕ) : ℤ)) ∧
      left.PrimeSquareTests value p XL ∧ right.PrimeSquareTests value p XR

theorem MovingSlotData.newCompensationUnits_iff_squareTests {σ : Type*}
    (value : σ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hprime : T.CompensationPrimeData value) (XL XR : ℕ) (hI : T.Integral value XL XR) :
    T.NewCompensationUnits value XL XR ↔ T.PrimeSquareTests value XL XR := by
  induction T generalizing XL XR with
  | leaf => rfl
  | node s CL CR U left right ihL ihR =>
    have hs := moving_compensation_square_tests (U.map value)
      ((MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR)
      s hprime.1 hprime.2.1 hprime.2.2.1
    have he : (∀ b ∈ U.map value, ¬ (b : ℤ) ^ 2 ∣
        left.frequency * ((XR * MovingSlotReversal.naturalProduct value CR : ℕ) : ℤ) -
        right.frequency * ((XL * MovingSlotReversal.naturalProduct value CL : ℕ) : ℤ)) ↔
      (∀ b ∈ U.map value, ¬ (b : ℤ) ^ 2 ∣ s *
        ((MovingSlotReversal.naturalProduct value U *
          (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR : ℕ) : ℤ)) := by
      have hrel := hI.1.2
      dsimp only [MovingSlotData.step] at hrel
      rw [hrel]
      rfl
    change (_ ∧ _ ∧ _) ↔ _ ∧ _ ∧ _
    rw [ihL hprime.2.2.2.1 _ _ hI.2.1, ihR hprime.2.2.2.2 _ _ hI.2.2, he]
    exact and_congr (by simpa only [MovingSlotReversal.naturalProduct, hprime.2.1, true_and] using hs)
      Iff.rfl

/-- An exact reduction of all pairwise slot tests to the top support and the
explicit numerator exclusions modulo b², for the original integral tree. -/
theorem MovingSlotData.fullPairwise_iff_squareTests {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hcoh : T.RegularCoherent)
    (hprime : T.CompensationPrimeData value) (XL XR : ℕ)
    (hI : T.Integral value XL XR) (hfreq : T.CrossFrequencyUnits value XL XR) :
    T.FullPairwise value XL XR ↔ T.CurrentPairwise value XL XR ∧ T.PrimeSquareTests value XL XR := by
  rw [T.fullPairwise_iff value hcoh XL XR hI hfreq,
    T.newCompensationUnits_iff_squareTests value hprime XL XR hI]

end Ostmann

end OAI
