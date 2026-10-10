import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeFrequencyAverage

namespace OAI

/-! # Compensation coincidences vanish on both original and arithmetic support -/

namespace Ostmann
open scoped Classical

theorem movingRegularOutsidePairwise_root {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (h : movingRegularOutsidePairwise value outside T) :
    (T.regularSlots.map value).Pairwise Nat.Coprime := by
  have hr : (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime := by
    cases T with
    | leaf => exact h
    | node => exact h.1
  exact (List.pairwise_append.mp hr).1

theorem movingFullOutsidePairwise_regular {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (h : movingFullOutsidePairwise value outside T XL XR) :
    movingRegularOutsidePairwise value outside T := by
  induction T generalizing XL XR with
  | leaf s regular =>
    exact h.tail.tail
  | node s CL CR U left right ihL ihR =>
    exact ⟨h.1.tail.tail, ihL _ _ h.2.1, ihR _ _ h.2.2⟩

theorem MovingSlotData.compensationDistinct_of_regularSupport {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hc : T.RegularCoherent) (h : movingRegularOutsidePairwise value outside T) :
    T.CompensationDistinct value := by
  induction T with
  | leaf => trivial
  | node s CL CR U left right ihL ihR =>
    have hp := movingRegularOutsidePairwise_root value outside left h.2.1
    have hperm := (hc.1.map value).pairwise_iff (R := Nat.Coprime) (fun h => h.symm)
    have hu : ((U ++ CL).map value).Pairwise Nat.Coprime := hperm.mp hp
    rw [List.map_append] at hu
    exact ⟨(List.pairwise_append.mp hu).1, ihL hc.2.2.1 h.2.1,
      ihR hc.2.2.2 h.2.2⟩

theorem movingSupportedWeight_zero_of_compensation_collision {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hc : T.RegularCoherent) (hbad : ¬ T.CompensationDistinct value)
    (XL XR : ℕ) (z : ℂ) : movingSupportedWeight value outside T XL XR z = 0 := by
  apply ite_eq_right
  intro h
  exact hbad (T.compensationDistinct_of_regularSupport value outside hc
    (movingFullOutsidePairwise_regular value outside T XL XR h.1))

theorem movingFrequencyPrimeAverage_zero_of_compensation_collision {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (x y : ℝ)
    (hc : ∀ b, (T b).RegularCoherent)
    (hbad : ¬ ∀ b, (T b).CompensationDistinct value) :
    movingFrequencyPrimeAverage value outside F E T nodes R r input Q x y = 0 := by
  rw [movingFrequencyPrimeAverage_core]
  have hn : ¬ ∀ b, movingRegularOutsidePairwise value outside (T b) ∧
      (∀ f ∈ nodes b, f.guard.frequencyBounds) := by
    intro h
    exact hbad (fun b => (T b).compensationDistinct_of_regularSupport value outside
      (hc b) (h b).1)
  rw [ite_eq_right hn, zero_mul]

theorem MovingSlotData.compensationPrimeData_of_units {σ : Type*}
    (value : σ → ℕ) (hprime : ∀ i, (value i).Prime) {n : ℕ} (T : MovingSlotData σ n)
    (hu : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hd : T.CompensationDistinct value) : T.CompensationPrimeData value := by
  induction T with
  | leaf => trivial
  | node s CL CR U left right ihL ihR =>
    refine ⟨?_, hd.1, ?_, ihL (fun i => (hu i).2.1) hd.2.1,
      ihR (fun i => (hu i).2.2) hd.2.2⟩
    · intro p hp
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      exact hprime i
    · intro p hp
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      apply (hprime i).coprime_iff_not_dvd.mp
      have h := (hu i).1
      change IsCoprime s (value i : ℤ) at h
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] at h
      exact Nat.coprime_comm.mp h

theorem movingSeparatedResidueCoefficient_zero_of_compensation_collision {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (R x y : ℤ)
    (hc : T.RegularCoherent) (hbad : ¬ T.CompensationDistinct value) :
    movingSeparatedResidueCoefficient q value outside F E g D S T nodes R x y = 0 := by
  apply ite_eq_right
  intro h
  exact hbad (T.compensationDistinct_of_regularSupport value outside hc h.1)

end Ostmann

end OAI
