import OAI.NumberTheory.TwoPoint.Bounds.ReciprocalSampling

namespace OAI

/-! Eliminate labels in the order of witness records, independently of label names. -/

namespace TwoPointCorrelations

open Finset

namespace FiniteLaw

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- The order belongs to the relation records. The ambient prime labels
need no compatible order and all unselected coordinates keep their law. -/
theorem ordered_coordinate_probability_bound {κ : Type*} [LinearOrder κ]
    [Nonempty A] (coordinate : κ → ι)
    (μ : ι → FiniteLaw A) (E : κ → (ι → A) → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (R : Finset κ)
    (hdepends : ∀ i ∈ R, ∀ j ∈ R, i < j → ∀ x a,
      E i (Function.update x (coordinate j) a) ↔ E i x)
    (hconditional : ∀ i ∈ R, ∀ x,
      (μ (coordinate i)).probability (fun a => E i (Function.update x (coordinate i) a)) ≤ δ) :
    (independent μ).probability (fun x => ∀ i ∈ R, E i x) ≤ δ ^ R.card := by
  classical
  revert hdepends hconditional
  induction R using Finset.strongInductionOn with
  | _ R ih =>
    intro hdepends hconditional
    by_cases hR : R.Nonempty
    · let i := R.max' hR
      have hi : i ∈ R := max'_mem R hR
      have hjlt (j : κ) (hj : j ∈ R.erase i) : j < i := by
        have hjR := (mem_erase.mp hj).2
        have hji := (mem_erase.mp hj).1
        exact lt_of_le_of_ne (le_max' R j hjR) hji
      have hretained : ∀ x a,
          (∀ j ∈ R.erase i, E j (Function.update x (coordinate i) a)) ↔ ∀ j ∈ R.erase i, E j x := by
        intro x a
        constructor <;> intro hx j hj
        · exact (hdepends j (mem_erase.mp hj).2 i hi (hjlt j hj) x a).mp (hx j hj)
        · exact (hdepends j (mem_erase.mp hj).2 i hi (hjlt j hj) x a).mpr (hx j hj)
      have hstep := eliminate_coordinate μ (coordinate i) (fun x => ∀ j ∈ R.erase i, E j x)
        (E i) δ hretained (hconditional i hi)
      have hevent : (fun x => ∀ j ∈ R, E j x) =
          (fun x => (∀ j ∈ R.erase i, E j x) ∧ E i x) := by
        funext x
        apply propext
        constructor
        · intro hx
          exact ⟨fun j hj => hx j (mem_erase.mp hj).2, hx i hi⟩
        · rintro ⟨hx, hxi⟩ j hj
          by_cases hji : j = i
          · simpa only [hji] using hxi
          · exact hx j (mem_erase.mpr ⟨hji, hj⟩)
      rw [hevent]
      apply hstep.trans
      have hrest := ih (R.erase i) (Finset.erase_ssubset hi)
        (fun j hj k hk hjk x a => hdepends j (mem_erase.mp hj).2 k (mem_erase.mp hk).2 hjk x a)
        (fun j hj => hconditional j (mem_erase.mp hj).2)
      have hmul := mul_le_mul_of_nonneg_left hrest hδ
      have hcard : R.card = (R.erase i).card + 1 := by
        rw [card_erase_of_mem hi]
        have hpos := card_pos.mpr hR
        omega
      simpa only [hcard, pow_succ, mul_comm] using hmul
    · have hzero : R = ∅ := not_nonempty_iff_eq_empty.mp hR
      rw [hzero, card_empty, pow_zero]
      exact probability_le_one _ _


/-- Ordered nondegenerate prime relations: selected coordinates can be
any labels in the ambient assignment, not necessarily an initial segment. -/
theorem ordered_prime_relation_probability {κ : Type*} [LinearOrder κ]
    (τ : κ → Type*) [∀ i, Fintype (τ i)]
    [Nonempty A] (μ : ι → FiniteLaw A) (value : A → ℕ)
    (hinj : Function.Injective value) (H N : ℕ) (hH : 0 < H) (hN : 1 ≤ N)
    (hprime : ∀ a, (value a).Prime) (hlo : ∀ a, H ≤ value a)
    (hhi : ∀ a, value a ≤ N) (hweight : ∀ i a, (μ i).weight a ≤ (value a : ℝ)⁻¹)
    (m : (i : κ) → τ i → PrimeMonomial ι) (selected control : κ → ι) (R : Finset κ)
    (hcontrol : ∀ i ∈ R, control i ≠ selected i)
    (htriangular : ∀ i ∈ R, ∀ j ∈ R, i < j →
      selected j ∉ primeRelationSupport (m i) ∧ control i ≠ selected j) :
    (independent μ).probability (fun x => ∀ i ∈ R,
      primeRelationEvent (m i) (selected i) (control i) (integerPrimeAssignment value x)) ≤
        ((H : ℝ)⁻¹ + (1 + Real.log N) / H) ^ R.card := by
  classical
  let E : κ → (ι → A) → Prop := fun i x =>
    primeRelationEvent (m i) (selected i) (control i) (integerPrimeAssignment value x)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  apply ordered_coordinate_probability_bound selected μ E _ (by positivity) R ?_ ?_
  · intro i hi j hj hij x a
    exact primeRelationEvent_update_irrelevant (m i) (selected i) (control i) (selected j)
      value x a (htriangular i hi j hj hij).1 (htriangular i hi j hj hij).2
  · intro i hi x
    have hlinear := nondegenerate_reciprocal_probability_bound (μ (selected i)) value hinj
      H N (value (x (control i)))
      (primeRelationCoefficient (m i) (selected i) (integerPrimeAssignment value x))
      (primeRelationConstant (m i) (selected i) (integerPrimeAssignment value x))
      hH hN (hprime _) hlo hhi (hweight (selected i))
    have hevent : (fun a => E i (Function.update x (selected i) a)) =
        (fun a => (value (x (control i)) : ℤ) ∣
          primeRelationCoefficient (m i) (selected i) (integerPrimeAssignment value x) * value a +
          primeRelationConstant (m i) (selected i) (integerPrimeAssignment value x) ∧
          ¬(value (x (control i)) : ℤ) ∣
            primeRelationCoefficient (m i) (selected i) (integerPrimeAssignment value x)) := by
      funext a
      exact propext (primeRelationEvent_update_selected (m i) (selected i) (control i)
        (hcontrol i hi) value x a)
    rw [hevent]
    apply hlinear.trans
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_left (by linarith) (by exact_mod_cast hH)
      (by exact_mod_cast hlo (x (control i)))

end FiniteLaw

end TwoPointCorrelations

end OAI
