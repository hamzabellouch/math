import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalLocalFactor

namespace OAI

/-! # Product of the frequency, internal-prime and spectator factors -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def movingFrequencyPairSupport {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (nodes : Bool → List MovingFormulaNode) (R x y : ℤ) : Prop :=
  ∀ side, movingRegularOutsidePairwise value outside (T side) ∧
    (∀ f ∈ nodes side, f.guard.frequencyBounds) ∧
    movingFrequencyGate value R (T side) x y

noncomputable def movingFrequencyPairFactor {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n)
    (nodes : Bool → List MovingFormulaNode) (R x y : ℤ) : ℂ :=
  if movingFrequencyPairSupport value outside T nodes R x y then
    movingDataWeight (F false) (E false) (T false) *
      conj (movingDataWeight (F true) (E true) (T true)) else 0

noncomputable def movingSpectatorPairFactor {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : Bool → (ZMod q)ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (x y : ZMod q) : ℂ :=
  movingModularSpectator value q g (D false) (T false) x y *
    conj (movingModularSpectator value q g (D true) (T true) x y)

/-- The coefficient of the literal original pair is a product over disjoint
arithmetic blocks. No Haar averaging or independence is assumed here. -/
theorem movingSeparatedPairResidueCoefficient_product {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (P : Finset ℕ)
    (hcover : ∀ side, ∀ o ∈ (T side).occurrences,
      ∀ i ∈ o.current.compensationSlots, value i ∈ P) (x y : ℕ) :
    movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R x y =
      movingFrequencyPairFactor value outside F E T nodes R x y *
        (∏ p ∈ P, movingInternalPairFactor value T p x y) *
        ∏ i ∈ S, movingSpectatorPairFactor value (q i) (g i) (fun side => D side i) T x y := by
  have hint := movingInternalPairFactor_product value T P hcover (x : ℤ) (y : ℤ)
  simp only [Int.cast_natCast] at hint
  rw [hint]
  have hsplit : (∀ side, movingSeparatedSupport value outside (T side) (nodes side) R x y) ↔
      movingFrequencyPairSupport value outside T nodes R x y ∧
        (∀ side, movingPrimeLineSupport value (T side) x y ∧
          movingSquareLineSupport value (T side) x y) := by
    simp only [movingSeparatedSupport, movingFrequencyPairSupport, Bool.forall_bool]
    tauto
  have hprod : (∏ i ∈ S,
        movingSpectatorPairFactor value (q i) (g i) (fun side => D side i) T x y) =
      (∏ i ∈ S, movingModularSpectator value (q i) (g i) (D false i) (T false) x y) *
        conj (∏ i ∈ S, movingModularSpectator value (q i) (g i) (D true i) (T true) x y) := by
    simp only [movingSpectatorPairFactor, Finset.prod_mul_distrib, map_prod]
  rw [hprod]
  unfold movingSeparatedPairResidueCoefficient movingSeparatedResidueCoefficient
    movingFrequencyPairFactor
  by_cases h0 : movingSeparatedSupport value outside (T false) (nodes false) R x y
  · by_cases h1 : movingSeparatedSupport value outside (T true) (nodes true) R x y
    · have hall : ∀ side, movingSeparatedSupport value outside (T side) (nodes side) R x y := by
        simp only [Bool.forall_bool]; exact ⟨h0, h1⟩
      obtain ⟨hf, hi⟩ := hsplit.mp hall
      simp only [ite_eq_left h0, ite_eq_left h1, ite_eq_left hf, ite_eq_left hi, map_mul, Int.cast_natCast]
      ring
    · have hall : ¬ (movingFrequencyPairSupport value outside T nodes R x y ∧
          ∀ side, movingPrimeLineSupport value (T side) x y ∧
            movingSquareLineSupport value (T side) x y) := fun h => h1 (hsplit.mpr h true)
      by_cases hf : movingFrequencyPairSupport value outside T nodes R x y
      · have hi := fun hi => hall ⟨hf, hi⟩
        simp only [ite_eq_left h0, ite_eq_right h1, ite_eq_left hf, ite_eq_right hi,
          map_zero, mul_zero, zero_mul]
      · simp only [ite_eq_left h0, ite_eq_right h1, ite_eq_right hf,
          map_zero, mul_zero, zero_mul]
  · have hall : ¬ (movingFrequencyPairSupport value outside T nodes R x y ∧
        ∀ side, movingPrimeLineSupport value (T side) x y ∧
          movingSquareLineSupport value (T side) x y) := fun h => h0 (hsplit.mpr h false)
    by_cases hf : movingFrequencyPairSupport value outside T nodes R x y
    · have hi := fun hi => hall ⟨hf, hi⟩
      simp only [ite_eq_right h0, ite_eq_left hf, ite_eq_right hi, mul_zero, zero_mul]
    · simp only [ite_eq_right h0, ite_eq_right hf, zero_mul]

end Ostmann

end OAI
