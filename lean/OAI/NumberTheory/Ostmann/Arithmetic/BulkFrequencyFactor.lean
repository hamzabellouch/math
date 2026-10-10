import OAI.NumberTheory.Ostmann.Arithmetic.BulkFrequencyResidues
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedProduct

namespace OAI

/-! # Separate the nonperiodic prime coincidences from frequency support -/

namespace Ostmann
open scoped Classical ComplexConjugate

noncomputable def movingFrequencyCore {σ : Type*} (value : σ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R x y : ℤ) : ℂ :=
  if ∀ b, movingFrequencyGate value R (T b) x y then
    movingDataWeight (F false) (E false) (T false) *
      conj (movingDataWeight (F true) (E true) (T true)) else 0

/-- The only nonperiodic part of this factor consists of the explicit
regular-prime coincidence tests. The remaining node bounds are independent
of the numerical bulk values. -/
theorem movingFrequencyPairFactor_core {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R x y : ℤ) :
    movingFrequencyPairFactor value outside F E T nodes R x y =
      (if ∀ b, movingRegularOutsidePairwise value outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds) then (1 : ℂ) else 0) *
      movingFrequencyCore value F E T R x y := by
  have he : movingFrequencyPairSupport value outside T nodes R x y ↔
      (∀ b, movingRegularOutsidePairwise value outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds)) ∧
      (∀ b, movingFrequencyGate value R (T b) x y) := by
    simp only [movingFrequencyPairSupport, Bool.forall_bool]
    tauto
  unfold movingFrequencyPairFactor movingFrequencyCore
  rw [he]
  by_cases hs : ∀ b, movingRegularOutsidePairwise value outside (T b) ∧
      (∀ f ∈ nodes b, f.guard.frequencyBounds)
  · by_cases hc : ∀ b, movingFrequencyGate value R (T b) x y
    · rw [ite_eq_left ⟨hs, hc⟩, ite_eq_left hs, ite_eq_left hc, one_mul]
    · rw [ite_eq_right (fun h => hc h.2), ite_eq_left hs, ite_eq_right hc, mul_zero]
  · rw [ite_eq_right (fun h => hs h.1), ite_eq_right hs, zero_mul]

/-- Unlike the removed coincidence tests, the actual frequency core is
constant on the joint bulk residue cells. -/
theorem movingFrequencyCore_values_modEq {σ : Type*} (v w : σ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hcomp : ∀ b, (T b).CompensationAgreement v w)
    (hR : ∀ b, (T b).frequencyProduct ∣ R)
    (hv : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD R ^ (n + 1)])
    (XL XR YL YR : ℤ) (hL : XL ≡ YL [ZMOD R ^ (n + 1)])
    (hRight : XR ≡ YR [ZMOD R ^ (n + 1)]) :
    movingFrequencyCore v F E T R XL XR = movingFrequencyCore w F E T R YL YR := by
  have he : (∀ b, movingFrequencyGate v R (T b) XL XR) ↔
      (∀ b, movingFrequencyGate w R (T b) YL YR) :=
    forall_congr' fun b => movingFrequencyGate_values_modEq v w R (T b)
      (hf b) (hcomp b) (hR b) hv XL XR YL YR hL hRight
  simp only [movingFrequencyCore, he]

def MovingSlotData.FrequencyBounds {σ : Type*} (childBound : ℕ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | n + 1, .node _ _ _ _ left right =>
      left.frequency.natAbs ≤ childBound (n + 1) ∧
      right.frequency.natAbs ≤ childBound (n + 1) ∧
      left.FrequencyBounds childBound ∧ right.FrequencyBounds childBound

theorem MovingSlotData.formulaNodes_frequencyBounds {σ : Type*} (value : σ → ℕ)
    (hv : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (L R : HistoryFormula Bool) :
    (∀ f ∈ T.formulaNodes value hv childBound pivotBound hf L R,
      f.guard.frequencyBounds) ↔ T.FrequencyBounds childBound := by
  induction T generalizing L R with
  | leaf => simp [formulaNodes, FrequencyBounds]
  | node s CL CR u left right ihL ihR =>
    simp only [formulaNodes, List.mem_cons, List.mem_append,
      or_imp, forall_and, forall_eq, ihL, ihR, FrequencyBounds]
    change ((_ ∧ _) ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
    tauto

end Ostmann

end OAI
