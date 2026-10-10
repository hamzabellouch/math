import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullResidues
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalGiantWeight

namespace OAI

/-! # Full manuscript support on the literal recursive giant weight -/

namespace Ostmann
open scoped Classical SchwartzMap

noncomputable def movingFullSupport {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) : Prop :=
  movingFullOutsidePairwise value outside T XL XR ∧ movingNaturalGiantUnits value outside T XL XR

/-- Multiplying by this mask retains all current-state coprimality and all
subtree-frequency unit tests, including the fixed outside list. -/
noncomputable def movingSupportedWeight {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) (z : ℂ) : ℂ :=
  if movingFullSupport value outside T XL XR then z else 0

noncomputable def movingResidueSupportedWeight {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (a b : ℤ) (z : ℂ) : ℂ :=
  if movingFullResidueSupport value outside T a b then z else 0

theorem movingResidueSupportedWeight_norm {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (a b : ℤ) (z : ℂ) :
    ‖movingResidueSupportedWeight value outside T a b z‖ ≤ ‖z‖ := by
  unfold movingResidueSupportedWeight
  split_ifs <;> simp

theorem movingSupportedWeight_residue {σ : Type*} (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hlevels : T.Levels tier) (hcoh : T.RegularCoherent) (hc : T.CompensationPrimeData value)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (XL XR a b : ℕ) (M : ℤ) (z : ℂ) (hI : z ≠ 0 → T.Integral value XL XR)
    (hunit : movingGiantUnitPeriod value outside T ∣ M)
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    movingSupportedWeight value outside T XL XR z =
      if XL.Coprime XR then movingResidueSupportedWeight value outside T a b z else 0 := by
  by_cases hz : z = 0
  · simp [movingSupportedWeight, movingResidueSupportedWeight, hz]
  · have hs := movingFullSupport_residue_iff tier value hprime hdisjoint outside T hlevels hcoh hc
      hf hsmall hfmod XL XR a b M (hI hz) hunit hsquare hL hR
    unfold movingSupportedWeight movingFullSupport movingResidueSupportedWeight
    rw [hs]
    split_ifs <;> simp_all

theorem movingOriginalGiantWeight_integral {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ)
    (hw : movingOriginalGiantWeight q value childBound pivotBound F E g Dq S
      ψ X lo hi φ G T t XL XR ≠ 0) : T.Integral value XL XR := by
  exact MovingSlotData.ArithmeticSupport.integral value hvalue childBound pivotBound T XL XR
    (movingSlotWeight_arithmeticSupport value hvalue childBound pivotBound _ _ T t hT hf XL XR hw)

/-- Exact factorization of the fully supported coefficient, with the single
nonperiodic top-pair coprimality indicator still visible. -/
theorem movingOriginalGiantWeight_full_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hlevels : T.Levels tier) (hcoh : T.RegularCoherent) (hc : T.CompensationPrimeData value)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (XL XR a b M : ℕ)
    (hM : movingTopPeriod value (fun i => (hprime i).ne_zero) childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hunit : movingGiantUnitPeriod value outside T ∣ (M : ℤ))
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound hf (.prime false) (.prime true)
    movingSupportedWeight value outside T XL XR
      (movingOriginalGiantWeight q value childBound pivotBound F E g Dq S ψ X lo hi φ G T t XL XR) =
      if XL.Coprime XR then
        movingResidueSupportedWeight value outside T a b
          (movingResidueCoefficient q value F E g Dq S T nodes a b) *
            movingRealKernel value T nodes ψ X lo hi hlo hhi φ G XL XR else 0 := by
  dsimp only
  have hvalue : ∀ i, value i ≠ 0 := fun i => (hprime i).ne_zero
  rw [movingSupportedWeight_residue tier value hprime hdisjoint outside T hlevels hcoh hc hf
    hsmall hfmod XL XR a b M _
    (movingOriginalGiantWeight_integral q value hvalue childBound pivotBound F E g Dq S
      ψ X lo hi φ G T t hT hf XL XR) hunit hsquare hL hR,
    movingOriginalGiantWeight_factor q value hvalue childBound pivotBound F E g hg Dq S
      ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf XL XR a b M hM hMq hL hR]
  split_ifs
  · unfold movingResidueSupportedWeight
    split_ifs <;> simp
  · rfl

end Ostmann

end OAI
