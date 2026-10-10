import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedOuterFactor
import OAI.NumberTheory.Ostmann.ZeroDensity.PageResidueReduction

namespace OAI

/-! # The original reduced arithmetic coefficient in the regular-prime CRT split -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem crtSplitExternalEquiv_snd (c r : ℕ) (hcop : c.Coprime r)
    (z : ZMod (c * r) × (ZMod (c * r))ˣ) :
    (crtSplitExternalEquiv c r hcop z).2 = externalResidueReduction (dvd_mul_left r c) z := by
  have he (a : ZMod (c * r)) : (ZMod.chineseRemainder hcop a).2 =
      ZMod.castHom (dvd_mul_left r c) (ZMod r) a :=
    RingHom.congr_fun (Subsingleton.elim
      ((RingHom.snd (ZMod c) (ZMod r)).comp (ZMod.chineseRemainder hcop).toRingHom)
      (ZMod.castHom (dvd_mul_left r c) (ZMod r))) a
  apply Prod.ext
  · exact he z.1
  · apply Units.ext
    exact he (z.2 : ZMod (c * r))

theorem movingReducedPairResidueCoefficient_modEq {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (a b c d : ℕ)
    (hL : (a : ℤ) ≡ (c : ℤ) [ZMOD movingReducedPairModulus value hvalue outside childBound pivotBound T hf q S])
    (hR : (b : ℤ) ≡ (d : ℤ) [ZMOD movingReducedPairModulus value hvalue outside childBound pivotBound T hf q S]) :
    let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
    movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes a b =
      movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes c d := by
  dsimp only
  have ht := movingReducedPairModulus_tests value hvalue outside childBound pivotBound T hf q S
  have he (side : Bool) := movingReducedResidueWeight_modEq value hvalue outside (T side) (hf side)
    a b c d _ _ _ (ht.2.2.1 side) (ht.2.2.2 side) hL hR
    (movingResidueCoefficient_modEq q value hvalue childBound pivotBound (F side) (E side)
      g (Dq side) S (T side) (hf side) a b c d _ (ht.1 side) (ht.2.1 side) hL hR)
  exact congrArg₂ (fun x y : ℂ => x * conj y) (he false) (he true)

/-- A periodic natural-coordinate coefficient descends to the second CRT
coordinate without changing its signed value. -/
theorem periodic_coefficient_crt (C : ℕ → ℕ → ℂ) (c r : ℕ) [NeZero r] [NeZero (c * r)]
    (hcop : c.Coprime r)
    (hC : ∀ a b d e, Nat.ModEq r a d → Nat.ModEq r b e → C a b = C d e)
    (z : ZMod (c * r) × (ZMod (c * r))ˣ) :
    C z.1.val (z.2 : ZMod (c * r)).val =
      C (crtSplitExternalEquiv c r hcop z).2.1.val
        ((crtSplitExternalEquiv c r hcop z).2.2 : ZMod r).val := by
  rw [crtSplitExternalEquiv_snd]
  apply hC
  · exact nat_modEq_castHom_val (dvd_mul_left r c) z.1
  · exact nat_modEq_castHom_val (dvd_mul_left r c) (z.2 : ZMod (c * r))

/-- Both factors are evaluated at their original natural residue representatives.
Only periodicity and the proved local transform energy are used in the split. -/
theorem periodic_coefficient_regular_average {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, p i) * r)] (hcop : (∏ i, p i).Coprime r)
    (active : I → Bool) (s : ℤ) (other : ∀ i, ZMod (p i))
    (hs : ∀ i, (s : ZMod (p i)) ≠ 0) (ho : ∀ i, other i ≠ 0)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i)
    (C : ℕ → ℕ → ℂ)
    (hC : ∀ a b d e, Nat.ModEq r a d → Nat.ModEq r b e → C a b = C d e) :
    (Fintype.card (ZMod ((∏ i, p i) * r) × (ZMod ((∏ i, p i) * r))ˣ) : ℂ)⁻¹ *
      (∑ z : ZMod ((∏ i, p i) * r) × (ZMod ((∏ i, p i) * r))ˣ, (guardedRegularMultiplier p active s other g z.1.val
        (z.2 : ZMod ((∏ i, p i) * r)).val : ℂ) * C z.1.val (z.2 : ZMod ((∏ i, p i) * r)).val) =
      ((∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹ : ℝ) : ℂ) *
        ((Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ * ∑ z : ZMod r × (ZMod r)ˣ, C z.1.val (z.2 : ZMod r).val) := by
  simp_rw [periodic_coefficient_crt C (∏ i, p i) r hcop hC]
  exact guardedRegularMultiplier_average p hc r hcop active s other hs ho g hg henergy
    (fun z => C z.1.val (z.2 : ZMod r).val)

end Ostmann

end OAI
