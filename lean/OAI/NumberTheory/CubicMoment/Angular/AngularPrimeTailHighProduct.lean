import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeProductPolynomialBounds
import OAI.NumberTheory.CubicMoment.Estimates.HighWideTail
import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailCoefficientEnergy

namespace OAI

/-! A single power-width exponent for every actual independent prime
product. The exponent is chosen before the coordinate types and arities;
all finite energies follow from unit weights and actual support counting. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_high_full_prime_envelope_tail_uniform
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι]
      [Fintype κ] [DecidableEq κ] (R : ℝ), 1 ≤ R →
      ∀ (n : ℕ) (W : ℝ → ℂ), HasCompactSupport W →
      tsupport W ⊆ Set.Ioi 0 → ContDiff ℝ ∞ W →
      ∃ K B₀ : ℝ, 0 < K ∧
    ∀ (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
        (X T H : ℝ),
      (∀ i, 1 ≤ XA i) → (∀ i, 1 ≤ XB i) →
      (∀ i x, x < 1 → WA i x = 0) → (∀ i x, R < x → WA i x = 0) →
      (∀ i x, x < 1 → WB i x = 0) → (∀ i x, R < x → WB i x = 0) →
      (∀ i x, ‖WA i x‖ ≤ 1) → (∀ i x, ‖WB i x‖ ≤ 1) →
      let A := ∏ i, XA i
      let B := ∏ i, XB i
      B₀ ≤ B → 4*(2*R^Fintype.card ι*B)^(3/2:ℝ) ≤ A →
      R^Fintype.card κ*A ≤ B^(2+γ) → A ≤ B^3 → 0 < X →
      (2*R^Fintype.card ι*B)^(1/50:ℝ) ≤ T → 1 ≤ H → H ≤ B^3 →
      ‖envelopeCutoffBilinearTail (fullSquarefreePrimeSupport R WA XA 1)
        (fullSquarefreePrimeSupport R WB XB 1)
        (fun a => theta ℓ a*fullPrimeCoefficient R WA XA a)
        (fun b => theta ℓ b*fullPrimeCoefficient R WB XB b) W H T X‖ ≤
          K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^n := by
  obtain ⟨γ,hγ,huniform⟩ := high_wide_envelope_tail_uniform hMV hC hHuxley
  refine ⟨γ,hγ,?_⟩
  intro ι κ _ _ _ _ R hR n W hW hpos hsm
  let MA : ℝ := 18*R^Fintype.card κ*((Fintype.card κ)^(Fintype.card κ):ℕ)^2
  let MB : ℝ := 18*R^Fintype.card ι*((Fintype.card ι)^(Fintype.card ι):ℕ)^2
  obtain ⟨K,B₀,hK,hbound⟩ := huniform MA MB
    (R^Fintype.card ι) (R^Fintype.card κ)
    (by dsimp [MA]; positivity) (by dsimp [MB]; positivity)
    (one_le_pow₀ hR) (one_le_pow₀ hR) n 0 0 W hW hpos hsm
  refine ⟨K,B₀,hK,?_⟩
  intro WA WB XA XB X T H hXA hXB hAlo hAhi hBlo hBhi hWA hWB
  dsimp only
  intro hB hAlow hAup hA3 hX hT hH hHB
  have hXAp : ∀ i, 0 < XA i := fun i => zero_lt_one.trans_le (hXA i)
  have hXBp : ∀ i, 0 < XB i := fun i => zero_lt_one.trans_le (hXB i)
  have henergyA := (theta_coefficient_energy ℓ _ _
    (fun x hx => (fullSquarefreePrimeSupport_primary R WA XA 1 hx).1)).trans_le
    (fullPrimeCoefficient_l2_unit (zero_le_one.trans hR) WA XA hXAp hAlo hAhi hWA 1)
  have henergyB := (theta_coefficient_energy ℓ _ _
    (fun y hy => (fullSquarefreePrimeSupport_primary R WB XB 1 hy).1)).trans_le
    (fullPrimeCoefficient_l2_unit (zero_le_one.trans hR) WB XB hXBp hBlo hBhi hWB 1)
  apply hbound _ _ _ _ (∏ i, XB i) (∏ i, XA i) X T H
    hB hAlow hAup hA3 hX hT hH hHB
  · intro x hx
    exact ⟨(fullSquarefreePrimeSupport_primary R WA XA 1 hx).1,
      fullPrimeProduct_norm_bounds R WA XA hXAp hAlo hAhi (Finset.mem_filter.mp hx).1⟩
  · intro y hy
    exact ⟨(fullSquarefreePrimeSupport_primary R WB XB 1 hy).1,
      (fullSquarefreePrimeSupport_primary R WB XB 1 hy).2,
      fullPrimeProduct_norm_bounds R WB XB hXBp hBlo hBhi (Finset.mem_filter.mp hy).1⟩
  · simpa only [MA,pow_zero,mul_one] using henergyA
  · simpa only [MB,pow_zero,mul_one] using henergyB

end CubicFirstMoment

end

end OAI
