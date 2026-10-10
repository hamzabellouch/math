import OAI.NumberTheory.CubicMoment.Estimates.LowWideTail
import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailCoefficientEnergy

namespace OAI

/-! The logarithmic-height tail for the actual independent prime products.
The bound is uniform over unit coordinate weights and preserves the full
product envelope, without requiring a new analytic input. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem low_full_prime_envelope_tail
    {C R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hpnt : PrimaryPrimePNT) (hR : 1 ≤ R)
    (n a : ℕ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
        (X T H : ℝ),
      (∀ i, 1 ≤ XA i) → (∀ i, 1 ≤ XB i) →
      (∀ i x, x < 1 → WA i x = 0) → (∀ i x, R < x → WA i x = 0) →
      (∀ i x, x < 1 → WB i x = 0) → (∀ i x, R < x → WB i x = 0) →
      (∀ i x, ‖WA i x‖ ≤ 1) → (∀ i x, ‖WB i x‖ ≤ 1) →
      let A := ∏ i, XA i
      let B := ∏ i, XB i
      (65536:ℝ)^2 ≤ B → 4*(2*R^Fintype.card ι*B)^(3/2:ℝ) ≤ A →
      R^Fintype.card κ*A ≤ B^2*(1+Real.log B)^(3*a) → A ≤ B^3 → 0 < X →
      (1+Real.log (2*R^Fintype.card ι*B))^Ct ≤ T → 1 ≤ H → H ≤ B^3 →
      ‖envelopeCutoffBilinearTail (fullSquarefreePrimeSupport R WA XA 1)
        (fullSquarefreePrimeSupport R WB XB 1)
        (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) W H T X‖ ≤
          K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^n := by
  let MA : ℝ := 18*R^Fintype.card κ*((Fintype.card κ)^(Fintype.card κ):ℕ)^2
  let MB : ℝ := 18*R^Fintype.card ι*((Fintype.card ι)^(Fintype.card ι):ℕ)^2
  let M : ℝ := ((Fintype.card ι)^(Fintype.card ι):ℕ)
  obtain ⟨K,Ct,hK,hbound⟩ := low_wide_envelope_tail hMV hC hHuxley hpnt
    (Mα := MA) (Mβ := MB) (M := M) (by dsimp [MA]; positivity)
    (by dsimp [MB]; positivity) (by dsimp [M]; positivity)
    (one_le_pow₀ hR (n := Fintype.card ι)) (one_le_pow₀ hR (n := Fintype.card κ))
    n 0 0 a W hW hpos hsm
  refine ⟨K,Ct,hK,?_⟩
  intro WA WB XA XB X T H hXA hXB hAlo hAhi hBlo hBhi hWA hWB
  dsimp only
  intro hB hAlow hAup hA3 hX hT hH hHB
  have hXAp : ∀ i, 0 < XA i := fun i => zero_lt_one.trans_le (hXA i)
  have hXBp : ∀ i, 0 < XB i := fun i => zero_lt_one.trans_le (hXB i)
  have henergyA := fullPrimeCoefficient_l2_unit (zero_le_one.trans hR) WA XA hXAp hAlo hAhi hWA 1
  have henergyB := fullPrimeCoefficient_l2_unit (zero_le_one.trans hR) WB XB hXBp hBlo hBhi hWB 1
  have hb (y : Eisenstein) : ‖fullPrimeCoefficient R WB XB y‖ ≤ M := by
    simpa [M] using fullPrimeCoefficient_norm_bound R WB XB (fun _ => 1)
      (fun _ => by norm_num) hWB y
  apply hbound _ _ _ _ (∏ i, XB i) (∏ i, XA i) X T H
    hB hAlow hAup hA3 hX hT hH hHB
  · intro x hx
    exact ⟨(fullSquarefreePrimeSupport_primary R WA XA 1 hx).1,
      fullPrimeProduct_norm_bounds R WA XA hXAp hAlo hAhi (Finset.mem_filter.mp hx).1⟩
  · intro y hy
    exact ⟨(fullSquarefreePrimeSupport_primary R WB XB 1 hy).1,
      (fullSquarefreePrimeSupport_primary R WB XB 1 hy).2,
      fullPrimeProduct_norm_bounds R WB XB hXBp hBlo hBhi (Finset.mem_filter.mp hy).1⟩
  · exact fun y _ => hb y
  · simpa only [MA,pow_zero,mul_one] using henergyA
  · simpa only [MB,pow_zero,mul_one] using henergyB

end CubicFirstMoment

end

end OAI
