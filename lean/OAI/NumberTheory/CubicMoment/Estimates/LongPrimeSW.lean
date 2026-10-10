import OAI.NumberTheory.CubicMoment.Estimates.PublishedKummerPrime

namespace OAI

/-! Prime cancellation on the long-prime range used to prove the
stopped sequence condition. The scale T can be log X while the prime
scale is only exp(sqrt(log X)); no positive power of X is required. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

/-- The precise raw Kummer prime input, followed by partial summation,
gives arbitrary T-power saving on every interval above a prime scale P
as soon as T <= (log P)^2. Smooth weights retain their actual variation. -/
theorem long_prime_interval_bound (hSW : KummerPrimeSiegelWalfisz)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C P₀ : ℝ, 0 < C ∧ 1 < P₀ ∧ ∀ (T P R a b : ℝ),
      1 ≤ T → P₀ ≤ P → T ≤ (Real.log P)^2 → P ≤ a → a ≤ b → b ≤ R*P →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) → norm v ≤ T^A →
      ∀ f : ℝ → ℂ, (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) →
      IntegrableOn (deriv f) (Set.Icc a b) →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p)*cubicSymbol p v‖ ≤
        (C*(R*P)/T^D)*(‖f a‖+‖f b‖+∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := weighted_kummer_prime_bound hSW
    (2*A) (2*D) (by positivity) (by positivity)
  refine ⟨C,P₀,hC,hP₀,?_⟩
  intro T P R a b hT hP hTP hPa hab hb v hv hnc hcon f hdiff hint
  have hP1 : 1 < P := hP₀.trans_le hP
  have hP0 : 0 < P := zero_lt_one.trans hP1
  have ha0 : 0 < a := hP0.trans_le hPa
  have hb0 : 0 < b := ha0.trans_le hab
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hlogP : 0 < Real.log P := Real.log_pos hP1
  have hloga : Real.log P ≤ Real.log a := Real.log_le_log hP0 hPa
  have hsquare (E : ℝ) : ((Real.log P)^2)^E = (Real.log P)^(2*E) := by
    simpa only [Nat.cast_ofNat] using (Real.rpow_natCast_mul hlogP.le 2 E).symm
  have hcon' : norm v ≤ (Real.log a)^(2*A) := by
    calc
      _ ≤ T^A := hcon
      _ ≤ ((Real.log P)^2)^A := Real.rpow_le_rpow hT0.le hTP hA.le
      _ = (Real.log P)^(2*A) := hsquare A
      _ ≤ (Real.log a)^(2*A) := Real.rpow_le_rpow hlogP.le hloga (by positivity)
  have hden : T^D ≤ (Real.log a)^(2*D) := by
    calc
      _ ≤ ((Real.log P)^2)^D := Real.rpow_le_rpow hT0.le hTP hD.le
      _ = (Real.log P)^(2*D) := hsquare D
      _ ≤ (Real.log a)^(2*D) := Real.rpow_le_rpow hlogP.le hloga (by positivity)
  have hfrac : C*b/(Real.log a)^(2*D) ≤ C*(R*P)/T^D :=
    div_le_div₀ (mul_nonneg hC.le (hb0.le.trans hb)) (mul_le_mul_of_nonneg_left hb hC.le)
      (Real.rpow_pos_of_pos hT0 D) hden
  apply (hbound a b (hP.trans hPa) hab v hv hnc hcon' f hdiff hint).trans
  apply mul_le_mul_of_nonneg_right hfrac
  exact add_nonneg (add_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _))
    (integral_nonneg (fun _ => _root_.norm_nonneg _))

end CubicFirstMoment

end

end OAI
