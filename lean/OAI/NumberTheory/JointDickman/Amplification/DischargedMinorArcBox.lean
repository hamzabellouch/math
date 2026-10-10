import OAI.NumberTheory.JointDickman.Arithmetic.DischargedSmoothMinorArc
import OAI.NumberTheory.JointDickman.Amplification.DiscardedRegionBound
import OAI.NumberTheory.JointDickman.Amplification.EndpointFourierReflection
import OAI.NumberTheory.JointDickman.Amplification.MinorArcMeasurable

namespace OAI

/-! # The actual separated kernel has a power-saving minor-arc contribution -/

namespace JointDickman
open Filter Finset MeasureTheory
open scoped Topology

theorem minorArc_box_bound_bounded_log
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b c d ε : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ T X : ℝ, 0 < T → 0 < X →
      (9/10 : ℝ)*B ≤ Real.log X → Real.log X ≤ (11/5 : ℝ)*B →
      Real.log (T*X) ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) →
      ∀ j : ℕ, ∀ g h : Finset ℕ → ℝ,
      (∀ S ⊆ auxiliaryPrimes B, |g S| ≤ 1) →
      (∀ S ⊆ auxiliaryPrimes B, |h S| ≤ 1) →
      ∀ (w₁ w₂ w₃ w₃' : ℝ → ℝ) (M M₃ N₃ : ℝ),
      0 ≤ M → 0 ≤ M₃ → 0 ≤ N₃ →
      (∀ t, |w₁ t| ≤ M) → (∀ t, |w₂ t| ≤ M) →
      (∀ t, HasDerivAt w₃ (w₃' t) t) → Continuous w₃' →
      (∀ t, |w₃ t| ≤ M₃) → (∀ t, |w₃' t| ≤ N₃) →
      (∀ t, t ≤ c ∨ d < t → w₃ t = 0) →
      ‖(B : ℂ)*(∫ θ in minorArcRegion B j X,
        endpointFourierSum B a b (T*X) g w₁ θ *
        endpointFourierSum B a b (T*X) h w₂ (-θ) *
        smoothCoefficientAdditiveSum B X (-(j : ℝ)*θ) w₃)‖ ≤
      K*M^2*(2*M₃+N₃*(d-c))*(B : ℝ)^(-5/4+ε)/T := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hmom⟩ := endpoint_fourier_moments hSD hM hMP ha hab (half_pos hε)
  obtain ⟨C₃,hC₃,hminor⟩ := smooth_coefficient_minorArc_bounded_log hc hcd (half_pos hε)
  have hd : 0 < d := hc.trans_le hcd
  refine ⟨C₂*C₃*d,by positivity,?_⟩
  filter_upwards [hmom,hminor,eventually_gt_atTop 0] with B hmomB hminorB hB
  intro T X hT hX hlogX hlogXhi hlogTX j g h hg hh w₁ w₂ w₃ w₃' M M₃ N₃ hM0 hM₃ hN₃
    hw₁ hw₂ hw₃ hw₃' hbw₃ hbw₃' hsupp
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let Q := C₂*M^2*(B : ℝ)^(-7/4+ε/2)/(T*X)
  let D := C₃*d*(2*M₃+N₃*(d-c))*X*(B : ℝ)^(-1/2+ε/2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hF := (hmomB (T*X) (mul_pos hT hX) hlogTX.1 hlogTX.2 g hg w₁ M hM0 hw₁).2
  have hG : (∫ θ in (0 : ℝ)..1, ‖endpointFourierSum B a b (T*X) h w₂ (-θ)‖^2) ≤ Q := by
    simpa only [endpointFourierSum_neg_norm] using
      (hmomB (T*X) (mul_pos hT hX) hlogTX.1 hlogTX.2 h hh w₂ M hM0 hw₂).2
  have hint := discarded_region_integral_bound
    (H := fun θ => smoothCoefficientAdditiveSum B X (-(j : ℝ)*θ) w₃)
    (minorArcRegion_measurable B j X) (minorArcRegion_subset B j X) hD
    (endpointFourierSum_continuous B a b (T*X) g w₁)
    ((endpointFourierSum_continuous B a b (T*X) h w₂).comp continuous_neg)
    (fun θ hθ => hminorB X (-(j : ℝ)*θ) hX hlogX hlogXhi hθ.2 w₃ w₃' M₃ N₃
      hM₃ hN₃ hw₃ hw₃' hbw₃ hbw₃' hsupp)
  rw [norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (B : ℝ)*(D/2*(Q+Q)) := mul_le_mul_of_nonneg_left
      (hint.trans (mul_le_mul_of_nonneg_left (add_le_add hF hG) (div_nonneg hD (by norm_num)))) hB0.le
    _ = _ := by
      have hp : (B : ℝ)^(-5/4+ε) =
          (B : ℝ)*(B : ℝ)^(-1/2+ε/2)*(B : ℝ)^(-7/4+ε/2) := by
        calc
          _ = (B : ℝ)^((1+(-1/2+ε/2))+(-7/4+ε/2)) := by congr 1; ring
          _ = _ := by rw [Real.rpow_add hB0,Real.rpow_add hB0,Real.rpow_one]
      rw [hp]
      dsimp [D,Q]
      field_simp
      ring

end JointDickman

end OAI
