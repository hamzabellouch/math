import OAI.NumberTheory.JointDickman.Counting.CoefficientRationalArc
import OAI.NumberTheory.JointDickman.Amplification.TruncatedMajorRegion
import OAI.NumberTheory.JointDickman.Amplification.DiscardedRegionBound
import OAI.NumberTheory.JointDickman.Amplification.EndpointFourierReflection

namespace OAI

/-! # The large-denominator part of the actual separated kernel is negligible -/

namespace JointDickman
open Filter MeasureTheory Finset
open scoped Topology

theorem largeMajorArc_box_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b c d ε : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) (hε : 0 < ε) :
    ∃ C D K : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ K ∧
      ∀ᶠ B : ℕ in atTop, ∀ T X : ℝ, 0 < T → 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      Real.log (T*X) ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) →
      ∀ Q : ℕ, (B : ℝ)^(2/5 : ℝ) ≤ Q → ∀ j : ℕ,
      ∀ g h : Finset ℕ → ℝ,
      (∀ S ⊆ auxiliaryPrimes B, |g S| ≤ 1) →
      (∀ S ⊆ auxiliaryPrimes B, |h S| ≤ 1) →
      ∀ (w₁ w₂ w₃ w₃' : ℝ → ℝ) (M M₃ N₃ : ℝ),
      0 ≤ M → 0 ≤ M₃ → 0 ≤ N₃ →
      (∀ t, |w₁ t| ≤ M) → (∀ t, |w₂ t| ≤ M) →
      (∀ t, HasDerivAt w₃ (w₃' t) t) → Continuous w₃' →
      (∀ t, |w₃ t| ≤ M₃) → (∀ t, |w₃' t| ≤ N₃) →
      (∀ t, t ≤ c ∨ d < t → w₃ t = 0) →
      ‖(B : ℂ)*(∫ θ in largeMajorArcRegion B j X Q,
        endpointFourierSum B a b (T*X) g w₁ θ *
        endpointFourierSum B a b (T*X) h w₂ (-θ) *
        smoothCoefficientAdditiveSum B X (-(j : ℝ)*θ) w₃)‖ ≤
      C*M^2*(D*M₃*(d-c)+K*d*(2*M₃+(N₃+2*Real.pi*M₃)*(d-c)))*
        (B : ℝ)^(-23/20+ε)/T := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hmom⟩ := endpoint_fourier_moments hSD hM hMP ha hab (half_pos hε)
  obtain ⟨D,K,hD,hK,hcoeff⟩ := coefficient_on_large_rational_arc hSD hSW hM hMP
  refine ⟨C₂,D,K,hC₂,hD,hK,?_⟩
  filter_upwards [hmom,hcoeff c d (ε/2) hc hcd (half_pos hε),eventually_ge_atTop 1]
    with B hmomB hcoeffB hB
  intro T X hT hX hlogX hlogTX Q hQ j g h hg hh w₁ w₂ w₃ w₃' M M₃ N₃
    hM0 hM₃ hN₃ hw₁ hw₂ hw₃ hw₃' hbw₃ hbw₃' hsupp
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  let P := C₂*M^2*(B : ℝ)^(-7/4+ε/2)/(T*X)
  let R := (D*M₃*(d-c)+K*d*(2*M₃+(N₃+2*Real.pi*M₃)*(d-c)))*X*
    (B : ℝ)^(-2/5+ε/2)
  have hR : 0 ≤ R := by dsimp [R]; have hd := hc.trans_le hcd; positivity
  have hF := (hmomB (T*X) (mul_pos hT hX) hlogTX.1 hlogTX.2 g hg w₁ M hM0 hw₁).2
  have hG : (∫ θ in (0 : ℝ)..1, ‖endpointFourierSum B a b (T*X) h w₂ (-θ)‖^2) ≤ P := by
    simpa only [endpointFourierSum_neg_norm] using
      (hmomB (T*X) (mul_pos hT hX) hlogTX.1 hlogTX.2 h hh w₂ M hM0 hw₂).2
  have hint := discarded_region_integral_bound
    (H := fun θ => smoothCoefficientAdditiveSum B X (-(j : ℝ)*θ) w₃)
    (largeMajorArcRegion_measurable B j X Q) (fun _ hx => hx.1.1) hR
    (endpointFourierSum_continuous B a b (T*X) g w₁)
    ((endpointFourierSum_continuous B a b (T*X) h w₂).comp continuous_neg)
    (fun θ hθ => by
      obtain ⟨r,hrQ,hrB,hnear⟩ := largeMajorArcRegion_witness hθ
      have hr15 : r.den ≤ B^15 := by
        have hr12 : r.den ≤ B^12 := by exact_mod_cast hrB
        exact hr12.trans (pow_le_pow_right₀ hB (by norm_num : 12 ≤ 15))
      have hrlo : (B : ℝ)^(2/5 : ℝ) ≤ r.den :=
        hQ.trans (by exact_mod_cast hrQ.le)
      exact hcoeffB X (-(j : ℝ)*θ) hX hlogX r hr15 hrlo hnear
        w₃ w₃' M₃ N₃ hM₃ hN₃ hw₃ hw₃' hbw₃ hbw₃' hsupp)
  rw [norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (B : ℝ)*(R/2*(P+P)) := mul_le_mul_of_nonneg_left
      (hint.trans (mul_le_mul_of_nonneg_left (add_le_add hF hG) (div_nonneg hR (by norm_num)))) hB0.le
    _ = _ := by
      have hp : (B : ℝ)^(-23/20+ε) =
          (B : ℝ)*(B : ℝ)^(-2/5+ε/2)*(B : ℝ)^(-7/4+ε/2) := by
        calc
          _ = (B : ℝ)^((1+(-2/5+ε/2))+(-7/4+ε/2)) := by congr 1; ring
          _ = _ := by rw [Real.rpow_add hB0,Real.rpow_add hB0,Real.rpow_one]
      rw [hp]
      dsimp [R,P]
      field_simp
      ring

end JointDickman

end OAI
