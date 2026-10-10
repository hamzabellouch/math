import OAI.NumberTheory.JointDickman.Counting.UniformCoefficientFreeze

namespace OAI

/-! # The published coefficient law with a fixed smooth Fourier profile -/

namespace JointDickman
open Filter MeasureTheory
open scoped Topology ArithmeticFunction.Moebius

theorem moebius_totient_complex_norm_le_one (q : ℕ) [NeZero q] :
    ‖(μ q : ℂ)/(q.totient : ℂ)‖ ≤ 1 := by
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hm : ‖(μ q : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  rw [norm_div,Complex.norm_natCast]
  exact (div_le_div_of_nonneg_right hm (by positivity)).trans
    ((div_le_one (by linarith : (0 : ℝ) < q.totient)).mpr hφ)

theorem coefficient_frozen_majorArc_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      ∀ (j q : ℕ) [NeZero j] [NeZero q] [NeZero (j*q)],
      (q : ℝ) ≤ (B : ℝ)^(15 : ℝ) → ∀ (t : Fin j) (r : Fin q), r.val.Coprime q →
      ∀ (w w' : ℝ → ℝ) (M N ξ : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ x, HasDerivAt w (w' x) x) → Continuous w' →
      (∀ x, |w x| ≤ M) → (∀ x, |w' x| ≤ N) →
      (∀ x, x ≤ a ∨ b < x → w x = 0) → |ξ| ≤ (B : ℝ)^(14 : ℝ) →
      ‖smoothCoefficientAdditiveSum B X (-(j : ℝ)*
          (((arcLiftEquiv j q (t,r)).val : ℝ)/(j*q : ℕ)+ξ/((j : ℝ)*X))) w -
        (X : ℂ)*((μ q : ℂ)/(q.totient : ℂ))*
          ((coefficientDensity c H B (Real.log X/B) : ℂ)*testFourierTransform w ξ)‖ ≤
        X*((K*b*(2*M+(N+2*Real.pi*M)*(b-a)))*(B : ℝ)^(-50 : ℝ)+C*M/B) := by
  obtain ⟨c,hc,hcpos,H,K,hK,hcoeff⟩ := coefficient_lifted_majorArc_law hSD hSW hM
  refine ⟨c,hc,hcpos,H,K,hK,?_⟩
  intro a b ha hab
  obtain ⟨C,hC,hfreeze⟩ := coefficientFourier_freeze_uniform hM hMP c hc H ha hab
  refine ⟨C,hC,?_⟩
  filter_upwards [hcoeff a b ha hab,hfreeze] with B hcoeffB hfreezeB
  intro X hX hlog j q _ _ _ hq t r hr w w' M N ξ hM0 hN0 hw hw' hwb hw'b hsupp hξ
  have hfirst := hcoeffB X hX hlog j q hq t r hr w w' M N ξ hM0 hN0
    hw hw' hwb hw'b hsupp hξ
  have hsecond := hfreezeB X hX hlog.1 w M hM0
    (continuous_iff_continuousAt.mpr (fun x => (hw x).continuousAt)) hwb hsupp ξ
  have hnorm : ‖(X : ℂ)*((μ q : ℂ)/(q.totient : ℂ))‖ ≤ X := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (moebius_totient_complex_norm_le_one q) hX.le
  calc
    _ ≤ ‖smoothCoefficientAdditiveSum B X (-(j : ℝ)*
          (((arcLiftEquiv j q (t,r)).val : ℝ)/(j*q : ℕ)+ξ/((j : ℝ)*X))) w -
        (X : ℂ)*((μ q : ℂ)/(q.totient : ℂ))*coefficientFourierTransform c H B X w ξ‖+
        ‖(X : ℂ)*((μ q : ℂ)/(q.totient : ℂ))*coefficientFourierTransform c H B X w ξ-
          (X : ℂ)*((μ q : ℂ)/(q.totient : ℂ))*
            ((coefficientDensity c H B (Real.log X/B) : ℂ)*testFourierTransform w ξ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (K*b*(2*M+(N+2*Real.pi*M)*(b-a)))*X*(B : ℝ)^(-50 : ℝ)+X*(C*M/B) := by
      apply add_le_add hfirst
      rw [← mul_sub,norm_mul]
      exact mul_le_mul hnorm hsecond (norm_nonneg _) hX.le
    _ = _ := by ring

end JointDickman

end OAI
