import OAI.NumberTheory.JointDickman.Counting.CoefficientDensityBound
import OAI.NumberTheory.JointDickman.Counting.OscillatoryCoefficientLaw
import OAI.NumberTheory.JointDickman.Counting.EndpointScaleWindow

namespace OAI

/-! # A uniform norm bound on the coefficient major arcs -/

namespace JointDickman
open Filter Finset MeasureTheory
open scoped Topology ArithmeticFunction.Moebius

theorem compact_density_integral_bound {a b M D ξ : ℝ} {w ρ : ℝ → ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M) (_hD : 0 ≤ D)
    (hw : ∀ t, |w t| ≤ M) (hρ : ∀ t ∈ Set.Icc a b, |ρ t| ≤ D)
    (hsupp : ∀ t, t ≤ a ∨ b < t → w t = 0) :
    ‖∫ s : ℝ, (w s : ℂ)*(ρ s : ℂ)*additivePhase (ξ*s)‖ ≤ M*D*(b-a) := by
  have he : (fun s : ℝ => (w s : ℂ)*(ρ s : ℂ)*additivePhase (ξ*s)) =
      (fun s => oscillatoryTest w ξ s*(ρ s : ℂ)) := by
    funext s
    unfold oscillatoryTest
    ring
  rw [he,← oscillatory_integral_eq_integral hab hsupp ξ (fun s => (ρ s : ℂ))]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := M*D)
    (f := fun s => oscillatoryTest w ξ s*(ρ s : ℂ)) (fun s hs => by
      have hs' : s ∈ Set.Icc a b := Set.uIcc_of_le hab ▸ Set.uIoc_subset_uIcc hs
      rw [norm_mul,oscillatoryTest_norm,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul (hw s) (hρ s hs') (abs_nonneg _) hM)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh

theorem coefficient_majorArc_norm_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
      ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ)^(15 : ℝ) → ∀ u : (ZMod q)ˣ,
      ∀ (w w' : ℝ → ℝ) (M N ξ : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ t, HasDerivAt w (w' t) t) → Continuous w' →
      (∀ t, |w t| ≤ M) → (∀ t, |w' t| ≤ N) →
      (∀ t, t ≤ a ∨ b < t → w t = 0) → |ξ| ≤ (B : ℝ)^(14 : ℝ) →
      ‖coefficientExponentialSum B q u ξ X w‖ ≤
        X*(D*M*(b-a)/q.totient +
          K*b*(2*M+(N+2*Real.pi*M)*(b-a))*(B : ℝ)^(-50 : ℝ)) := by
  obtain ⟨c,hc,_,H,K,hK,hexp⟩ := coefficient_oscillatory_law hSD hSW hM
  obtain ⟨D,hD,hdensity⟩ := coefficientDensity_eventually_bounded hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  refine ⟨D,K,hD,hK,?_⟩
  intro a b ha hab
  filter_upwards [hexp a b ha hab,hdensity,endpoint_scale_window ha,eventually_gt_atTop 0]
    with B hexpB hdensityB hwindow hB
  intro X hX hlog q _ hq u w w' M N ξ hM0 hN hw hw' hbw hbw' hsupp hξ
  have hloga := (hwindow X hX hlog.1 (hlog.2.trans (by
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    nlinarith))).2.1
  have hρ : ∀ s ∈ Set.Icc a b, |coefficientDensity c H B (Real.log (s*X)/B)| ≤ D := by
    intro s hs
    apply hdensityB
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    apply (le_div_iff₀ hB0).mpr
    exact hloga.trans (Real.log_le_log (mul_pos ha hX) (mul_le_mul_of_nonneg_right hs.1 hX.le))
  have hI := compact_density_integral_bound hab hM0 hD hbw hρ hsupp (ξ := ξ)
  have hμ : ‖(μ q : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast,Int.cast_one] using
      (show |((μ q : ℤ) : ℝ)| ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q))
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hmain : ‖(X : ℂ)*((μ q : ℂ)/(q.totient : ℂ))*
      ∫ s : ℝ, (w s : ℂ)*(coefficientDensity c H B (Real.log (s*X)/B) : ℂ)*
        additivePhase (ξ*s)‖ ≤ X*(D*M*(b-a)/q.totient) := by
    rw [norm_mul,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX,
      Complex.norm_natCast]
    have hfrac : ‖(μ q : ℂ)‖/(q.totient : ℝ) ≤ 1/(q.totient : ℝ) :=
      div_le_div_of_nonneg_right hμ hφ.le
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hfrac hX.le) hI
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have herr := hexpB X hX hlog q hq u w w' M N ξ hM0 hN hw hw' hbw hbw' hsupp hξ
  calc
    _ ≤ ‖coefficientExponentialSum B q u ξ X w -
        (X : ℂ)*((μ q : ℂ)/(q.totient : ℂ))*
          ∫ s : ℝ, (w s : ℂ)*(coefficientDensity c H B (Real.log (s*X)/B) : ℂ)*additivePhase (ξ*s)‖ +
        ‖(X : ℂ)*((μ q : ℂ)/(q.totient : ℂ))*
          ∫ s : ℝ, (w s : ℂ)*(coefficientDensity c H B (Real.log (s*X)/B) : ℂ)*additivePhase (ξ*s)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ _ := by nlinarith [add_le_add herr hmain]

end JointDickman

end OAI
