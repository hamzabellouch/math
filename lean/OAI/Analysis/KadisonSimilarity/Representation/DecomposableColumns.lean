import OAI.Analysis.KadisonSimilarity.Representation.LocalizedL2Bound

namespace OAI

/-! The columns of an operator commuting with localization are pointwise
bounded by its operator norm. No essential-norm formula is assumed. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped ENNReal Topology

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem indicatorConstL2_norm_sq (s : Set Ω) (hs : MeasurableSet s) (x : H) :
    ‖indicatorConstLp 2 hs (measure_ne_top μ s) x‖ ^ 2 = ‖x‖ ^ 2 * μ.real s := by
  rw [l2_norm_sq_eq_integral]
  have heq : (fun a => ‖indicatorConstLp 2 hs (measure_ne_top μ s) x a‖ ^ 2) =ᵐ[μ]
      s.indicator (fun _ => ‖x‖ ^ 2) := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs)
      (hμs := measure_ne_top μ s) (c := x)] with a ha
    rw [ha]
    by_cases h : a ∈ s <;> simp [h]
  rw [integral_congr_ae heq, integral_indicator hs]
  simp [measureReal_def, mul_comm]

omit [CompleteSpace H] in
/-- Commutation with localization bounds each constant-vector column almost
 everywhere. The null set is allowed to depend on the chosen vector. -/
theorem decomposable_column_ae_bound
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hlocal : ∀ (s : Set Ω) (hs : MeasurableSet s) (x : H),
      T (indicatorConstLp 2 hs (measure_ne_top μ s) x) =ᵐ[μ]
        s.indicator (T (Lp.const 2 μ x)))
    (x : H) :
    ∀ᵐ a ∂μ, ‖T (Lp.const 2 μ x) a‖ ≤ ‖T‖ * ‖x‖ := by
  apply ae_norm_le_of_localized_square_bound μ (T (Lp.const 2 μ x)) (C := ‖T‖ * ‖x‖)
    (mul_nonneg (norm_nonneg T) (norm_nonneg x))
  intro s hs
  let f := indicatorConstLp 2 hs (measure_ne_top μ s) x
  refine ⟨T f, hlocal s hs x, ?_⟩
  calc
    ‖T f‖ ^ 2 ≤ (‖T‖ * ‖f‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (T.le_opNorm f)
    _ = (‖T‖ * ‖x‖) ^ 2 * μ.real s := by
      rw [mul_pow, indicatorConstL2_norm_sq]
      ring

end KadisonSimilarity

end

end OAI
