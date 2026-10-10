import OAI.Analysis.OperatorAlgebra.ScalarLpProjection

namespace OAI

/-! The interval spectral cutoffs on scalar L² converge strongly to the
identity, giving a strongly exhausting family of projections. -/

noncomputable section
open MeasureTheory Filter Set
open scoped InnerProductSpace Topology

namespace WeakPureInfiniteness

lemma scalarLp_norm_sq_integral (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ t : ℝ, ‖f t‖ ^ 2 := by
  calc
    ‖f‖ ^ 2 = (inner ℂ f f).re := (inner_self_eq_norm_sq (𝕜 := ℂ) f).symm
    _ = ∫ t : ℝ, (inner ℂ (f t) (f t)).re := by
      rw [L2.inner_def]
      exact (integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) f f)).symm
    _ = ∫ t : ℝ, ‖f t‖ ^ 2 := by
      congr 1
      funext t
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (f t)

def scalarIntervalProjection (n : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  scalarLpProjection volume (Icc (-(n : ℝ)) n) measurableSet_Icc

lemma scalarIntervalProjection_ae (n : ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    scalarIntervalProjection n f =ᵐ[volume] (Icc (-(n : ℝ)) n).indicator f :=
  scalarLpProjection_ae volume _ _ f

lemma scalarIntervalProjection_norm_le (n : ℕ) : ‖scalarIntervalProjection n‖ ≤ 1 :=
  scalarLpProjection_norm_le volume _ _

lemma scalarIntervalProjection_isStarProjection (n : ℕ) :
    IsStarProjection (scalarIntervalProjection n) :=
  scalarLpProjection_isStarProjection volume _ _

lemma scalarIntervalProjection_strong (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun n => scalarIntervalProjection n f) atTop (𝓝 f) := by
  let F (n : ℕ) (t : ℝ) := ‖(Icc (-(n : ℝ)) n).indicator (f : ℝ → ℂ) t - f t‖ ^ 2
  have hbound (n : ℕ) (t : ℝ) : F n t ≤ ‖f t‖ ^ 2 := by
    dsimp only [F]
    by_cases ht : t ∈ Icc (-(n : ℝ)) n <;> simp [ht]
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) volume :=
    (((Lp.aestronglyMeasurable f).indicator measurableSet_Icc).sub
      (Lp.aestronglyMeasurable f)).norm.pow 2
  have hi : Integrable (fun t : ℝ => ‖f t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hpoint (t : ℝ) : Tendsto (fun n => F n t) atTop (𝓝 0) := by
    obtain ⟨N, hN⟩ := exists_nat_gt |t|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnt : |t| ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hn)
    have ht : t ∈ Icc (-(n : ℝ)) n := abs_le.mp hnt
    simp [F, ht]
  have hint : Tendsto (fun n => ∫ t : ℝ, F n t) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun t : ℝ => ‖f t‖ ^ 2)
      hmeas hi (fun n => ae_of_all _ (fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hbound n t)) (ae_of_all _ hpoint)
    simpa only [integral_zero] using h
  have heq (n : ℕ) : ‖scalarIntervalProjection n f - f‖ ^ 2 = ∫ t : ℝ, F n t := by
    rw [scalarLp_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (scalarIntervalProjection n f) f,
      scalarIntervalProjection_ae n f] with t hs hp
    rw [hs, Pi.sub_apply, hp]
  have hsq : Tendsto (fun n => ‖scalarIntervalProjection n f - f‖ ^ 2) atTop (𝓝 0) :=
    hint.congr' (Eventually.of_forall fun n => (heq n).symm)
  have hn : Tendsto (fun n => Real.sqrt (‖scalarIntervalProjection n f - f‖ ^ 2))
      atTop (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end WeakPureInfiniteness

end

end OAI
