import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDilation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Strong continuity of the physical homogeneous dilation -/

open Filter MeasureTheory Topology
open scoped SchwartzMap ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {R : ℝ // 1 ≤ R}

theorem homogeneousDilation_norm_le_one (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (R : Radius) (f : HomogeneousY a k) :
    ‖homogeneousDilation a k R.1 ha ha1 hk R.2 f‖ ≤ ‖f‖ := by
  exact (homogeneousDilation_norm_le a k R.1 ha ha1 hk R.2 f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos R.2 (by linarith)))

private theorem dilation_polynomial_bound (ψ : 𝓢(E, ℂ)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : Radius) (ξ : E),
      (1 + ‖ξ‖) ^ N * ‖ψ (R.1 • ξ)‖ ≤ C := by
  let C := 2 ^ N * (Finset.Iic (N, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ
  refine ⟨|C|, abs_nonneg C, fun R ξ => ?_⟩
  have hnorm : ‖ξ‖ ≤ ‖R.1 • ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le zero_lt_one R.2)]
    nlinarith [norm_nonneg ξ, R.2]
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (N, 0)) le_rfl le_rfl ψ (R.1 • ξ)
  have hb : (1 + ‖R.1 • ξ‖) ^ N * ‖ψ (R.1 • ξ)‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using h
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖ξ‖ ≤ 1 + ‖R.1 • ξ‖) N)
      (norm_nonneg _)).trans (hb.trans (le_abs_self C))

private theorem continuous_dilation_schwartz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    Continuous (fun R : Radius => homogeneousDilation a k R.1 ha ha1 hk R.2
      (homogeneousFrequencyEmbedding a k ha ha1 hk ψ)) := by
  let μ := homogeneousFourierMeasure a k
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  let N := μ.integrablePower
  obtain ⟨C, hC, hb⟩ := dilation_polynomial_bound ψ N
  have hc : Continuous (fun R : Radius => R.1 ^ (12 - 2 * a)) :=
    continuous_subtype_val.rpow_const
      (fun R => Or.inl (lt_of_lt_of_le zero_lt_one R.2).ne')
  rw [continuous_iff_continuousAt]
  intro R₀
  let M := R₀.1 ^ (12 - 2 * a) + 1
  let D := 2 * M * C
  have hnear : ∀ᶠ R : Radius in 𝓝 R₀, R.1 ^ (12 - 2 * a) ≤ M :=
    (hc.continuousAt.eventually (eventually_lt_nhds (by dsimp [M]; linarith))).mono
      (fun _ h => h.le)
  have hR₀ : R₀.1 ^ (12 - 2 * a) ≤ M := by dsimp [M]; linarith
  let Ψ := fun R : Radius => homogeneousFourierDilation a R.1
    (lt_of_lt_of_le zero_lt_one R.2) ψ
  have hpoly (R : Radius) (hR : R.1 ^ (12 - 2 * a) ≤ M) (ξ : E) :
      (1 + ‖ξ‖) ^ N * ‖Ψ R ξ‖ ≤ M * C := by
    change (1 + ‖ξ‖) ^ N * ‖homogeneousFourierDilation a R.1 _ ψ ξ‖ ≤ _
    rw [homogeneousFourierDilation_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith [R.2]) _)]
    calc
      _ = R.1 ^ (12 - 2 * a) * ((1 + ‖ξ‖) ^ N * ‖ψ (R.1 • ξ)‖) := by ring
      _ ≤ R.1 ^ (12 - 2 * a) * C := mul_le_mul_of_nonneg_left (hb R ξ)
        (Real.rpow_nonneg (by linarith [R.2]) _)
      _ ≤ M * C := mul_le_mul_of_nonneg_right hR hC
  have hdom (R : Radius) (hR : R.1 ^ (12 - 2 * a) ≤ M) (ξ : E) :
      ‖Ψ R ξ - Ψ R₀ ξ‖ ^ 2 ≤ D ^ 2 * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
    let P := (1 + ‖ξ‖) ^ N
    have hP : 1 ≤ P := one_le_pow₀ (by linarith [norm_nonneg ξ])
    have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
    have hdiff : P * ‖Ψ R ξ - Ψ R₀ ξ‖ ≤ D := by
      calc
        _ ≤ P * (‖Ψ R ξ‖ + ‖Ψ R₀ ξ‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) hPpos.le
        _ ≤ D := by dsimp [P, D]; nlinarith [hpoly R hR ξ, hpoly R₀ hR₀ ξ]
    have hs := pow_le_pow_left₀ (mul_nonneg hPpos.le (norm_nonneg _)) hdiff 2
    have hp : P ≤ P ^ 2 := by nlinarith
    have hs' : P * ‖Ψ R ξ - Ψ R₀ ξ‖ ^ 2 ≤ D ^ 2 := by nlinarith [sq_nonneg ‖Ψ R ξ - Ψ R₀ ξ‖]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    exact (le_mul_inv_iff₀ hPpos).mpr (by simpa only [mul_comm] using hs')
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (fun ξ : E => D ^ 2 * (1 + ‖ξ‖) ^ (-(N : ℝ)))
    (F := fun R ξ => ‖Ψ R ξ - Ψ R₀ ξ‖ ^ 2) (f := fun _ => (0 : ℝ))
    (Eventually.of_forall (fun R => ((Ψ R).continuous.sub (Ψ R₀).continuous).norm.pow 2 |>.aestronglyMeasurable))
    (hnear.mono (fun R hR => ae_of_all μ (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hdom R hR ξ)))
    ((Measure.integrable_pow_neg_integrablePower μ).const_mul (D ^ 2))
    (ae_of_all μ (fun ξ => by
      have hcont : Continuous (fun R : Radius => Ψ R ξ) := by
        simp only [Ψ, homogeneousFourierDilation_apply]
        exact (Complex.continuous_ofReal.comp hc).mul
          (ψ.continuous.comp (continuous_subtype_val.smul continuous_const))
      have ht : Tendsto (fun R : Radius => ‖Ψ R ξ - Ψ R₀ ξ‖ ^ 2) (𝓝 R₀)
          (𝓝 (‖Ψ R₀ ξ - Ψ R₀ ξ‖ ^ 2)) :=
        ((hcont.sub (continuous_const (y := Ψ R₀ ξ))).norm.fun_pow 2).tendsto R₀
      simpa only [sub_self, norm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht))
  have hsq : Tendsto (fun R : Radius => ‖homogeneousDilation a k R.1 ha ha1 hk R.2
      (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) -
      homogeneousDilation a k R₀.1 ha ha1 hk R₀.2
        (homogeneousFrequencyEmbedding a k ha ha1 hk ψ)‖ ^ 2) (𝓝 R₀) (𝓝 0) := by
    simpa only [homogeneousDilation_on_Schwartz, ← map_sub,
      homogeneousFrequencyEmbedding_norm_sq_integral, sub_apply, integral_zero, Ψ] using hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq

theorem continuous_homogeneousDilation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    Continuous (fun R : Radius => homogeneousDilation a k R.1 ha ha1 hk R.2 f) := by
  rw [continuous_iff_continuousAt]
  intro R₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨ψ, hψ⟩ := (homogeneousFrequencyEmbedding_dense a k ha ha1 hk).exists_dist_lt
    f (by positivity : 0 < ε / 4)
  let g := homogeneousFrequencyEmbedding a k ha ha1 hk ψ
  have hg : ∀ᶠ R : Radius in 𝓝 R₀,
      dist (homogeneousDilation a k R.1 ha ha1 hk R.2 g)
        (homogeneousDilation a k R₀.1 ha ha1 hk R₀.2 g) < ε / 4 :=
    (continuous_dilation_schwartz a k ha ha1 hk ψ).continuousAt.eventually
      (Metric.ball_mem_nhds _ (by positivity))
  filter_upwards [hg] with R hR
  have hsmall : ‖f - g‖ < ε / 4 := by simpa only [dist_eq_norm, g] using hψ
  have h1 := homogeneousDilation_norm_le_one a k ha ha1 hk R (f - g)
  have h2 := homogeneousDilation_norm_le_one a k ha ha1 hk R₀ (f - g)
  have ht := dist_triangle (homogeneousDilation a k R.1 ha ha1 hk R.2 f)
    (homogeneousDilation a k R.1 ha ha1 hk R.2 g)
    (homogeneousDilation a k R₀.1 ha ha1 hk R₀.2 f)
  have ht' := dist_triangle (homogeneousDilation a k R.1 ha ha1 hk R.2 g)
    (homogeneousDilation a k R₀.1 ha ha1 hk R₀.2 g)
    (homogeneousDilation a k R₀.1 ha ha1 hk R₀.2 f)
  rw [dist_comm (homogeneousDilation a k R₀.1 ha ha1 hk R₀.2 g)] at ht'
  simp only [dist_eq_norm, ← map_sub] at *
  linarith

theorem continuous_homogeneousDilation_uncurry (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    Continuous (fun p : Radius × HomogeneousY a k =>
      homogeneousDilation a k p.1.1 ha ha1 hk p.1.2 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hu : ∀ᶠ q : Radius × HomogeneousY a k in 𝓝 p, dist q.2 p.2 < ε / 2 :=
    continuous_snd.continuousAt.tendsto.eventually (Metric.ball_mem_nhds p.2 (by linarith))
  have hs : ∀ᶠ q : Radius × HomogeneousY a k in 𝓝 p,
      dist (homogeneousDilation a k q.1.1 ha ha1 hk q.1.2 p.2)
        (homogeneousDilation a k p.1.1 ha ha1 hk p.1.2 p.2) < ε / 2 :=
    ((continuous_homogeneousDilation a k ha ha1 hk p.2).comp continuous_fst).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds _ (by linarith))
  filter_upwards [hu, hs] with q hqu hqs
  have hb := homogeneousDilation_norm_le_one a k ha ha1 hk q.1 (q.2 - p.2)
  calc
    _ ≤ dist (homogeneousDilation a k q.1.1 ha ha1 hk q.1.2 q.2)
        (homogeneousDilation a k q.1.1 ha ha1 hk q.1.2 p.2) +
      dist (homogeneousDilation a k q.1.1 ha ha1 hk q.1.2 p.2)
        (homogeneousDilation a k p.1.1 ha ha1 hk p.1.2 p.2) := dist_triangle _ _ _
    _ ≤ dist q.2 p.2 + dist (homogeneousDilation a k q.1.1 ha ha1 hk q.1.2 p.2)
        (homogeneousDilation a k p.1.1 ha ha1 hk p.1.2 p.2) := by
      exact add_le_add (by simpa only [dist_eq_norm, ← map_sub] using hb) le_rfl
    _ < ε := by linarith

end DefocusingNLS

end OAI
