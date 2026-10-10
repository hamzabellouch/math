import OAI.Geometry.RCD.Heat.HeatLocalEnergy

namespace OAI

/-! # Continuity and monotonicity of actual heat upper-level masses -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular] in
theorem integral_upperLevelPart_sq (f : Lp ℝ 2 μ) {k : ℝ} (hk : 0 ≤ k) (S : Set X) :
    (∫ x in S, ((upperLevelPart_lipschitz k).compLp (upperLevelPart_zero hk) f x)^2 ∂μ) =
      ∫ x in S, (max (f x-k) 0)^2 ∂μ := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae ((upperLevelPart_lipschitz k).coeFn_compLp
    (upperLevelPart_zero hk) f)] with x hx
  exact congrArg (fun z : ℝ => z^2) hx

theorem continuous_heat_upper_level_mass (f : Lp ℝ 2 μ) {k : ℝ} (hk : 0 ≤ k)
    {S : Set X} (hS : MeasurableSet S) :
    Continuous (fun t => ∫ x in S, (max (heatAt μ hQ t f x-k) 0)^2 ∂μ) := by
  let P : Lp ℝ 2 μ → Lp ℝ 2 μ :=
    (upperLevelPart_lipschitz k).compLp (upperLevelPart_zero hk)
  have hP : Continuous P := (upperLevelPart_lipschitz k).continuous_compLp (upperLevelPart_zero hk)
  have he : (fun t => ∫ x in S, (max (heatAt μ hQ t f x-k) 0)^2 ∂μ) =
      fun t => ∫ x in S, (P (heatAt μ hQ t f) x)^2 ∂μ := by
    funext t
    exact (integral_upperLevelPart_sq μ (heatAt μ hQ t f) hk S).symm
  rw [he]
  exact continuous_setIntegral_sq_path μ (hP.comp (heatAt_continuous μ hQ f)) hS

theorem heat_upper_level_mass_mono (f : Lp ℝ 2 μ) (t : ℝ)
    {j k : ℝ} (hj : 0 ≤ j) (hjk : j ≤ k) {S T : Set X} (hST : S ⊆ T) :
    (∫ x in S, (max (heatAt μ hQ t f x-k) 0)^2 ∂μ) ≤
      ∫ x in T, (max (heatAt μ hQ t f x-j) 0)^2 ∂μ := by
  have hi (l : ℝ) (hl : 0 ≤ l) : Integrable
      (fun x => (max (heatAt μ hQ t f x-l) 0)^2) μ :=
    ((upperLevelPart_lipschitz l).comp_memLp (upperLevelPart_zero hl)
      (Lp.memLp (heatAt μ hQ t f))).integrable_sq
  calc
    _ ≤ ∫ x in S, (max (heatAt μ hQ t f x-j) 0)^2 ∂μ := by
      apply integral_mono_ae (hi k (hj.trans hjk)).integrableOn (hi j hj).integrableOn
      exact Eventually.of_forall fun x => (sq_le_sq₀ (le_max_right _ _) (le_max_right _ _)).mpr
        (max_le_max (by linarith) le_rfl)
    _ ≤ _ := setIntegral_mono_set (hi j hj).integrableOn
      (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hST)

theorem heat_zero_level_mass_le (f : Lp ℝ 2 μ) (t : ℝ)
    {S T : Set X} (hST : S ⊆ T) :
    (∫ x in S, (max (heatAt μ hQ t f x) 0)^2 ∂μ) ≤
      ∫ x in T, (heatAt μ hQ t f x)^2 ∂μ := by
  have hi : Integrable (fun x => (max (heatAt μ hQ t f x) 0)^2) μ := by
    simpa only [Function.comp_apply,upperLevelPart,sub_zero] using
      ((upperLevelPart_lipschitz 0).comp_memLp (upperLevelPart_zero (by norm_num))
        (Lp.memLp (heatAt μ hQ t f))).integrable_sq
  calc
    _ ≤ ∫ x in S, (heatAt μ hQ t f x)^2 ∂μ := by
      apply integral_mono_ae hi.integrableOn (Lp.memLp (heatAt μ hQ t f)).integrable_sq.integrableOn
      apply Eventually.of_forall
      intro x
      change (max (heatAt μ hQ t f x) 0)^2 ≤ (heatAt μ hQ t f x)^2
      by_cases hx : 0 ≤ heatAt μ hQ t f x
      · rw [max_eq_left hx]
      · rw [max_eq_right (le_of_not_ge hx),zero_pow (by decide)]
        exact sq_nonneg _
    _ ≤ _ := setIntegral_mono_set (Lp.memLp (heatAt μ hQ t f)).integrable_sq.integrableOn
      (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hST)

end RegularPointCoordinates

end

end OAI
