import OAI.Geometry.EinsteinFour.ScalarBoundedBessel

namespace OAI

/-! Integrating the finite Bessel bound gives square summability of
compactly supported local coefficient operators. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set
open scoped BoundedContinuousFunction

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

theorem scalarComplexL2_norm_sq (f : Lp ℂ 2 (volume : Measure V)) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => (norm_sq_eq_re_inner (f x)).symm)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι : Type*} {v : ι → E}

theorem scalarLocalOperator_sum_bound (hv : Orthonormal ℝ v)
    (A : E →L[ℝ] (V →ᵇ ℂ)) (B : E →L[ℝ] Lp ℂ 2 (volume : Measure V))
    (hAB : ∀ u, (B u : V → ℂ) =ᵐ[volume] A u)
    {K : Set V} (hK : IsCompact K) (hs : ∀ u x, x ∉ K → A u x = 0) (s : Finset ι) :
    ∑ i ∈ s, ‖B (v i)‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 * (volume K).toReal := by
  have hi (i : ι) : IntegrableOn (fun x => ‖A (v i) x‖ ^ 2) K :=
    (A (v i)).continuous.norm.pow 2 |>.continuousOn.integrableOn_compact hK
  have he (i : ι) : ‖B (v i)‖ ^ 2 = ∫ x in K, ‖A (v i) x‖ ^ 2 := by
    rw [scalarComplexL2_norm_sq, ← integral_indicator hK.isClosed.measurableSet]
    apply integral_congr_ae
    filter_upwards [hAB (v i)] with x hx
    rw [hx]
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
    · rw [indicator_of_notMem hxK, hs (v i) x hxK, norm_zero, zero_pow (by decide)]
  simp_rw [he]
  rw [← integral_finsetSum s (fun i _ => hi i)]
  calc
    _ ≤ ∫ _x in K, 2 * ‖A‖ ^ 2 := by
      apply integral_mono (integrable_finsetSum _ (fun i _ => hi i))
        (continuousOn_const.integrableOn_compact hK)
      intro x
      exact scalarBoundedOperator_bessel hv A s x
    _ = _ := by rw [integral_const]; simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]; ring

theorem scalarLocalOperator_summable (hv : Orthonormal ℝ v)
    (A : E →L[ℝ] (V →ᵇ ℂ)) (B : E →L[ℝ] Lp ℂ 2 (volume : Measure V))
    (hAB : ∀ u, (B u : V → ℂ) =ᵐ[volume] A u)
    {K : Set V} (hK : IsCompact K) (hs : ∀ u x, x ∉ K → A u x = 0) :
    Summable (fun i => ‖B (v i)‖ ^ 2) := by
  exact summable_of_sum_le (fun i => sq_nonneg _) (fun s =>
    scalarLocalOperator_sum_bound hv A B hAB hK hs s)

end
end PositiveEinsteinFour.Geometry

end OAI
