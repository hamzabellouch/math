import OAI.Geometry.EinsteinFour.ScalarPoissonKernelAdjointEstimate

namespace OAI

/-! Small-coefficient regularity applies to an existing L2 distributional
solution: construct an H2 solution, then identify the two using the actual
formal-transpose uniqueness theorem. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "S" => 𝓢(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative

private theorem scalar_coordinate_sub (i : Fin 4) (u v : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative i (u - v) =
      scalarCoordinateDerivative i u - scalarCoordinateDerivative i v := by
  exact (LineDeriv.lineDerivOpCLM ℂ 𝓢'(V, ℂ) (EuclideanSpace.basisFun (Fin 4) ℝ i)).map_sub u v

theorem scalarPerturbedOperator_sub (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (u v : 𝓢'(V, ℂ)) :
    scalarPerturbedOperator a b (u - v) =
      scalarPerturbedOperator a b u - scalarPerturbedOperator a b v := by
  simp only [scalarPerturbedOperator, normalizedScalarHelmholtz, scalar_coordinate_sub,
    ← laplacianCLM_apply, map_sub, smul_sub, Finset.sum_sub_distrib]
  abel

private theorem scalarSchwartz_Linf_bound (a : S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ x, ‖a x‖ ≤ δ) : ‖a.toLp ∞ (volume : Measure V)‖ ≤ δ := by
  rw [SchwartzMap.toLp, Lp.norm_toLp,
    eLpNorm_exponent_top a.continuous.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hδ (eLpNormEssSup_le_of_ae_bound (.of_forall ha))

/-- This is regularity of the given solution, not only existence of a new
regular solution. All smallness assumptions concern the actual coefficient
functions and their first two derivatives. -/
theorem scalar_small_elliptic_gain_two
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (u f : L2) (hu : scalarPerturbedOperator a b (u : 𝓢'(V, ℂ)) = (f : 𝓢'(V, ℂ))) :
    MemSobolev 2 2 (u : 𝓢'(V, ℂ)) := by
  have hsmall' : 16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ < 1 := by
    have hle : 16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ ≤
        (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ := by
      calc
        _ ≤ 16 * (2 * Real.pi) ^ 2 * δ + 4 * (2 * Real.pi) * δ +
            (32 * (2 * Real.pi) + 20) * δ := by
          exact le_add_of_nonneg_right (mul_nonneg (by positivity) hδ)
        _ = _ := by ring
    exact hle.trans_lt hsmall
  obtain ⟨v, hv2, hv⟩ := scalar_perturbedHelmholtz_solution
    (fun i j => (a i j : V → ℂ)) (fun i => (b i : V → ℂ))
    (fun i j => (a i j).hasTemperateGrowth) (fun i => (b i).hasTemperateGrowth)
    δ ha hb hsmall' f
  have hv' : scalarPerturbedOperator a b (v : 𝓢'(V, ℂ)) = (f : 𝓢'(V, ℂ)) := hv
  have hdiff : scalarPerturbedOperator a b ((u - v : L2) : 𝓢'(V, ℂ)) = 0 := by
    change scalarPerturbedOperator a b ((Lp.toTemperedDistributionCLM ℂ volume 2) (u - v)) = 0
    rw [map_sub, scalarPerturbedOperator_sub, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistributionCLM_apply, hu, hv', sub_self]
  have heq : u - v = 0 := scalarPerturbedOperator_kernel_small a b δ hδ
    (fun i j => scalarSchwartz_Linf_bound _ δ hδ (ha i j))
    (fun i j k => scalarSchwartz_Linf_bound _ δ hδ (ha1 i j k))
    (fun i j k l => scalarSchwartz_Linf_bound _ δ hδ (ha2 i j k l))
    (fun i => scalarSchwartz_Linf_bound _ δ hδ (hb i))
    (fun i k => scalarSchwartz_Linf_bound _ δ hδ (hb1 i k)) hsmall (u - v) hdiff
  rw [sub_eq_zero.mp heq]
  exact hv2

end
end PositiveEinsteinFour.Geometry

end OAI
