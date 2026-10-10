import OAI.Geometry.SurfaceImmersion.Geometry.LocalCovarianceParameter
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicPrimitive
import OAI.Geometry.SurfaceImmersion.Geometry.IntegratedCovariance

namespace OAI

/-! Integrated covariance correction on an open parameter domain. -/

noncomputable section
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.CovarianceCorrector

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The explicit primitive is smooth wherever the geometric data are admissible. -/
theorem contDiffOn_integratedCorrector {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ} {S : Set P} (hS : IsOpen S)
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hr : ContDiffOn ℝ ∞ (fun z : P × ℝ => r z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hq : ContDiffOn ℝ ∞ q S) (hqpos : ∀ p ∈ S, 0 < q p)
    (hcircle : ∀ p ∈ S, ∀ t, inner ℝ (V p t) (V p t) = q p) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => integratedCorrector V r q z.1 z.2)
      (S ×ˢ Set.univ) :=
  PeriodicPrimitive.contDiffOn_primitive_joint hS
    (contDiffOn_parameterCorrector_joint hS hV hr hq hqpos hcircle)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The fluctuation equation uses the constant-speed hypotheses only at this parameter. -/
theorem parameterCorrector_projection_at {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ} (p : P)
    (hr : average (r p) = 0) (hq : 0 < q p)
    (hcircle : ∀ t, inner ℝ (V p t) (V p t) = q p) :
    fluctuation (fun t => inner ℝ (V p t) (parameterCorrector V r q p t)) = r p :=
  corrected_projection (V p) (average (V p)) (r p).continuous hr hq.ne' hcircle _

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- The zero mean equation uses invertibility only at this parameter. -/
theorem parameterCorrector_average_at {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ} (p : P) (hq : 0 < q p)
    (hcircle : ∀ t, inner ℝ (V p t) (V p t) = q p) :
    average (parameterCorrector V r q p) = 0 :=
  average_correctedVector (V p).continuous rfl (r p).continuous (q p)
    (covarianceSolution (V p) (r p) (q p))
    (covarianceSolution_equation (r p) hq hcircle)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [CompleteSpace E] in
lemma parameterCorrector_mem_submodule_at (N : Submodule ℝ E)
    (V : P → C(Period, E)) (r : P → C(Period, ℝ)) (q : P → ℝ) (p : P)
    (hmem : ∀ t, V p t ∈ N) (hq : 0 < q p)
    (hcircle : ∀ t, inner ℝ (V p t) (V p t) = q p) (t : Period) :
    parameterCorrector V r q p t ∈ N := by
  apply N.smul_mem
  apply N.sub_mem
  · exact N.smul_mem _ (hmem t)
  · exact covarianceSolution_mem_submodule N (V p) (r p) hmem hq hcircle

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
