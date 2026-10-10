import OAI.Geometry.SurfaceImmersion.Geometry.CovarianceParameter
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPeriodicPrimitive

namespace OAI

/-! The explicit covariance and primitive operations preserve a fixed
subspace at each parameter value; no choice of a moving frame is required. -/

noncomputable section
open MeasureTheory

namespace ClosedSurfaceR4.CovarianceCorrector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma average_mem_submodule (P : Submodule ℝ E) {f : Period → E}
    (hf : Continuous f) (hm : ∀ t, f t ∈ P) : average f ∈ P :=
  P.convex.integral_mem P.closed_of_finiteDimensional
    (Filter.Eventually.of_forall hm) (integrable_of_continuous hf)

lemma covariance_mem_submodule (P : Submodule ℝ E) {V : Period → E}
    (hV : Continuous V) (hmem : ∀ t, V t ∈ P) {v : E} (hv : v ∈ P) (m : E) :
    covariance V v m ∈ P := by
  apply average_mem_submodule P
  · exact ((hV.sub continuous_const).inner continuous_const).smul (hV.sub continuous_const)
  · intro t
    exact P.smul_mem _ (P.sub_mem (hmem t) hv)

/-- The equation for m forces m into the velocity plane, since both terms
on its right side belong to that plane. -/
lemma covarianceSolution_mem_submodule (P : Submodule ℝ E)
    (V : C(Period, E)) (r : C(Period, ℝ)) (hmem : ∀ t, V t ∈ P)
    {q : ℝ} (hq : 0 < q) (hcircle : ∀ t, inner ℝ (V t) (V t) = q) :
    covarianceSolution V r q ∈ P := by
  have hv := average_mem_submodule P V.continuous hmem
  have hc := covariance_mem_submodule P V.continuous hmem hv (covarianceSolution V r q)
  have hr : average (fun t => r t • V t) ∈ P :=
    average_mem_submodule P (r.continuous.smul V.continuous)
      (fun t => P.smul_mem _ (hmem t))
  have he := covarianceSolution_equation r hq hcircle
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  exact P.add_mem hr (P.smul_mem _ hc)

lemma parameterCorrector_mem_submodule {A : Type*} (P : A → Submodule ℝ E)
    (V : A → C(Period, E)) (r : A → C(Period, ℝ)) (q : A → ℝ)
    (hmem : ∀ p t, V p t ∈ P p) (hq : ∀ p, 0 < q p)
    (hcircle : ∀ p t, inner ℝ (V p t) (V p t) = q p) (p : A) (t : Period) :
    parameterCorrector V r q p t ∈ P p := by
  apply (P p).smul_mem
  apply (P p).sub_mem
  · exact (P p).smul_mem _ (hmem p t)
  · exact covarianceSolution_mem_submodule (P p) (V p) (r p) (hmem p) (hq p) (hcircle p)

end ClosedSurfaceR4.CovarianceCorrector

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma intervalIntegral_mem_submodule (P : Submodule ℝ E) {f : ℝ → E}
    (hf : Continuous f) (hm : ∀ t, f t ∈ P) (a b : ℝ) :
    (∫ t in a..b, f t) ∈ P := by
  let g : ℝ → P := fun t => ⟨f t, hm t⟩
  have hg : Continuous g := hf.subtype_mk _
  change (∫ t in a..b, P.subtypeL (g t)) ∈ P
  rw [P.subtypeL.intervalIntegral_comp_comm (hg.intervalIntegrable a b)]
  exact (∫ t in a..b, g t).property

lemma primitive_mem_submodule (P : Submodule ℝ E) {f : ℝ → E}
    (hf : Continuous f) (hm : ∀ t, f t ∈ P) (x : ℝ) : primitive f x ∈ P := by
  apply P.sub_mem (intervalIntegral_mem_submodule P hf hm 0 x)
  exact intervalIntegral_mem_submodule P (rawPrimitive_continuous hf)
    (fun t => intervalIntegral_mem_submodule P hf hm 0 t) 0 1

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
