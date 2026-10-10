import OAI.Geometry.RCD.Sobolev.BochnerWeakSubsolution
import OAI.Geometry.RCD.Sobolev.PoissonHessianInput

namespace OAI

/-! # The actual Poisson energy as a weak subsolution -/

open Set Metric Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The one-dimensional span of a constant-source solution is enough for
the finite-span Bochner input. -/
theorem LocalPoissonHessianInput.energy_subsolution {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hess : LocalPoissonHessianInput hX)
    (κ : ℝ) (hκ : 0 ≤ κ) (hK : -κ ≤ K) (p : X) (r : ℝ) (hr : 0 < r)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ) (L : ℝ≥0)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) f c)
    (hgrad : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L:ℝ)^2) :
    ∃ (e : SobolevSpace (hausdorff n X) hX.quadratic) (B : ℝ), 0 ≤ B ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic e =ᵐ[(hausdorff n X).restrict (ball p (2*r))]
        localGamma (hausdorff n X) hX.quadratic f f ∧
      (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic e x| ≤ B) ∧
      IsWeakSubsolutionOn (hausdorff n X) hX.quadratic (ball p (2*r)) e (2*κ) := by
  let μ := hausdorff n X
  let U : Euclidean (n+2) →L[ℝ] SobolevSpace μ hX.quadratic :=
    (EuclideanSpace.proj (0 : Fin (n+2))).smulRight f
  let ell : Euclidean (n+2) →ₗ[ℝ] ℝ := c • EuclideanSpace.projₗ 0
  have hUv (v : Euclidean (n+2)) : U v = v 0 • f := rfl
  have hc (v : Euclidean (n+2)) :
      IsConstantLaplacianOn μ hX.quadratic (ball p (8*r)) (U v) (ell v) := by
    simpa only [hUv,ell,LinearMap.smul_apply,EuclideanSpace.projₗ,PiLp.projₗ_apply,
      smul_eq_mul,mul_comm] using hf.smul μ hX.quadratic (v 0)
  have hg (v : Euclidean (n+2)) :
      ∀ᵐ x ∂μ.restrict (ball p (8*r)), localGamma μ hX.quadratic (U v) (U v) x ≤
        (L:ℝ)^2*‖v‖^2 := by
    rw [hUv]
    have hv : |v 0| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v 0
    filter_upwards [hgrad,
      ae_restrict_of_ae (localGamma_smul_left μ hX.quadratic (v 0) f (v 0 • f)),
      ae_restrict_of_ae (localGamma_smul_right μ hX.quadratic (v 0) f f)] with x hx hl hr'
    rw [hl,hr']
    calc
      _ = (v 0)^2*localGamma μ hX.quadratic f f x := by ring
      _ ≤ (v 0)^2*(L:ℝ)^2 := mul_le_mul_of_nonneg_left hx (sq_nonneg _)
      _ ≤ (L:ℝ)^2*‖v‖^2 := by
        have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hv 2) (sq_nonneg (L:ℝ))
        simpa only [sq_abs,mul_comm] using hh
  obtain ⟨M,hM,_,_⟩ := hess κ hκ hK p r hr L U ell hc hg
  let v : Euclidean (n+2) := EuclideanSpace.single 0 1
  obtain ⟨G⟩ := hM v
  have hv : U v = f := by simp [hUv,v]
  refine ⟨G.energy,((L^2*‖v‖₊^2:ℝ≥0):ℝ),by positivity,?_,G.bounded,?_⟩
  · simpa only [hv] using G.representative
  · exact G.weak_subsolution μ hX.quadratic

end RegularPointCoordinates

end

end OAI
