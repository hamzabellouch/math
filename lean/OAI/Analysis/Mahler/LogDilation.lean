import OAI.Analysis.Mahler.SphereFluxLimit

namespace OAI

open Complex MeasureTheory Metric Filter Set
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

lemma boundaryForm_congr {u v : E → ℂ} {x : E} (h : u =ᶠ[𝓝 x] v) (k : ℕ) :
    boundaryForm u k x = boundaryForm v k x := by
  have hf : oneForm (dcLinear u) =ᶠ[𝓝 x] oneForm (dcLinear v) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    simp only [oneForm, dcLinear, hy]
  unfold boundaryForm extDeriv
  rw [hf.eq_of_nhds, hf.fderiv_eq]

/-- The rescaling epsilon^(-2m) tau(epsilon z), followed by log. -/
noncomputable def rescaledLog (τ : E → ℝ) (m : ℕ) (r : ℝ) (x : E) : ℂ :=
  (Real.log ((r^(2*m))⁻¹ * τ (r • x)) : ℂ)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma rescaledLog_eventually [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {τ : E → ℝ} {r : ℝ} {x : E} (m : ℕ)
    (hr : 0 < r) (hτ : ContinuousAt τ (r • x)) (hp : 0 < τ (r • x)) :
    rescaledLog τ m r =ᶠ[𝓝 x]
      (fun y => (Real.log (τ (r • y)) : ℂ) - ((2*m : ℕ) : ℂ) * (Real.log r : ℂ)) := by
  have hc : ContinuousAt (fun y : E => τ (r • y)) x :=
    hτ.comp (realDilation r).continuous.continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hp)] with y hy
  unfold rescaledLog
  rw [Real.log_mul (inv_ne_zero (pow_ne_zero _ hr.ne')) hy.ne', Real.log_inv, Real.log_pow]
  push_cast
  ring

/-- Literal logarithmic rescaling pulls back d^c log tau and every dd^c
factor, with no extra scale or orientation sign. -/
theorem boundaryForm_rescaledLog {τ : E → ℝ} {r : ℝ} {x : E}
    (hr : 0 < r) (hτ : ContinuousAt τ (r • x)) (hp : 0 < τ (r • x))
    (hu : ContDiffAt ℝ 2 (fun y => (Real.log (τ y) : ℂ)) (r • x)) (m k : ℕ) :
    boundaryForm (rescaledLog τ m r) k x =
      (boundaryForm (fun y => (Real.log (τ y) : ℂ)) k (r • x)).compLinearMap
        (realDilation r).toLinearMap := by
  rw [boundaryForm_congr (rescaledLog_eventually m hr hτ hp) k]
  exact boundaryForm_dilation hu _ k

/-- Equality for actual Euclidean surface integrals, before taking a limit. -/
theorem smallSphereFlux_log_eq {k m : ℕ} {τ : ComplexEuclidean (k+1) → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hτ : ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContinuousAt τ (r • (z : ComplexEuclidean (k+1))))
    (hp : ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      0 < τ (r • (z : ComplexEuclidean (k+1))))
    (hu : ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContDiffAt ℝ 2 (fun y => (Real.log (τ y) : ℂ)) (r • (z : ComplexEuclidean (k+1)))) :
    smallSphereFlux k (fun y => (Real.log (τ y) : ℂ)) r =
      unitSphereFlux k (rescaledLog τ m r) := by
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only
  rw [boundaryForm_rescaledLog hr (hτ z) (hp z) (hu z) m k, boundaryForm_pullback_scale]
  unfold sphereDensity
  rw [wedge_smul_right]
  rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma continuousOn_actualRealComplexJet [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {u : E → ℂ} {K : Set E}
    (hu : ∀ x ∈ K, ContDiffAt ℝ 2 u x) : ContinuousOn (actualRealComplexJet u) K := by
  intro x hx
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ u) x := (hu x hx).fderiv_right (by norm_num)
  have h2 : ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ u)) x := h1.fderiv_right (by norm_num)
  exact (h1.continuousAt.prodMk h2.continuousAt).continuousWithinAt

/-- A limit theorem whose analytic inputs are C^2 regularity
and uniform first/second log jets on a compact annulus (or any compact set
containing the sphere). Transport and integral convergence are conclusions. -/
theorem smallSphereFlux_log_tendsto {k m : ℕ} {τ : ComplexEuclidean (k+1) → ℝ}
    {v : ComplexEuclidean (k+1) → ℂ} {K : Set (ComplexEuclidean (k+1))}
    (hK : IsCompact K) (hS : sphere (0 : ComplexEuclidean (k+1)) 1 ⊆ K)
    (hv : ∀ x ∈ K, ContDiffAt ℝ 2 v x)
    (hu : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ x ∈ K, ContDiffAt ℝ 2 (rescaledLog τ m r) x)
    (hτ : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContinuousAt τ (r • (z : ComplexEuclidean (k+1))))
    (hp : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      0 < τ (r • (z : ComplexEuclidean (k+1))))
    (hlog : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContDiffAt ℝ 2 (fun y => (Real.log (τ y) : ℂ)) (r • (z : ComplexEuclidean (k+1))))
    (h1 : TendstoUniformlyOn (fun r => fderiv ℝ (rescaledLog τ m r))
      (fderiv ℝ v) (𝓝[>] 0) K)
    (h2 : TendstoUniformlyOn (fun r => fderiv ℝ (fderiv ℝ (rescaledLog τ m r)))
      (fderiv ℝ (fderiv ℝ v)) (𝓝[>] 0) K) :
    Tendsto (smallSphereFlux k (fun y => (Real.log (τ y) : ℂ))) (𝓝[>] 0)
      (𝓝 (unitSphereFlux k v)) := by
  have ht := unitSphereFlux_tendsto hK hS (continuousOn_actualRealComplexJet hv)
    (hu.mono (fun r hr => continuousOn_actualRealComplexJet hr))
    (fun x hx => ((hv x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    (hu.mono (fun r hr x hx => ((hr x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))) h1 h2
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin, hτ, hp, hlog] with r hr htr hpr hlr
  exact (smallSphereFlux_log_eq hr htr hpr hlr).symm

end Mahler

end OAI
