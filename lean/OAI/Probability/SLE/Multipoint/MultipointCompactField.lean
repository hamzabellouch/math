import OAI.Probability.SLE.Multipoint.MultipointDiscountedField

namespace OAI

/-! Compact smooth tests agreeing with the discounted product on each
bounded localization region. -/

noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge.Multipoint

theorem exists_compact_discounted_field {ι : Type*} [Fintype ι]
    (s : Finset ι) (κ : ℝ) (D σ : ι → ℝ) (hD : ∀ i ∈ s, 0 < D i)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ φ : ((ι → ℂ × ℝ) × ℝ) × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ (∀ p, 0 ≤ φ p) ∧
      (∀ z x, ‖(z,x)‖ ≤ R → φ (z,x) = discountedProduct s κ D σ z x) ∧
      (∀ z x, ‖(z,x)‖ ≤ R →
        fderiv ℝ φ (z,x) =
          fderiv ℝ (fun p => discountedProduct s κ D σ p.1 p.2) (z,x)) ∧
      (∀ z x, ‖(z,x)‖ ≤ R → iteratedDeriv 2 (fun y => φ (z,y)) x =
        iteratedDeriv 2 (discountedProduct s κ D σ z) x) := by
  let b : ContDiffBump (0 : ((ι → ℂ × ℝ) × ℝ) × ℝ) :=
    ⟨R+1, R+2, by linarith, by linarith⟩
  let φ := fun p : ((ι → ℂ × ℝ) × ℝ) × ℝ => b p*discountedProduct s κ D σ p.1 p.2
  have hnear (p : ((ι → ℂ × ℝ) × ℝ) × ℝ) (hp : ‖p‖ ≤ R) :
      φ =ᶠ[𝓝 p] (fun q => discountedProduct s κ D σ q.1 q.2) := by
    have hball : p ∈ Metric.ball (0 : ((ι → ℂ × ℝ) × ℝ) × ℝ) b.rIn := by
      simp only [Metric.mem_ball, dist_zero_right]
      change ‖p‖ < R+1
      linarith
    filter_upwards [b.eventuallyEq_one_of_mem_ball hball] with q hq
    simp only [φ, hq, Pi.one_apply, one_mul]
  refine ⟨φ, b.contDiff.mul (discountedProduct_contDiff s κ D σ), b.hasCompactSupport.mul_right,
    ?_, (fun z x h => (hnear (z,x) h).eq_of_nhds), ?_, ?_⟩
  · intro p
    apply mul_nonneg b.nonneg
    apply mul_nonneg (Real.exp_pos _).le
    exact (Finset.prod_pos (fun i hi => regularizedLogFactor_pos κ (D i) (σ i) (hD i hi) _ _)).le
  · intro z x h
    exact (hnear (z,x) h).fderiv_eq
  · intro z x h
    have he := (hnear (z,x) h).comp_tendsto
      ((continuous_const.prodMk continuous_id).tendsto x)
    exact he.iteratedDeriv_eq 2

lemma discountedProduct_pair_directional {ι : Type*} [Fintype ι]
    (s : Finset ι) (κ : ℝ) (D σ : ι → ℝ)
    (z v : (ι → ℂ × ℝ) × ℝ) (x : ℝ) :
    fderiv ℝ (fun p => discountedProduct s κ D σ p.1 p.2) (z,x) (v,0) =
      fderiv ℝ (fun q => discountedProduct s κ D σ q x) z v := by
  have hd := ((discountedProduct_contDiff s κ D σ).differentiable (by simp)) (z,x)
  have hp := (hasFDerivAt_id (𝕜 := ℝ) z).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) (E := (ι → ℂ × ℝ) × ℝ) x z)
  have hc := (hd.hasFDerivAt.comp z hp).fderiv
  have he := congrArg (fun A : ((ι → ℂ × ℝ) × ℝ) →L[ℝ] ℝ => A v) hc
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, id_eq, zero_apply] using he.symm

theorem compact_discounted_generator_nonpos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (D σ : ι → ℝ) (z : ι → ℂ × ℝ) (b x : ℝ)
    (hD : ∀ i ∈ s, 0 < D i) (hσ : ∀ i ∈ s, σ i ≤ 1)
    (hδ : ∀ i ∈ s, branchRegulator κ (D i) (σ i) (z i) ≤ 1)
    (φ : ((ι → ℂ × ℝ) × ℝ) × ℝ → ℝ)
    (hφD : fderiv ℝ φ ((z,b),x) =
      fderiv ℝ (fun p => discountedProduct s κ D σ p.1 p.2) ((z,b),x))
    (hφ2 : iteratedDeriv 2 (fun y => φ ((z,b),y)) x =
      iteratedDeriv 2 (discountedProduct s κ D σ (z,b)) x) :
    fderiv ℝ φ ((z,b),x)
        (((fun i => physicalLogLoewnerField (Real.sqrt κ*x) (z i)),
          productDriftCost s κ D σ z x),0) +
      (1/2 : ℝ)*iteratedDeriv 2 (fun y => φ ((z,b),y)) x ≤ 0 := by
  rw [hφD, hφ2, discountedProduct_pair_directional]
  exact discountedProduct_generator_nonpos s κ hκ hκ8 D σ z b x hD hσ hδ

end SLEExactGauge.Multipoint

end

end OAI
