import Mathlib
import OAI.Geometry.SmoothYau.Estimates.CoefficientEllipticFlux
import OAI.Geometry.SmoothYau.Smoothness.TestAsSmooth
import OAI.Geometry.SmoothYau.Spectrum.JointLocalLaplacian

namespace OAI

noncomputable section
namespace YauCounterexamples
open Set Filter Metric Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] (L : E ≃L[ℝ] F)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma directional_comp_equiv {f : E → ℝ} {y : F}
    (hf : DifferentiableAt ℝ f (L.symm y)) (v : E) :
    fderiv ℝ (f ∘ L.symm) y (L v) = fderiv ℝ f (L.symm y) v := by
  rw [fderiv_comp y hf L.symm.differentiableAt]
  simp only [L.symm.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    L.symm_apply_apply]

omit [FiniteDimensional ℝ F] in
lemma coefficientSchrodinger_metric_equiv (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ) (p : M) (y : F)
    (hy : L.symm y ∈ (chartAt E p).target)
    (a : CoordIndex E → CoordIndex E → SmoothScalar F) (V w : SmoothScalar F)
    (ha : ∀ᶠ z in 𝓝 y, ∀ i j,
      a i j z = Real.sqrt (metricCoefficients g p (L.symm z)).det *
        (metricCoefficients g p (L.symm z))⁻¹ i j)
    (hV : V y = lam * Real.sqrt (metricCoefficients g p (L.symm y)).det)
    (hw : (w : F → ℝ) =ᶠ[𝓝 y] (u ∘ (chartAt E p).symm) ∘ L.symm)
    (hsol : -laplaceBeltrami g u ((chartAt E p).symm (L.symm y)) =
      lam*u ((chartAt E p).symm (L.symm y))) :
    coefficientSchrodinger (fun i => L (Module.finBasis ℝ E i)) a V w y = 0 := by
  have hnh : ∀ᶠ z in 𝓝 y, L.symm z ∈ (chartAt E p).target :=
    L.symm.continuous.continuousAt.preimage_mem_nhds ((chartAt E p).open_target.mem_nhds hy)
  have he (i : CoordIndex E) :
      (fun z => ∑ j, a i j z * SmoothScalar.directional (L (Module.finBasis ℝ E j)) w z) =ᶠ[𝓝 y]
        (fun z => metricFlux g u p (L.symm z) i) := by
    filter_upwards [ha, hw.fderiv (𝕜 := ℝ),hnh] with z hza hzw hzt
    simp only [metricFlux, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [SmoothScalar.directional_apply,hzw,directional_comp_equiv L
      ((contDiffAt_inChart hu p hzt).differentiableAt (by simp))]
    rw [hza]; ring
  have heL : coefficientElliptic (fun i => L (Module.finBasis ℝ E i)) a w y =
      Real.sqrt (metricCoefficients g p (L.symm y)).det * localLaplacian g u p (L.symm y) := by
    rw [coefficientElliptic_flux]
    simp only [(he _).fderiv_eq]
    have hdiff (i : CoordIndex E) : DifferentiableAt ℝ (fun z => metricFlux g u p z i) (L.symm y) :=
      (differentiableAt_pi.mp (differentiableAt_metricFlux hu g p hy)) i
    simp only [show ∀ i, fderiv ℝ (fun z => metricFlux g u p (L.symm z) i) y
        (L (Module.finBasis ℝ E i)) = fderiv ℝ (fun z => metricFlux g u p z i) (L.symm y)
          (Module.finBasis ℝ E i) from fun i => directional_comp_equiv L (hdiff i) _]
    rw [localLaplacian, ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr
      (metricCoefficients_det_pos g p hy)).ne', one_mul]
  rw [laplaceBeltrami_inChart hu g p _ ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy] at hsol
  change coefficientElliptic (fun i => L (Module.finBasis ℝ E i)) a w y + V y*w y = 0
  rw [heL, hV, hw.eq_of_nhds]
  dsimp only [Function.comp_apply]
  have hh := congrArg (fun t : ℝ => Real.sqrt (metricCoefficients g p (L.symm y)).det * t) hsol
  nlinarith only [hh]

theorem exists_metric_ucp_model_equiv (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ)
    (hsol : ∀ x, -laplaceBeltrami g u x = lam*u x) (p : M) :
    ∃ (a : CoordIndex E → CoordIndex E → SmoothScalar F) (V w : SmoothScalar F) (r : ℝ),
      0 < r ∧ (∀ i j, a i j = a j i) ∧
      ball (L ((chartAt E p) p)) r ⊆ L.symm ⁻¹' (chartAt E p).target ∧
      (∀ y ∈ ball (L ((chartAt E p) p)) r, w y = u ((chartAt E p).symm (L.symm y))) ∧
      (∀ y ∈ ball (L ((chartAt E p) p)) r, Matrix.PosDef (fun i j => a i j y)) ∧
      (∀ y ∈ ball (L ((chartAt E p) p)) r,
        coefficientSchrodinger (fun i => L (Module.finBasis ℝ E i)) a V w y = 0) := by
  classical
  let ρ : F → ℝ := fun y => Real.sqrt (metricCoefficients g p (L.symm y)).det
  let G₀ : F → Matrix (CoordIndex E) (CoordIndex E) ℝ × (ℝ × ℝ) :=
    fun y => ((fun i j => ρ y * (metricCoefficients g p (L.symm y))⁻¹ i j),
      (lam*ρ y,u ((chartAt E p).symm (L.symm y))))
  let O := L.symm ⁻¹' (chartAt E p).target
  have hρ : ContDiffOn ℝ ∞ ρ O := (contDiffOn_metricDensity g p).comp
    L.symm.contDiff.contDiffOn (fun _ h => h)
  have hF : ContDiffOn ℝ ∞ G₀ O := by
    apply ContDiffOn.prodMk
    · exact contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j =>
        hρ.mul ((contDiffOn_metricInverse g p i j).comp L.symm.contDiff.contDiffOn (fun _ h => h))))
    · apply ContDiffOn.prodMk
      · exact contDiffOn_const.mul hρ
      · intro y hy
        exact ((contDiffAt_inChart hu p hy).comp y L.symm.contDiff.contDiffAt).contDiffWithinAt
  have hp : L ((chartAt E p) p) ∈ O := by
    simpa only [O, mem_preimage, L.symm_apply_apply] using
      (chartAt E p).map_source (mem_chart_source E p)
  have hO : IsOpen O := (chartAt E p).open_target.preimage L.symm.continuous
  obtain ⟨G,hG,he⟩ := smooth_extension_near_compact isCompact_singleton hO
    (singleton_subset_iff.mpr hp) hF
  have he' : G₀ =ᶠ[𝓝 (L ((chartAt E p) p))] G := he.filter_mono (nhds_le_nhdsSet (mem_singleton _))
  let a : CoordIndex E → CoordIndex E → SmoothScalar F := fun i j =>
    ⟨fun y => ((G y).1 i j + (G y).1 j i)/2, by
      change ContDiff ℝ ∞ (fun y => ((G y).1 i j + (G y).1 j i)/2)
      exact ((contDiff_pi.mp (contDiff_pi.mp hG.fst i) j).add
        (contDiff_pi.mp (contDiff_pi.mp hG.fst j) i)).div_const 2⟩
  let V : SmoothScalar F := ⟨fun y => (G y).2.1,hG.snd.fst⟩
  let w : SmoothScalar F := ⟨fun y => (G y).2.2,hG.snd.snd⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.eventually_nhds_iff.mp (he'.and (hO.mem_nhds hp))
  have heq (y : F) (hy : y ∈ ball (L ((chartAt E p) p)) r) :
      (∀ i j, a i j y = ρ y*(metricCoefficients g p (L.symm y))⁻¹ i j) ∧
        V y = lam*ρ y ∧ w y = u ((chartAt E p).symm (L.symm y)) := by
    have hny := hrsub hy
    have hsym (i j : CoordIndex E) : (metricCoefficients g p (L.symm y))⁻¹ j i =
        (metricCoefficients g p (L.symm y))⁻¹ i j := by
      have hh := congrArg (fun B : Matrix (CoordIndex E) (CoordIndex E) ℝ => B i j)
        (metricInverse_posDef g p hny.2).isHermitian
      simpa only [Matrix.conjTranspose_apply, star_trivial] using hh
    have hg : G y = G₀ y := hny.1.symm
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · change ((G y).1 i j+(G y).1 j i)/2 = _
      rw [hg]; dsimp only [G₀]; rw [hsym]; ring
    · change (G y).2.1 = _
      rw [hg]
    · change (G y).2.2 = _
      rw [hg]
  refine ⟨a,V,w,r,hr,?_,fun y hy => (hrsub hy).2,
    fun y hy => (heq y hy).2.2,?_,?_⟩
  · intro i j
    apply Subtype.ext; ext y
    change (_+_)/2 = (_+_)/2
    rw [add_comm]
  · intro y hy
    simp only [(heq y hy).1]
    exact (metricInverse_posDef g p (hrsub hy).2).smul (Real.sqrt_pos.mpr
      (metricCoefficients_det_pos g p (hrsub hy).2))
  · intro y hy
    apply coefficientSchrodinger_metric_equiv L g hu lam p y (hrsub hy).2 a V w
    · filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      exact (heq z hz).1
    · exact (heq y hy).2.1
    · filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      exact (heq z hz).2.2
    · exact hsol _
end YauCounterexamples


end

end OAI
