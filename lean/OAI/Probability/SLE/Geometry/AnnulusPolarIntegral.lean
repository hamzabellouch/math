import OAI.Probability.SLE.AngularLaws
import OAI.Probability.SLE.Geometry.PolarLaplacianFlux

namespace OAI

/-! Polar change of variables on a finite annulus. -/
noncomputable section
open Set Filter Metric Function Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian

namespace SLEExactGauge

lemma annulus_integral_polar_rectangle (g : ℂ → ℝ) {a R : ℝ} (ha : 0<a) :
    (∫ z in {z : ℂ | a<‖z‖ ∧ ‖z‖<R}, g z)=
      ∫ p in Ioo a R ×ˢ Ioo (-Real.pi) Real.pi, p.1*g (polarPoint p.1 p.2) := by
  let A := {z : ℂ | a<‖z‖ ∧ ‖z‖<R}
  let T : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi
  let S : Set (ℝ × ℝ) := Ioo a R ×ˢ Ioo (-Real.pi) Real.pi
  have hA : MeasurableSet A :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Ioo
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hST : S⊆T := prod_mono (fun r hr => ha.trans hr.1) subset_rfl
  let f : ℂ → ℝ := A.indicator g
  calc
    _ = ∫ z, f z := (integral_indicator hA).symm
    _ = ∫ p in T, p.1 • f (Complex.polarCoord.symm p) :=
      (Complex.integral_comp_polarCoord_symm f).symm
    _ = ∫ p in T, S.indicator (fun p : ℝ × ℝ => p.1*g (polarPoint p.1 p.2)) p := by
      apply setIntegral_congr_fun hT
      intro p hp
      have hn : ‖Complex.polarCoord.symm p‖=p.1 := by
        rw [Complex.norm_polarCoord_symm,abs_of_pos hp.1]
      by_cases hr : p.1∈Ioo a R
      · have hz : Complex.polarCoord.symm p∈A := by
          change a<‖_‖ ∧ ‖_‖<R
          rwa [hn]
        have hs : p∈S := ⟨hr,hp.2⟩
        simp only [f,indicator_of_mem hz,indicator_of_mem hs,smul_eq_mul,polarPoint_eq_polarCoord]
      · have hz : Complex.polarCoord.symm p∉A := by
          change ¬(a<‖_‖ ∧ ‖_‖<R)
          simpa only [hn,mem_Ioo] using hr
        have hs : p∉S := fun hs => hr hs.1
        simp only [f,indicator_of_notMem hz,indicator_of_notMem hs,smul_zero]
    _ = _ := by
      rw [integral_indicator hS,Measure.restrict_restrict hS,inter_eq_left.mpr hST]

lemma annulus_integral_polar (g : ℂ → ℝ) {a R : ℝ} (ha : 0<a) (haR : a≤R)
    (hc : ∀ z : ℂ, a≤‖z‖ → ‖z‖≤R → ContinuousAt g z) :
    (∫ z in {z : ℂ | a<‖z‖ ∧ ‖z‖<R}, g z)=
      ∫ r in a..R, ∫ θ in -Real.pi..Real.pi, r*g (polarPoint r θ) := by
  let G (p : ℝ × ℝ) := p.1*g (polarPoint p.1 p.2)
  have hGc : ContinuousOn G (Icc a R ×ˢ Icc (-Real.pi) Real.pi) := by
    intro p hp
    have hn : ‖polarPoint p.1 p.2‖=p.1 := by
      rw [polarPoint_norm,abs_of_pos (ha.trans_le hp.1.1)]
    exact (continuousAt_fst.mul ((hc _ (by rw [hn]; exact hp.1.1)
      (by rw [hn]; exact hp.1.2)).comp (f := fun p : ℝ × ℝ => polarPoint p.1 p.2)
      polarPoint_contDiff.continuous.continuousAt)).continuousWithinAt
  have hi : IntegrableOn G (Ioo a R ×ˢ Ioo (-Real.pi) Real.pi) :=
    (hGc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [annulus_integral_polar_rectangle g ha,Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod] at hi
  rw [setIntegral_prod _ hi]
  simp_rw [←integral_Ioc_eq_integral_Ioo]
  rw [←intervalIntegral.integral_of_le haR]
  congr 1
  ext r
  exact (intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi≤Real.pi)).symm

lemma annulus_integral_laplacian_flux {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0<a) (haR : a≤R)
    (hu : ∀ z : ℂ, a≤‖z‖ → ‖z‖≤R → ContDiffAt ℝ 2 u z) :
    (∫ z in {z : ℂ | a<‖z‖ ∧ ‖z‖<R}, (Δ u) z)=
      (∫ θ in -Real.pi..Real.pi, radialLaplacianFlux u (R,θ))-
      (∫ θ in -Real.pi..Real.pi, radialLaplacianFlux u (a,θ)) := by
  rw [annulus_integral_polar _ ha haR
    (fun z hz hzR => plane_laplacian_continuousAt (hu z hz hzR))]
  exact annulus_laplacian_flux ha haR hu

end SLEExactGauge

end

end OAI
