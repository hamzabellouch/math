import OAI.Probability.SLE.RadiusClocks

namespace OAI

/-! The unweighted polar divergence identity on a closed annulus. -/
noncomputable section
open Set Filter Metric Function Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian

namespace SLEExactGauge

def radialLaplacianFlux (u : ℂ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * fderiv ℝ u (polarPoint p.1 p.2) (circleMap 0 1 p.2)

def angularLaplacianFlux (u : ℂ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1⁻¹ * fderiv ℝ u (polarPoint p.1 p.2) (polarPoint p.1 p.2 * I)

lemma radialLaplacianFlux_differentiableAt {u : ℂ → ℝ} {r θ : ℝ}
    (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    DifferentiableAt ℝ (radialLaplacianFlux u) (r,θ) := by
  have hp := polarPoint_contDiff.differentiable (by simp) (r,θ)
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).comp (r,θ) hp
  exact differentiableAt_fst.mul (hd.clm_apply (by unfold circleMap; fun_prop))

lemma angularLaplacianFlux_differentiableAt {u : ℂ → ℝ} {r θ : ℝ}
    (hr : r≠0) (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    DifferentiableAt ℝ (angularLaplacianFlux u) (r,θ) := by
  have hp := polarPoint_contDiff.differentiable (by simp) (r,θ)
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).comp (r,θ) hp
  exact (differentiableAt_fst.inv hr).mul (hd.clm_apply (hp.mul_const I))

lemma radialLaplacianFlux_radial_hasDeriv {u : ℂ → ℝ} {r θ : ℝ}
    (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    HasDerivAt (fun s => radialLaplacianFlux u (s,θ))
      (fderiv ℝ u (polarPoint r θ) (circleMap 0 1 θ)+
        r*fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (circleMap 0 1 θ) (circleMap 0 1 θ)) r := by
  convert! (hasDerivAt_id r).mul (radial_second_hasDeriv hu) using 1
  simp only [one_mul,id_eq]

lemma angularLaplacianFlux_angular_hasDeriv {u : ℂ → ℝ} {r θ : ℝ}
    (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    HasDerivAt (fun φ => angularLaplacianFlux u (r,φ))
      (r⁻¹*(fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (polarPoint r θ*I) (polarPoint r θ*I)-
        fderiv ℝ u (polarPoint r θ) (polarPoint r θ))) θ :=
  (angular_second_hasDeriv hu).const_mul r⁻¹

lemma polarLaplacian_divergence {u : ℂ → ℝ} {r θ : ℝ}
    (hr : r≠0) (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    fderiv ℝ (radialLaplacianFlux u) (r,θ) (1,0)+
      fderiv ℝ (angularLaplacianFlux u) (r,θ) (0,1)=
        r*(Δ u) (polarPoint r θ) := by
  have hf := (radialLaplacianFlux_differentiableAt hu).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r θ))
  have hg := (angularLaplacianFlux_differentiableAt hr hu).hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_const θ r).prodMk (hasDerivAt_id θ))
  rw [hf.unique (radialLaplacianFlux_radial_hasDeriv hu),
    hg.unique (angularLaplacianFlux_angular_hasDeriv hu)]
  have he : fderiv ℝ u (polarPoint r θ) (polarPoint r θ)=
      r*fderiv ℝ u (polarPoint r θ) (circleMap 0 1 θ) := by
    conv_lhs => arg 2; rw [polarPoint]
    simp only [map_smul,smul_eq_mul]
  rw [he]
  have hh := polar_laplacian_identity (u := u) r θ
  apply (mul_left_cancel₀ hr)
  field_simp [hr]
  nlinarith only [hh]

lemma annulus_laplacian_flux {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0<a) (haR : a≤R)
    (hu : ∀ z : ℂ, a≤‖z‖ → ‖z‖≤R → ContDiffAt ℝ 2 u z) :
    (∫ r in a..R, ∫ θ in -Real.pi..Real.pi, r*(Δ u) (polarPoint r θ))=
      (∫ θ in -Real.pi..Real.pi, radialLaplacianFlux u (R,θ))-
      (∫ θ in -Real.pi..Real.pi, radialLaplacianFlux u (a,θ)) := by
  let S := uIcc a R ×ˢ uIcc (-Real.pi) Real.pi
  have hmem (p : ℝ × ℝ) (hp : p∈S) : p.1≠0 ∧ ContDiffAt ℝ 2 u (polarPoint p.1 p.2) := by
    have hr : p.1∈Icc a R := by simpa only [uIcc_of_le haR] using hp.1
    have hn : ‖polarPoint p.1 p.2‖=p.1 := by
      rw [polarPoint_norm,abs_of_pos (ha.trans_le hr.1)]
    exact ⟨(ha.trans_le hr.1).ne',hu _ (by rw [hn]; exact hr.1) (by rw [hn]; exact hr.2)⟩
  have hf : ContinuousOn (radialLaplacianFlux u) S := fun p hp =>
    (radialLaplacianFlux_differentiableAt (hmem p hp).2).continuousAt.continuousWithinAt
  have hg : ContinuousOn (angularLaplacianFlux u) S := fun p hp =>
    (angularLaplacianFlux_differentiableAt (hmem p hp).1 (hmem p hp).2).continuousAt.continuousWithinAt
  have hl : ContinuousOn (fun p : ℝ × ℝ => p.1*(Δ u) (polarPoint p.1 p.2)) S := by
    intro p hp
    exact (continuousAt_fst.mul ((plane_laplacian_continuousAt (hmem p hp).2).comp
      (f := fun p : ℝ × ℝ => polarPoint p.1 p.2)
      polarPoint_contDiff.continuous.continuousAt)).continuousWithinAt
  have he : EqOn (fun p : ℝ × ℝ => fderiv ℝ (radialLaplacianFlux u) p (1,0)+
      fderiv ℝ (angularLaplacianFlux u) p (0,1))
      (fun p => p.1*(Δ u) (polarPoint p.1 p.2)) S :=
    fun p hp => polarLaplacian_divergence (hmem p hp).1 (hmem p hp).2
  have hi : IntegrableOn (fun p : ℝ × ℝ => fderiv ℝ (radialLaplacianFlux u) p (1,0)+
      fderiv ℝ (angularLaplacianFlux u) p (0,1)) S :=
    (hl.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).congr_fun
      (fun p hp => (he hp).symm) (measurableSet_uIcc.prod measurableSet_uIcc)
  have hm : Ioo (min a R) (max a R) ×ˢ Ioo (min (-Real.pi) Real.pi) (max (-Real.pi) Real.pi) ⊆ S :=
    prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hh := integral2_divergence_prod_of_hasFDerivAt (radialLaplacianFlux u) (angularLaplacianFlux u)
    (fderiv ℝ (radialLaplacianFlux u)) (fderiv ℝ (angularLaplacianFlux u)) a (-Real.pi) R Real.pi hf hg
    (fun p hp => (radialLaplacianFlux_differentiableAt (hmem p (hm hp)).2).hasFDerivAt)
    (fun p hp => (angularLaplacianFlux_differentiableAt (hmem p (hm hp)).1
      (hmem p (hm hp)).2).hasFDerivAt) hi
  have hi_eq : (∫ r in a..R, ∫ θ in -Real.pi..Real.pi,
      fderiv ℝ (radialLaplacianFlux u) (r,θ) (1,0)+
        fderiv ℝ (angularLaplacianFlux u) (r,θ) (0,1))=
      ∫ r in a..R, ∫ θ in -Real.pi..Real.pi, r*(Δ u) (polarPoint r θ) := by
    apply intervalIntegral.integral_congr
    intro r hr
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact he ⟨hr,hθ⟩
  rw [hi_eq] at hh
  simpa only [angularLaplacianFlux,polarPoint_endpoints,sub_self,zero_add] using hh

end SLEExactGauge

end

end OAI
