import OAI.Analysis.CircleDomains.Rigidity.ConductivityFlux
import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevJacobianReplacement
import OAI.Analysis.CircleDomains.Sobolev.SmoothImageArea

namespace OAI

/-! The weak conductivity Jacobian has the signed area of the actual
image circle. The two interior replacements are constructed; locality
removes their compact errors before applying the smooth Green identity. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem holomorphic_physical_re_smooth {φ : ℂ → ℂ} {F : Set EuclideanPlane}
    (hF : IsClosed F) (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (φ (complexPlaneCoordinates x)).re) Fᶜ := by
  have hO : IsOpen (complexPlaneCoordinates '' F)ᶜ :=
    (complexPlaneCoordinates.toHomeomorph.isClosedMap _ hF).isOpen_compl
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) φ (complexPlaneCoordinates '' F)ᶜ :=
    (hh.contDiffOn hO).restrict_scalars ℝ
  have hp := hc.comp complexPlaneCoordinates.contDiff.contDiffOn
    (show MapsTo complexPlaneCoordinates Fᶜ (complexPlaneCoordinates '' F)ᶜ from by
      intro x hx hm
      obtain ⟨y, hy, heq⟩ := hm
      exact hx (complexPlaneCoordinates.injective heq ▸ hy))
  exact Complex.reCLM.contDiff.contDiffOn.comp hp (mapsTo_univ _ _)

 theorem PlaneLocalWeakComplex.jacobian_boundary
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (hgreen : UnorientedFiniteCircleGreenFormula) (hφ : Continuous φ)
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hh : DifferentiableOn ℂ φ (complexPlaneCoordinates '' F)ᶜ)
    {r₀ R : ℝ} (hr₀ : 0 < r₀) (hFr : F ⊆ ball 0 r₀) (hR : r₀ < R) :
    (∫ x in ball (0 : EuclideanPlane) R,
      D.realGradient x 0 * D.imagGradient x 1 -
        D.realGradient x 1 * D.imagGradient x 0) =
      signedCurveArea (φ ∘ unitCircleParam 0 R) := by
  have hcont := hφ.comp complexPlaneCoordinates.continuous
  obtain ⟨a, e, _he, ha, _hse, _hsube, _hue, hexta⟩ := exists_smooth_exterior_replacement hF hFr
    (D.realWitness hcont r₀) (holomorphic_physical_re_smooth hF.isClosed hh)
  obtain ⟨b, f, _hf, hb, _hsf, _hsubf, _huf, hextb⟩ := exists_smooth_exterior_replacement hF hFr
    (D.imagWitness hcont r₀) (holomorphic_physical_im_smooth hF.isClosed hh)
  have hRpos : 0 < R := hr₀.trans hR
  let A : DeGiorgi.MemW1pWitness 2 a (ball 0 (R+1)) :=
    smoothPlaneSobolevWitness isOpen_ball (ha.of_le (by simp)).contDiffOn
      (continuous_memLp_ball ha.continuous (R+1))
      (fun i => continuous_memLp_ball
        ((ha.continuous_fderiv (by simp)).clm_apply continuous_const) (R+1))
  let B : DeGiorgi.MemW1pWitness 2 b (ball 0 (R+1)) :=
    smoothPlaneSobolevWitness isOpen_ball (hb.of_le (by simp)).contDiffOn
      (continuous_memLp_ball hb.continuous (R+1))
      (fun i => continuous_memLp_ball
        ((hb.continuous_fderiv (by simp)).clm_apply continuous_const) (R+1))
  have houtside {x : EuclideanPlane} (hx : x ∉ ball 0 R) : x ∉ ball 0 r₀ :=
    fun hm => hx (ball_subset_ball hR.le hm)
  have hj := local_sobolev_jacobian_ball_replacement (show R < R+1 by linarith)
    (D.realWitness hcont (R+1)) (D.imagWitness hcont (R+1)) A B
    (fun x hx => (hexta (houtside hx.2)).symm)
    (fun x hx => (hextb (houtside hx.2)).symm)
  change (∫ x in ball (0 : EuclideanPlane) R,
      D.realGradient x 0 * D.imagGradient x 1 - D.realGradient x 1 * D.imagGradient x 0) =
    (∫ x in ball (0 : EuclideanPlane) R,
      fderiv ℝ a x (EuclideanSpace.single 0 1) * fderiv ℝ b x (EuclideanSpace.single 1 1) -
        fderiv ℝ a x (EuclideanSpace.single 1 1) * fderiv ℝ b x (EuclideanSpace.single 0 1)) at hj
  rw [hj, smooth_physical_disk_jacobian hgreen R hRpos ha hb]
  let Ψ : ℂ → ℂ := fun z => (a (complexPlaneCoordinates.symm z) : ℂ) +
    Complex.I * (b (complexPlaneCoordinates.symm z) : ℂ)
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ :=
    (Complex.ofRealCLM.contDiff.comp (ha.comp complexPlaneCoordinates.symm.contDiff)).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (hb.comp complexPlaneCoordinates.symm.contDiff)))
  have hre : (fun z => (Ψ z).re) = fun z => a (complexPlaneCoordinates.symm z) := by
    funext z
    simp [Ψ]
  have him : (fun z => (Ψ z).im) = fun z => b (complexPlaneCoordinates.symm z) := by
    funext z
    simp [Ψ]
  have hcurve : Ψ ∘ unitCircleParam 0 R = φ ∘ unitCircleParam 0 R := by
    funext t
    have hn : ‖complexPlaneCoordinates.symm (unitCircleParam 0 R t)‖ = R := by
      rw [← complexPlaneCoordinates_norm, ContinuousLinearEquiv.apply_symm_apply]
      simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRpos]
    have hout : complexPlaneCoordinates.symm (unitCircleParam 0 R t) ∉ ball 0 r₀ := by
      simp only [mem_ball, dist_zero_right, hn]
      exact not_lt_of_gt hR
    have haeq := hexta hout
    have hbeq := hextb hout
    simp only [ContinuousLinearEquiv.apply_symm_apply] at haeq hbeq
    apply Complex.ext <;> simp [Ψ, haeq, hbeq]
  have hγ : ContDiff ℝ (⊤ : ℕ∞) (unitCircleParam 0 R) :=
    (contDiff_circleMap 0 R).comp (contDiff_const.mul contDiff_id)
  rw [← hcurve, signedCurveArea_smooth_image hΨ hγ]
  simp only [him]
  congr 1 <;> funext z <;> rw [congrFun hre z]

end CircleDomainRigidity

end

end OAI
