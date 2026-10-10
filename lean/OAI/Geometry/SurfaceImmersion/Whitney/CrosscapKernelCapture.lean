import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceDirectionEstimates

namespace OAI

/-! A kernel near a crosscap is captured in the same affine direction
chart, with an explicit bound on its direction parameter. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma tangentRay_sub (b : Bool) (s t : ℝ) :
    tangentRay b s-tangentRay b t = (s-t) • tangentRayVelocity b := by
  cases b <;> ext i <;> fin_cases i <;> simp [tangentRay,tangentRayVelocity]

lemma exists_fixed_tangentRay_kernel (L : Base →L[ℝ] ProjectionTarget 3)
    (b : Bool) (hL : ¬ Function.Injective L) (hv : L (tangentRayVelocity b) ≠ 0) :
    ∃ t : ℝ, L (tangentRay b t) = 0 := by
  change ¬ (∀ u v : Base, L u = L v → u = v) at hL
  push Not at hL
  obtain ⟨u,v,he,hne⟩ := hL
  have hn : u-v ≠ 0 := sub_ne_zero.mpr hne
  have hz : L (u-v) = 0 := by rw [map_sub,he,sub_self]
  let w := u-v
  have hw : w ≠ 0 := hn
  change L w = 0 at hz
  cases b
  · have h0 : w 0 ≠ 0 := by
      intro h0
      have hew : w = w 1 • tangentRayVelocity false := by
        ext i
        fin_cases i <;> simp [tangentRayVelocity,h0]
      rw [hew,map_smul] at hz
      have h1 := (smul_eq_zero.mp hz).resolve_right hv
      apply hw
      ext i
      fin_cases i <;> simp [h0,h1]
    refine ⟨w 1/w 0,?_⟩
    have hew : w = w 0 • tangentRay false (w 1/w 0) := by
      ext i
      fin_cases i
      · simp [tangentRay]
      · change w 1 = w 0*(w 1/w 0)
        field_simp
    rw [hew,map_smul] at hz
    exact (smul_eq_zero.mp hz).resolve_left h0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      have hew : w = w 0 • tangentRayVelocity true := by
        ext i
        fin_cases i <;> simp [tangentRayVelocity,h1]
      rw [hew,map_smul] at hz
      have h0 := (smul_eq_zero.mp hz).resolve_right hv
      apply hw
      ext i
      fin_cases i <;> simp [h0,h1]
    refine ⟨w 0/w 1,?_⟩
    have hew : w = w 1 • tangentRay true (w 0/w 1) := by
      ext i
      fin_cases i
      · change w 0 = w 1*(w 0/w 1)
        field_simp
      · simp [tangentRay]
    rw [hew,map_smul] at hz
    exact (smul_eq_zero.mp hz).resolve_left h1

lemma exists_near_tangentRay_kernel (L : Base →L[ℝ] ProjectionTarget 3)
    (b : Bool) (t₀ η : ℝ) (hL : ¬ Function.Injective L)
    (hv : L (tangentRayVelocity b) ≠ 0)
    (hsmall : ‖L (tangentRay b t₀)‖ < η*‖L (tangentRayVelocity b)‖) :
    ∃ t : ℝ, |t-t₀| < η ∧ L (tangentRay b t) = 0 := by
  obtain ⟨t,ht⟩ := exists_fixed_tangentRay_kernel L b hL hv
  refine ⟨t,?_,ht⟩
  have he : L (tangentRay b t₀) = (t₀-t) • L (tangentRayVelocity b) := by
    calc
      _ = L (tangentRay b t₀)-L (tangentRay b t) := by rw [ht,sub_zero]
      _ = L (tangentRay b t₀-tangentRay b t) := (map_sub L _ _).symm
      _ = _ := by rw [tangentRay_sub,map_smul]
  rw [he,norm_smul,Real.norm_eq_abs,abs_sub_comm] at hsmall
  exact (mul_lt_mul_iff_left₀ (norm_pos_iff.mpr hv)).mp hsmall

theorem kernel_capture_near (L : Base →L[ℝ] ProjectionTarget 3)
    (b : Bool) (t₀ : ℝ) (hzero : L (tangentRay b t₀) = 0)
    (hv : L (tangentRayVelocity b) ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : Base →L[ℝ] ProjectionTarget 3,
      ‖H-L‖ < δ → ¬ Function.Injective H →
      ∃ t : ℝ, |t-t₀| < η ∧ H (tangentRay b t) = 0 := by
  let U := {H : Base →L[ℝ] ProjectionTarget 3 |
    ‖H (tangentRay b t₀)‖ < η*‖H (tangentRayVelocity b)‖}
  have hU : IsOpen U := isOpen_lt
    (ContinuousLinearMap.apply ℝ (ProjectionTarget 3) (tangentRay b t₀)).continuous.norm
    (continuous_const.mul
      (ContinuousLinearMap.apply ℝ (ProjectionTarget 3) (tangentRayVelocity b)).continuous.norm)
  have hL : L ∈ U := by
    change ‖L (tangentRay b t₀)‖ < η*‖L (tangentRayVelocity b)‖
    rw [hzero,norm_zero]
    exact mul_pos hη (norm_pos_iff.mpr hv)
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hL)
  refine ⟨δ,hδ,?_⟩
  intro H hnear hH
  have hHU : H ∈ U := hδU (by simpa only [mem_ball,dist_eq_norm] using hnear)
  have hHv : H (tangentRayVelocity b) ≠ 0 := by
    intro hn
    change ‖H (tangentRay b t₀)‖ < η*‖H (tangentRayVelocity b)‖ at hHU
    rw [hn,norm_zero,mul_zero] at hHU
    exact (not_lt_of_ge (norm_nonneg _)) hHU
  exact exists_near_tangentRay_kernel H b t₀ η hH hHv hHU

lemma crosscap_transverse_derivative_ne_zero {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (b : Bool) (z : Base × ℝ)
    (hreg : Function.Injective (fderiv ℝ (surfaceDirection f b) z)) :
    fderiv ℝ f z.1 (tangentRayVelocity b) ≠ 0 := by
  intro hn
  rw [(surfaceDirection_hasFDerivAt hf b z).fderiv] at hreg
  have hval : surfaceDirectionLinearization f b z ((0 : Base),1) = 0 := by
    change fderiv ℝ f z.1 ((1:ℝ) • tangentRayVelocity b)+
      fderiv ℝ (fderiv ℝ f) z.1 0 (tangentRay b z.2) = 0
    simp [hn]
  have he := hreg (hval.trans (map_zero _).symm)
  have hh := congrArg Prod.snd he
  exact one_ne_zero hh

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
