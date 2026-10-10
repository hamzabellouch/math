import OAI.Probability.SLE.Loewner.RadiusHalfPlaneHull

namespace OAI

/-! The inverse of the explicit half-disk chart is normalized at infinity
and stays within the radius of its argument. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

noncomputable def radiusHullInverse (R : ℝ) : ℂ → ℂ :=
  invFunOn (radiusHullMap R) (exteriorUpperRadius R)

lemma radiusHullInverse_mapsTo {R : ℝ} (hR : 0<R) :
    MapsTo (radiusHullInverse R) upperHalfPlane (exteriorUpperRadius R) :=
  (radiusHullMap_bijOn hR).surjOn.mapsTo_invFunOn

lemma radiusHullMap_inverse {R : ℝ} (hR : 0<R) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    radiusHullMap R (radiusHullInverse R z)=z :=
  (radiusHullMap_bijOn hR).surjOn.rightInvOn_invFunOn hz

lemma radiusHullInverse_differentiableOn {R : ℝ} (hR : 0<R) :
    DifferentiableOn ℂ (radiusHullInverse R) upperHalfPlane := by
  have ho : IsOpen (exteriorUpperRadius R) :=
    (isOpen_lt continuous_const continuous_norm).inter isOpen_upperHalfPlane
  simpa only [radiusHullInverse,(radiusHullMap_bijOn hR).image_eq] using
    (radiusHullMap_differentiableOn hR).invFunOn ho (radiusHullMap_bijOn hR).injOn

lemma radiusHullInverse_displacement {R : ℝ} (hR : 0<R) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    ‖radiusHullInverse R z-z‖≤R := by
  have hm := radiusHullInverse_mapsTo hR hz
  have hnorm : 0<‖radiusHullInverse R z‖ := hR.trans hm.1
  have hh := radiusHullMap_inverse hR hz
  rw [radiusHullMap_formula hR] at hh
  have he : radiusHullInverse R z-z = -((R:ℂ)^2/radiusHullInverse R z) := by
    linear_combination hh
  rw [he,norm_neg,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
  apply (div_le_iff₀ hnorm).mpr
  nlinarith [hm.1]

lemma ratio_one_of_bounded_displacement {F : ℂ → ℂ} {R : ℝ}
    (hF : ∀ z ∈ upperHalfPlane, ‖F z-z‖≤R) :
    Tendsto (fun z : ℂ => F z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 0) := by
    have hh : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
      simpa only [Metric.cobounded_eq_cocompact] using
        (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0))
    exact hh.mono_left inf_le_left
  have hbound : ∀ᶠ z in cocompact ℂ ⊓ 𝓟 upperHalfPlane,
      ‖(F z-z)/z‖≤R*‖z⁻¹‖ := by
    rw [eventually_inf_principal]
    apply Eventually.of_forall
    intro z hz
    rw [norm_div,norm_inv,div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hF z hz) (inv_nonneg.mpr (norm_nonneg _))
  have hlim : Tendsto (fun z : ℂ => R*‖z⁻¹‖)
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using hi.norm.const_mul R
  have hn := squeeze_zero' (Eventually.of_forall (fun z : ℂ => norm_nonneg ((F z-z)/z))) hbound hlim
  have hz : Tendsto (fun z : ℂ => (F z-z)/z)
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hn
  have hh := hz.const_add 1
  simp only [add_zero] at hh
  apply hh.congr'
  change ∀ᶠ z in cocompact ℂ ⊓ 𝓟 upperHalfPlane, 1 + (F z-z)/z = F z/z
  rw [eventually_inf_principal]
  apply Eventually.of_forall
  intro z hzH
  have hz0 : z ≠ 0 := by
    intro he
    simp only [upperHalfPlane,mem_ofPred_eq,he,zero_im,lt_self_iff_false] at hzH
  field_simp [hz0]
  ring

lemma radiusHullInverse_normalized {R : ℝ} (hR : 0<R) :
    Tendsto (fun z : ℂ => radiusHullInverse R z/z)
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1) :=
  ratio_one_of_bounded_displacement (fun _ hz => radiusHullInverse_displacement hR hz)

end SLEExactGauge

end

end OAI
