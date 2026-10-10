import OAI.Analysis.CircleDomains.Sobolev.SmoothSphereCharts
import OAI.Analysis.CircleDomains.Modulus.ConformalNormalization

namespace OAI

/-!
# Principal normalization at infinity

A holomorphic germ fixing zero with nonzero derivative has a reciprocal
with one simple pole. Two divided differences isolate its pole and
constant terms and leave an analytic first-order remainder. This gives
the affine normalization used before taking limits of circle models.
-/

open Set Filter Function Asymptotics
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem analyticAt_dslope_zero {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) :
    AnalyticAt ℂ (dslope u 0) 0 := by
  obtain ⟨p, hp⟩ := hu
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem reciprocal_germ_normalization {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 = 0) (hdu : deriv u 0 ≠ 0) :
    ∃ (a b : ℂ) (R : ℂ → ℂ), a ≠ 0 ∧ AnalyticAt ℂ R 0 ∧
      ∀ z : ℂ, z ≠ 0 → a * (u z)⁻¹ + b = z⁻¹ + z * R z := by
  let v := dslope u 0
  have hv : AnalyticAt ℂ v 0 := analyticAt_dslope_zero hu
  have hv0 : v 0 ≠ 0 := by simpa only [v, dslope_same] using hdu
  let q : ℂ → ℂ := fun z => (v z)⁻¹
  have hq : AnalyticAt ℂ q 0 := hv.inv hv0
  let r := dslope q 0
  let t := dslope r 0
  have ht : AnalyticAt ℂ t 0 := analyticAt_dslope_zero (analyticAt_dslope_zero hq)
  have hu_eq (z : ℂ) : u z = z * v z := by
    simpa only [sub_zero, smul_eq_mul, hu0] using (sub_smul_dslope u 0 z).symm
  have hq_eq (z : ℂ) : q z = q 0 + z * r 0 + z ^ 2 * t z := by
    have h1 : z * r z = q z - q 0 := by
      simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope q 0 z
    have h2 : z * t z = r z - r 0 := by
      simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope r 0 z
    calc
      q z = q 0 + z * r z := by linear_combination -h1
      _ = q 0 + z * r 0 + z ^ 2 * t z := by linear_combination -z * h2
  refine ⟨v 0, -(v 0 * r 0), fun z => v 0 * t z, hv0, analyticAt_const.mul ht, ?_⟩
  intro z hz
  calc
    v 0 * (u z)⁻¹ + -(v 0 * r 0) = v 0 * z⁻¹ * q z - v 0 * r 0 := by
      rw [hu_eq, mul_inv_rev]
      dsimp only [q]
      ring
    _ = z⁻¹ + z * (v 0 * t z) := by
      rw [hq_eq]
      dsimp only [q]
      field_simp
      ring

theorem finiteCoord_sphereInv (p : Sphere) : finiteCoord (sphereInv p) = (finiteCoord p)⁻¹ := by
  cases p using OnePoint.rec with
  | infty => simp [finiteCoord]
  | coe z => simpa only [finiteCoord_coe] using finiteCoord_sphereInv_coe z

theorem analyticAt_infty_chart
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hf : IsConformalOn f U)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty) :
    AnalyticAt ℂ (sphereLocalMap f OnePoint.infty) 0 := by
  let F : Sphere → Sphere := CannonMobius.inversion ∘ f ∘ CannonMobius.inversion
  let V : Set Sphere := CannonMobius.inversion ⁻¹' U
  have hV : IsOpen V := hU.preimage CannonMobius.inversion.continuous
  have hF : IsConformalOn F V := by
    intro p hp
    exact (isConformalAt_inversion _).comp ((hf _ hp).comp (isConformalAt_inversion p))
  have hzero : ((0 : ℂ) : Sphere) ∈ V := by
    change CannonMobius.inv ((0 : ℂ) : Sphere) ∈ U
    simpa only [CannonMobius.inv_zero] using hinf
  have hFzero : F ((0 : ℂ) : Sphere) = ((0 : ℂ) : Sphere) := by
    change CannonMobius.inv (f (CannonMobius.inv ((0 : ℂ) : Sphere))) = _
    rw [CannonMobius.inv_zero, hfix, CannonMobius.inv_infty]
  have ha := analyticAt_finite_map_of_conformal hV hF hzero
    (by rw [hFzero]; exact OnePoint.coe_ne_infty (0 : ℂ))
  change AnalyticAt ℂ (fun z : ℂ => finiteCoord (sphereInv (f (sphereInv (z : Sphere))))) 0 at ha
  have heq : sphereLocalMap f OnePoint.infty =
      (fun z : ℂ => finiteCoord (sphereInv (f (sphereInv (z : Sphere))))) := by
    funext z
    change chart (f OnePoint.infty) (f (chartSymm OnePoint.infty z)) = _
    rw [hfix, chart_infty_apply, chartSymm, ite_eq_left rfl]
  rw [heq]
  exact ha

theorem affine_normalization_expansion
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hf : IsConformalOn f U)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (a b : ℂ) (R : ℂ → ℂ), a ≠ 0 ∧ AnalyticAt ℂ R 0 ∧
      ∀ z : ℂ, z ≠ 0 → a * finiteCoord (f (z : Sphere)) + b = z + z⁻¹ * R z⁻¹ := by
  have ha := analyticAt_infty_chart hU hf hinf hfix
  have hzero : sphereLocalMap f OnePoint.infty 0 = 0 := by
    simp only [sphereLocalMap, chartSymm, ite_true, sphereInv_zero, hfix, chart_infty_self]
  obtain ⟨_, d, hd, hder⟩ := hf _ hinf
  have hder' : HasDerivAt (sphereLocalMap f OnePoint.infty) d 0 := by
    change HasDerivAt (sphereLocalMap f OnePoint.infty) d
      (chart OnePoint.infty OnePoint.infty) at hder
    rw [chart_infty_self] at hder
    exact hder
  have hdu : deriv (sphereLocalMap f OnePoint.infty) 0 ≠ 0 := hder'.deriv.symm ▸ hd
  obtain ⟨a, b, R, hane, hR, hexp⟩ := reciprocal_germ_normalization ha hzero hdu
  refine ⟨a, b, R, hane, hR, ?_⟩
  intro z hz
  have h := hexp z⁻¹ (inv_ne_zero hz)
  have hchart : (sphereLocalMap f OnePoint.infty z⁻¹)⁻¹ = finiteCoord (f (z : Sphere)) := by
    simp only [sphereLocalMap, hfix, chart_infty_apply, chartSymm, ite_true]
    have hinv : sphereInv ((z⁻¹ : ℂ) : Sphere) = (z : Sphere) := by
      simp [sphereInv, inv_ne_zero hz]
    rw [hinv, finiteCoord_sphereInv, inv_inv]
  simpa only [hchart, inv_inv] using h

end CircleDomainRigidity

end

end OAI
