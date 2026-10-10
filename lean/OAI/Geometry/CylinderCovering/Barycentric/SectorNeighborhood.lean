import OAI.Geometry.CylinderCovering.Barycentric.SectorNeighborhoodDefinitions
import OAI.Geometry.CylinderCovering.Barycentric.Sector
import OAI.Geometry.CylinderCovering.Radial.Triangle

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace RadialCoordinates.BarycentricSector

private theorem nearby_sector_point_in_triangle
    {l r k M t ρ : ℝ} {z : Plane}
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) (hk : 0 ≤ k)
    (ht : t ∈ Icc l r) (hρ : ρ ∈ Icc (-(2*k*(r-l))) (M+2*k*(r-l)))
    (hz : dist z (ρ • ray t) ≤ Real.sqrt 2*k*(r-l)^2) :
    z ∈ neighborhoodTriangle l r k M := by
  let d := r-l
  let c := (l+r)/2
  let u := z 0+z 1
  have hd : 0 ≤ d := sub_nonneg.mpr hlr
  have hd1 : d ≤ 1 := by dsimp [d]; linarith
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hc1 : c ≤ 1 := by dsimp [c]; linarith
  have htC : |t-c| ≤ d/2 := by
    rw [abs_le]
    dsimp [c,d]
    constructor <;> linarith [ht.1, ht.2]
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    norm_num
  have hnorm : ‖z-ρ • ray t‖ ≤ 2*k*d^2 := by
    calc
      _ ≤ Real.sqrt 2*k*d^2 := by simpa only [dist_eq_norm, d] using hz
      _ ≤ 2*k*d^2 := by nlinarith [mul_le_mul_of_nonneg_right hsqrt (by positivity : 0 ≤ k*d^2)]
  have he0 : |z 0-ρ*t| ≤ 2*k*d^2 := by
    have h := (PiLp.norm_apply_le (z-ρ • ray t) 0).trans hnorm
    simpa [ray, Real.norm_eq_abs] using h
  have he1 : |z 1-ρ*(1-t)| ≤ 2*k*d^2 := by
    have h := (PiLp.norm_apply_le (z-ρ • ray t) 1).trans hnorm
    simpa [ray, Real.norm_eq_abs] using h
  have hu : |u-ρ| ≤ 4*k*d^2 := by
    calc
      _ = |(z 0-ρ*t)+(z 1-ρ*(1-t))| := by dsimp [u]; congr 1; ring
      _ ≤ |z 0-ρ*t|+|z 1-ρ*(1-t)| := abs_add_le _ _
      _ ≤ 4*k*d^2 := by linarith
  have hrad : |ρ| ≤ ρ+4*k*d := by
    rw [abs_le]
    constructor
    · dsimp [d] at *
      linarith [hρ.1]
    · have := mul_nonneg hk hd
      linarith
  have he : |(z 0-c*u)-(t-c)*ρ| ≤ 2*k*d^2 := by
    calc
      _ = |(1-c)*(z 0-ρ*t)-c*(z 1-ρ*(1-t))| := by dsimp [u]; congr 1; ring
      _ ≤ |(1-c)*(z 0-ρ*t)|+|c*(z 1-ρ*(1-t))| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le ((1-c)*(z 0-ρ*t)) (-(c*(z 1-ρ*(1-t))))
      _ = (1-c)*|z 0-ρ*t|+c*|z 1-ρ*(1-t)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hc1), abs_of_nonneg hc0]
      _ ≤ 2*k*d^2 := by
        nlinarith [mul_le_mul_of_nonneg_left he0 (sub_nonneg.mpr hc1),
          mul_le_mul_of_nonneg_left he1 hc0]
  have hwidth : |z 0-c*u| ≤ d/2*u+6*k*d^2 := by
    have hbase : |z 0-c*u| ≤ d/2*|ρ|+2*k*d^2 := by
      calc
        _ = |(t-c)*ρ+((z 0-c*u)-(t-c)*ρ)| := by congr 1; ring
        _ ≤ |(t-c)*ρ|+|(z 0-c*u)-(t-c)*ρ| := abs_add_le _ _
        _ ≤ d/2*|ρ|+2*k*d^2 := by
          rw [abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right htC (abs_nonneg ρ)) he
    have hrel : ρ ≤ u+4*k*d^2 := by linarith [(abs_le.mp hu).1]
    have hcubic : d^3 ≤ d^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hd1 (sq_nonneg d)]
    nlinarith [mul_le_mul_of_nonneg_left hrad (show 0 ≤ d/2 by positivity),
      mul_le_mul_of_nonneg_left hrel (show 0 ≤ d/2 by positivity),
      mul_le_mul_of_nonneg_left hcubic (show 0 ≤ 2*k by positivity)]
  have hkd : k*d^2 ≤ k*d := by
    have hsq : d^2 ≤ d := by nlinarith
    exact mul_le_mul_of_nonneg_left hsq hk
  refine ⟨(u, z 0), ?_, ?_⟩
  · change -(12*k*(r-l)) ≤ u ∧ u ≤ M+6*k*(r-l) ∧
      |z 0-(l+r)/2*u| ≤ (r-l)/2*(u-(-(12*k*(r-l))))
    change -(12*k*d) ≤ u ∧ u ≤ M+6*k*d ∧
      |z 0-c*u| ≤ d/2*(u-(-(12*k*d)))
    refine ⟨?_, ?_, ?_⟩
    · have hρlo : -(2*k*d) ≤ ρ := hρ.1
      have := mul_nonneg hk hd
      nlinarith [(abs_le.mp hu).1]
    · have hρhi : ρ ≤ M+2*k*d := hρ.2
      nlinarith [(abs_le.mp hu).2]
    · nlinarith only [hwidth]
  · ext i
    fin_cases i <;> simp [triangleChart, u]

theorem neighborhood_subset_triangle {l r k M : ℝ}
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) (hk : 0 ≤ k) (hM : 0 ≤ M) :
    neighborhood l r k M ⊆ neighborhoodTriangle l r k M := by
  have hcompact := isCompact_signedSector hlr
    (show 0 ≤ 2*k*(r-l) by positivity) (show 0 ≤ M+2*k*(r-l) by positivity)
  rw [neighborhood, hcompact.cthickening_eq_biUnion_closedBall (by positivity)]
  intro z hz
  obtain ⟨w, ⟨t, ht, ρ, hρ, rfl⟩, hz⟩ := mem_iUnion₂.mp hz
  exact nearby_sector_point_in_triangle hl hlr hr hk ht hρ hz

private def triangleCoordinateMap : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![0,1;1,-1]

private theorem triangleCoordinateMap_det : triangleCoordinateMap.det = -1 := by
  rw [triangleCoordinateMap, LinearMap.det_toLin, Matrix.det_fin_two]
  norm_num

theorem triangleChart_volume (S : Set (ℝ × ℝ)) :
    volume (triangleChart '' S) = volume S := by
  have hm : triangleChart = AngularCaps.pairToPlane ∘ triangleCoordinateMap := by
    funext p
    ext i
    fin_cases i <;>
      simp [triangleChart, triangleCoordinateMap, Matrix.toLin_finTwoProd_apply,
        AngularCaps.pairToPlane]
    ring
  have him : triangleChart '' S = AngularCaps.pairToPlane '' (triangleCoordinateMap '' S) := by
    rw [image_image]
    exact congrArg (fun f : (ℝ × ℝ) → Plane => f '' S) hm
  rw [him, AngularCaps.pairToPlane_volume,
    Measure.addHaar_image_linearMap, triangleCoordinateMap_det]
  norm_num

theorem neighborhoodTriangle_volume {l r k M : ℝ}
    (hlr : l ≤ r) (hk : 0 ≤ k) (hM : 0 ≤ M) :
    volume (neighborhoodTriangle l r k M) =
      ENNReal.ofReal ((r-l)*(M+18*k*(r-l))^2/2) := by
  have hd : 0 ≤ r-l := sub_nonneg.mpr hlr
  rw [neighborhoodTriangle, triangleChart_volume,
    CylinderCovering.RadialTriangle.region_volume (by nlinarith [mul_nonneg hk hd]) hd]
  congr 1
  ring

theorem neighborhoodTriangle_area {l r k M : ℝ}
    (hlr : l ≤ r) (hk : 0 ≤ k) (hM : 0 ≤ M) :
    volume.real (neighborhoodTriangle l r k M) = (r-l)*(M+18*k*(r-l))^2/2 := by
  rw [measureReal_def, neighborhoodTriangle_volume hlr hk hM, ENNReal.toReal_ofReal]
  positivity

theorem neighborhood_isCompact {l r k M : ℝ}
    (hlr : l ≤ r) (hk : 0 ≤ k) (hM : 0 ≤ M) :
    IsCompact (neighborhood l r k M) := by
  exact (isCompact_signedSector hlr (by positivity) (by positivity)).cthickening

theorem neighborhood_area_le {l r k M : ℝ}
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) (hk : 0 ≤ k) (hM : 0 ≤ M) :
    volume.real (neighborhood l r k M) ≤ (r-l)*(M+18*k*(r-l))^2/2 := by
  have hmono := measureReal_mono (μ := volume)
    (neighborhood_subset_triangle hl hlr hr hk hM)
    (by rw [neighborhoodTriangle_volume hlr hk hM]; exact ENNReal.ofReal_ne_top)
  rwa [neighborhoodTriangle_area hlr hk hM] at hmono

theorem neighborhood_area_error {l r k M M₀ : ℝ}
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) (hk : 0 ≤ k)
    (hM : 0 ≤ M) (hMM : M ≤ M₀) :
    0 ≤ volume.real (neighborhood l r k M)-(r-l)*M^2/2 ∧
    volume.real (neighborhood l r k M)-(r-l)*M^2/2 ≤
      (18*k*M₀+162*k^2)*(r-l)^2 := by
  have hd : 0 ≤ r-l := sub_nonneg.mpr hlr
  have hd1 : r-l ≤ 1 := by linarith
  constructor
  · have hmono := measureReal_mono (μ := volume)
      (Metric.self_subset_cthickening
        (signedSector l r (2*k*(r-l)) (M+2*k*(r-l))))
      (neighborhood_isCompact hlr hk hM).measure_ne_top
    change volume.real (signedSector l r (2*k*(r-l)) (M+2*k*(r-l))) ≤
      volume.real (neighborhood l r k M) at hmono
    rw [collar_sector_area hlr hk hM] at hmono
    have hz : 0 ≤ 2*k*M*(r-l)^2+4*k^2*(r-l)^3 := by positivity
    linarith
  · have hupper := neighborhood_area_le hl hlr hr hk hM
    have hcubic : (r-l)^3 ≤ (r-l)^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hd1 (sq_nonneg (r-l))]
    nlinarith [mul_le_mul_of_nonneg_left hMM (show 0 ≤ 18*k*(r-l)^2 by positivity),
      mul_le_mul_of_nonneg_left hcubic (show 0 ≤ 162*k^2 by positivity)]

theorem intercepted_area_bound {l r k M M₀ : ℝ} {S : Set Plane}
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) (hk : 0 ≤ k)
    (hM : 0 ≤ M) (hMM : M ≤ M₀) (hS : S ⊆ neighborhood l r k M) :
    volume.real S ≤ (r-l)*M^2/2+(18*k*M₀+162*k^2)*(r-l)^2 := by
  have hmono := measureReal_mono (μ := volume) hS
    (neighborhood_isCompact hlr hk hM).measure_ne_top
  have herror := (neighborhood_area_error hl hlr hr hk hM hMM).2
  linarith

end RadialCoordinates.BarycentricSector

end

end OAI
