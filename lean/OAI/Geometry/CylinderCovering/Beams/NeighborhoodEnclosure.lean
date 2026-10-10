import OAI.Geometry.CylinderCovering.Radial.TriangleDefinitions
import OAI.Geometry.CylinderCovering.Beams.Neighborhood
import OAI.Geometry.TriangularCovering.Main

namespace OAI

open Set
noncomputable section
namespace CylinderCovering.BeamNeighborhood

lemma noisy_sector_bounds {N l r δ p d x y : ℝ}
    (hl : 0 ≤ l) (hr : r ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hlen : r-l = δ)
    (hp : p ∈ Icc l r) (hd : d ∈ Icc (-δ) (N+δ))
    (hx : |x| ≤ δ^2) (hy : |y| ≤ δ^2) :
    -δ-2*δ^2 ≤ d+x+y ∧ d+x+y ≤ N+δ+2*δ^2 ∧
    |d*p+x-((l+r)/2)*(d+x+y)| ≤ δ/2*(d+x+y)+5*δ^2 := by
  have hm0 : 0 ≤ (l+r)/2 := by linarith [hp.1,hp.2]
  have hm1 : (l+r)/2 ≤ 1 := by linarith [hp.1,hp.2]
  have hmabs : |(l+r)/2| ≤ 1 := by rwa [abs_of_nonneg hm0]
  have hpabs : |p-(l+r)/2| ≤ δ/2 :=
    abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hdabs : |d| ≤ d+2*δ := by
    apply abs_le.mpr
    constructor <;> linarith [hd.1]
  have hnoise : |x-((l+r)/2)*(x+y)| ≤ 3*δ^2 := by
    have hsum : |x+y| ≤ 2*δ^2 := (abs_add_le x y).trans (by linarith)
    have hm := mul_le_mul hmabs hsum (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have htri := abs_sub x (((l+r)/2)*(x+y))
    rw [abs_mul] at htri
    linarith
  have hsector := mul_le_mul hdabs hpabs (abs_nonneg _) (by linarith [hd.1] : 0 ≤ d+2*δ)
  have htriangle := abs_add_le (d*(p-(l+r)/2)) (x-((l+r)/2)*(x+y))
  rw [abs_mul] at htriangle
  have hid : d*(p-(l+r)/2)+(x-((l+r)/2)*(x+y)) =
      d*p+x-((l+r)/2)*(d+x+y) := by ring
  rw [hid] at htriangle
  have hδ3 : δ^3 ≤ δ^2 := by
    have := mul_le_mul_of_nonneg_right hδ1 (sq_nonneg δ)
    nlinarith only [this]
  have hxlo := (abs_le.mp hx).1
  have hylo := (abs_le.mp hy).1
  have hsumlo := mul_le_mul_of_nonneg_left (show -2*δ^2 ≤ x+y by linarith) hδ
  refine ⟨by linarith [hd.1], by linarith [hd.2,(abs_le.mp hx).2,(abs_le.mp hy).2],?_⟩
  nlinarith only [htriangle,hnoise,hsector,hsumlo,hδ3]

lemma mem_enclosingTriangle_of_coordinates {a l r δ : ℝ} {z : Plane}
    (hδ : 0 < δ) (hlen : r-l = δ) (hR : 0 < enclosingRadius a δ)
    (ht0 : 0 ≤ z 0+z 1+10*δ)
    (htR : z 0+z 1+10*δ ≤ enclosingRadius a δ)
    (he : |z 0-((l+r)/2)*(z 0+z 1)| ≤ δ/2*(z 0+z 1)+5*δ^2) :
    z ∈ enclosingTriangle a l r δ := by
  have hlo : l*(z 0+z 1+10*δ) ≤ z 0+10*δ*((l+r)/2) := by
    rw [← hlen] at he ⊢
    nlinarith only [(abs_le.mp he).1]
  have hhi : z 0+10*δ*((l+r)/2) ≤ r*(z 0+z 1+10*δ) := by
    rw [← hlen] at he ⊢
    nlinarith only [(abs_le.mp he).2]
  obtain ⟨u,v,hu,hv,huv,ht,hx⟩ := TriangularCovering.sector_weights
    (show l < r by linarith) hR ht0 htR hlo hhi
  change z ∈ TriangularCovering.triangle (enclosingApex l r δ)
    (enclosingApex l r δ+enclosingRadius a δ • radial l)
    (enclosingApex l r δ+enclosingRadius a δ • radial r)
  rw [TriangularCovering.mem_triangle_iff]
  refine ⟨u,v,hu,hv,huv,?_⟩
  simp only [add_sub_cancel_left]
  ext i
  fin_cases i <;> simp [enclosingApex,radial]
  · nlinarith only [hx]
  · nlinarith only [ht,hx]

theorem paddedSector_subset_enclosingTriangle {a l r δ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/2) (hl : 0 ≤ l) (hr : r ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlen : r-l = δ) :
    paddedSector a l r δ ⊆ enclosingTriangle a l r δ := by
  intro z hz
  change z ∈ Metric.cthickening (δ^2) (sector a l r δ) at hz
  rw [(sector_isCompact a l r δ).cthickening_eq_biUnion_closedBall (sq_nonneg δ)] at hz
  simp only [mem_iUnion, Metric.mem_closedBall] at hz
  obtain ⟨q, ⟨p,hp,d,hd,rfl⟩, hdist⟩ := hz
  rw [dist_eq_norm] at hdist
  let x := z 0-d*p
  let y := z 1-d*(1-p)
  have hx : |x| ≤ δ^2 := by
    have h := (PiLp.norm_apply_le (z-d • radial p) 0).trans hdist
    simpa [x,radial,Real.norm_eq_abs] using h
  have hy : |y| ≤ δ^2 := by
    have h := (PiLp.norm_apply_le (z-d • radial p) 1).trans hdist
    simpa [y,radial,Real.norm_eq_abs] using h
  have hb := noisy_sector_bounds hl hr hδ.le hδ1 hlen hp hd hx hy
  have hsum : d+x+y = z 0+z 1 := by dsimp [x,y]; ring
  have hfirst : d*p+x = z 0 := by dsimp [x]; ring
  rw [hsum,hfirst] at hb
  have hδ2 : δ^2 ≤ δ := by nlinarith
  have haabs : |a| ≤ 1/2 := by simpa only [abs_of_nonneg ha] using ha1
  apply mem_enclosingTriangle_of_coordinates hδ hlen
  · dsimp [enclosingRadius]
    nlinarith only [le_abs_self a, haabs, hδ, sq_nonneg δ]
  · nlinarith only [hb.1,hδ2,hδ]
  · dsimp [enclosingRadius]
    linarith only [hb.2.1]
  · exact hb.2.2

theorem paddedSector_mem_radialRegion {a l r δ : ℝ} {z : Plane}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/2) (hl : 0 ≤ l) (hr : r ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlen : r-l = δ)
    (hz : z ∈ paddedSector a l r δ) :
    (z 0+z 1,z 0) ∈ RadialTriangle.region (-10*δ) (2-a+δ+2*δ^2) ((l+r)/2) δ := by
  have htriangle := paddedSector_subset_enclosingTriangle ha ha1 hl hr hδ hδ1 hlen hz
  change z ∈ TriangularCovering.triangle (enclosingApex l r δ)
    (enclosingApex l r δ+enclosingRadius a δ • radial l)
    (enclosingApex l r δ+enclosingRadius a δ • radial r) at htriangle
  obtain ⟨u, v, hu, hv, huv, hpoint⟩ :=
    (TriangularCovering.mem_triangle_iff _ _ _ _).mp htriangle
  have hR : 0 ≤ enclosingRadius a δ := by
    dsimp [enclosingRadius]
    nlinarith only [ha1, hδ, sq_nonneg δ]
  have hsum : z 0+z 1 = -10*δ+(u+v)*enclosingRadius a δ := by
    rw [hpoint]
    simp [enclosingApex, radial]
    ring
  have hfirst : z 0 = -10*δ*((l+r)/2)+(u*l+v*r)*enclosingRadius a δ := by
    rw [hpoint]
    simp [enclosingApex, radial]
    ring
  change -10*δ ≤ z 0+z 1 ∧ z 0+z 1 ≤ 2-a+δ+2*δ^2 ∧ _
  rw [hsum, hfirst]
  refine ⟨by linarith only [mul_nonneg (add_nonneg hu hv) hR], ?_, ?_⟩
  · have hupper := mul_le_mul_of_nonneg_right huv hR
    dsimp [enclosingRadius] at hupper ⊢
    linarith only [hupper]
  · apply abs_le.mpr
    rw [show r = l+δ by linarith only [hlen]]
    constructor
    · nlinarith only [mul_nonneg hv (mul_nonneg hδ.le hR)]
    · nlinarith only [mul_nonneg hu (mul_nonneg hδ.le hR)]

end CylinderCovering.BeamNeighborhood

end

end OAI
