import OAI.Probability.SLE.Geometry.HolomorphicRadialFlux

namespace OAI

/-! Inversion of circle averages and the elementary signed-area identity
for a map with leading term z and a holomorphic inverse-radius remainder. -/
noncomputable section
open Set Filter Metric Function Complex MeasureTheory InnerProductSpace Real
open scoped Topology Laplacian ComplexConjugate

namespace SLEExactGauge

lemma circleAverage_inv_radius {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (r : ℝ) :
    circleAverage (fun z => f z⁻¹) 0 r=circleAverage f 0 r⁻¹ := by
  calc
    _ = circleAverage (fun z : ℂ => f (((r:ℂ)*z+0)⁻¹)) 0 1 :=
      circleAverage_eq_circleAverage_zero_one
    _ = circleAverage (fun z : ℂ => f (((r⁻¹:ℝ):ℂ)*z⁻¹)) 0 1 := by
      congr 1
      ext z
      simp only [add_zero,mul_inv_rev,Complex.ofReal_inv,mul_comm]
    _ = circleAverage (fun z : ℂ => f (((r⁻¹:ℝ):ℂ)*z)) 0 1 := by
      exact circleAverage_zero_one_congr_inv (f := fun z : ℂ => f (((r⁻¹:ℝ):ℂ)*z))
    _ = _ := by
      simpa only [add_zero] using
        (circleAverage_eq_circleAverage_zero_one (f := f) (c := (0:ℂ)) (R := r⁻¹)).symm

lemma inverse_area_density_identity (z c cp : ℂ) (hz : z≠0) :
    2*((z-z⁻¹*cp)*conj (z+c)).re=
      2*‖z‖^2+2*‖z‖^2*(z⁻¹*c-z⁻¹^2*cp).re-
        2*(z⁻¹*cp*conj c).re := by
  have hh : (z-z⁻¹*cp)*conj (z+c)=
      ((‖z‖^2:ℝ):ℂ)+((‖z‖^2:ℝ):ℂ)*(conj (z⁻¹*c)-z⁻¹^2*cp)-z⁻¹*cp*conj c := by
    have hnorm : ((‖z‖^2:ℝ):ℂ)=z*conj z := by
      simpa only [Complex.ofReal_pow] using (Complex.mul_conj' z).symm
    rw [hnorm]
    simp only [map_add,map_mul,map_inv₀]
    field_simp [hz]
    ring
  rw [hh]
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.conj_re]
  ring

end SLEExactGauge

end

end OAI
