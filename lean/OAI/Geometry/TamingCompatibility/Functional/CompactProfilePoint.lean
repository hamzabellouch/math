import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.PhysicalProfile
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationKernel

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume Set
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
lemma compact_chart_profile_bound_points (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ L : ℝ, 0 < L ∧ ∀ x y : X,
      x ∈ (extChartAt Model p).source → y ∈ (extChartAt Model p).source →
      extChartAt Model p x ∈ K → extChartAt Model p y ∈ K → ∀ r : ℝ, 0 < r →
      ((1+‖extChartAt Model p x-extChartAt Model p y‖/r)⁻¹)^6 ≤
        physicalProfile J α hs ht (L*r) x y := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨L₀,hL₀⟩ := chartInverse_compact_lipschitz J α hs ht p K hK hKT
  let L : ℝ := (L₀:ℝ)+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L,hL,fun x y hx hy hxK hyK r hr => ?_⟩
  have hphys := hL₀.dist_le_mul _ hxK _ hyK
  change dist ((extChartAt Model p).symm (extChartAt Model p x))
    ((extChartAt Model p).symm (extChartAt Model p y)) ≤ _ at hphys
  rw [(extChartAt Model p).left_inv hx,(extChartAt Model p).left_inv hy,dist_eq_norm] at hphys
  have htransport : dist x y ≤ L*‖extChartAt Model p x-extChartAt Model p y‖ :=
    hphys.trans (mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) (norm_nonneg _))
  have hdiv : dist x y/(L*r) ≤ ‖extChartAt Model p x-extChartAt Model p y‖/r := by
    apply (div_le_iff₀ (mul_pos hL hr)).mpr
    calc
      _ ≤ L*‖extChartAt Model p x-extChartAt Model p y‖ := htransport
      _ = _ := by field_simp
  change _ ≤ ((1+dist x y/(L*r))⁻¹)^6
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) (by linarith)) 6
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.Concentration
lemma sum_six_le (r t : ℝ) : (r+t)^6 ≤ 8*(r^2+t^2)^3 := by
  have h₁ : (r+t)^2 ≤ 2*(r^2+t^2) := by nlinarith [sq_nonneg (r-t)]
  have hh := pow_le_pow_left₀ (sq_nonneg (r+t)) h₁ 3
  calc
    (r+t)^6 = ((r+t)^2)^3 := by ring
    _ ≤ (2*(r^2+t^2))^3 := hh
    _ = _ := by ring

lemma radialCoefficient_profile {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    radialCoefficient r t ≤ (8/r^4)*((1+t/r)⁻¹)^6 := by
  have hs : 0 < r^2+t^2 := by positivity
  have hrt : 0 < r+t := by positivity
  have he : ((1+t/r)⁻¹)^6 = r^6/(r+t)^6 := by
    field_simp
  rw [he,radialCoefficient]
  have he' : (8/r^4)*(r^6/(r+t)^6) = 8*r^2/(r+t)^6 := by field_simp
  rw [he']
  apply (div_le_div_iff₀ (pow_pos hs 4) (pow_pos hrt 6)).mpr
  have hsmall : r^2 ≤ r^2+t^2 := by nlinarith [sq_nonneg t]
  have hmult := mul_le_mul_of_nonneg_left (sum_six_le r t) (by positivity : 0 ≤ r^2)
  have hbig := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 8*(r^2+t^2)^3)
  have h := mul_le_mul_of_nonneg_left (hmult.trans hbig) (by positivity : 0 ≤ r^2)
  nlinarith

lemma radialCoefficient_linear_profile {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    radialCoefficient r t*t ≤ (8/r^3)*((1+t/r)⁻¹)^6 := by
  have hs : 0 < r^2+t^2 := by positivity
  have hrt : 0 < r+t := by positivity
  have he : ((1+t/r)⁻¹)^6 = r^6/(r+t)^6 := by
    field_simp
  rw [he,radialCoefficient]
  have he' : (8/r^3)*(r^6/(r+t)^6) = 8*r^3/(r+t)^6 := by field_simp
  rw [he',div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (pow_pos hs 4) (pow_pos hrt 6)).mpr
  have hsmall : r*t ≤ r^2+t^2 := by nlinarith [sq_nonneg (r-t)]
  have hmult := mul_le_mul_of_nonneg_left (sum_six_le r t) (by positivity : 0 ≤ r*t)
  have hbig := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 8*(r^2+t^2)^3)
  have h := mul_le_mul_of_nonneg_left (hmult.trans hbig) (by positivity : 0 ≤ r^3)
  nlinarith
lemma radialCoefficient_quadratic_profile {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    radialCoefficient r t*t^2 ≤ (8/r^2)*((1+t/r)⁻¹)^6 := by
  have hs : 0 < r^2+t^2 := by positivity
  have hrt : 0 < r+t := by positivity
  have he : ((1+t/r)⁻¹)^6 = r^6/(r+t)^6 := by field_simp
  rw [he,radialCoefficient]
  have he' : (8/r^2)*(r^6/(r+t)^6) = 8*r^4/(r+t)^6 := by field_simp
  rw [he',div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (pow_pos hs 4) (pow_pos hrt 6)).mpr
  have hsmall : t^2 ≤ r^2+t^2 := by nlinarith [sq_nonneg r]
  have hmult := mul_le_mul_of_nonneg_left (sum_six_le r t) (by positivity : 0 ≤ t^2)
  have hbig := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 8*(r^2+t^2)^3)
  have h := mul_le_mul_of_nonneg_left (hmult.trans hbig) (by positivity : 0 ≤ r^4)
  nlinarith
end TamingCompatibility.Concentration

end
end

end OAI
