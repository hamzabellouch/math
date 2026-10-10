import OAI.Geometry.CylinderCovering.Footprints.ConvergenceDefinitions
import OAI.Geometry.CylinderCovering.Footprints.Area
import OAI.Geometry.CylinderCovering.Radial.Riemann

namespace OAI

noncomputable section
namespace RadialFootprints
open Set MeasureTheory Filter
open scoped Topology
open CylinderCovering.RadialRiemann

theorem absoluteFootprint_area_sum_tendsto {a b : ℝ} (hab : a < b)
    {R W : ℝ → ℝ} (hR : ContinuousOn R (Icc a b)) (hW : ContinuousOn W (Icc a b))
    (hR0 : ∀ t ∈ Icc a b, 0 ≤ R t) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (tag shear : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged a b N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N,
      volume.real (absoluteFootprint A B (capMax R a b N i) (step a b N) (shear N i)) *
        W (tag N i)) atTop (𝓝 ((1/2 : ℝ) * ∫ t in a..b, R t^2 * W t)) := by
  have h := maxPolynomialSum_tendsto hab hR hW (1/2) (A+2*B) (A^2+4*A*B) tag htag
  convert h using 1
  funext N
  apply Finset.sum_congr rfl
  intro i _
  rw [absoluteFootprint_area (shear N i) hA hB (capMax_nonneg hab hR hR0 i)
    (step_pos hab (Nat.zero_lt_of_lt i.isLt)).le]
  ring

theorem affineFootprint_area_sum_tendsto {a b : ℝ} (hab : a < b)
    {R W : ℝ → ℝ} (hR : ContinuousOn R (Icc a b)) (hW : ContinuousOn W (Icc a b))
    (hR0 : ∀ t ∈ Icc a b, 0 ≤ R t) {A B : ℝ} (hA : 0 ≤ A) (hB : A/2 ≤ B)
    (tag shear : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged a b N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N,
      volume.real (affineFootprint A B (capMax R a b N i) (step a b N) (shear N i)) *
        W (tag N i)) atTop (𝓝 ((1/2 : ℝ) * ∫ t in a..b, R t^2 * W t)) := by
  have h := maxPolynomialSum_tendsto hab hR hW (1/2) (A+2*B) (4*A*B) tag htag
  convert h using 1
  funext N
  apply Finset.sum_congr rfl
  intro i _
  rw [affineFootprint_area (shear N i) hA hB (capMax_nonneg hab hR hR0 i)
    (step_pos hab (Nat.zero_lt_of_lt i.isLt)).le]
  ring

theorem halfheightFootprint_area_sum_tendsto {a b : ℝ} (hab : a < b)
    {R W : ℝ → ℝ} (hR : ContinuousOn R (Icc a b)) (hW : ContinuousOn W (Icc a b))
    (hR0 : ∀ t ∈ Icc a b, 0 ≤ R t) {E : ℝ} (hE : 0 ≤ E)
    (tag shear : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged a b N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N,
      volume.real (halfheightFootprint (step a b N / 2) (E * step a b N)
        (capMax R a b N i) (shear N i)) * W (tag N i))
      atTop (𝓝 ((1/2 : ℝ) * ∫ t in a..b, R t^2 * W t)) := by
  have h := maxPolynomialSum_tendsto hab hR hW (1/2) (3*E) (4*E^2) tag htag
  convert h using 1
  funext N
  apply Finset.sum_congr rfl
  intro i _
  have hd := (step_pos hab (Nat.zero_lt_of_lt i.isLt)).le
  rw [halfheightFootprint_area (shear N i) (div_nonneg hd (by norm_num))
    (mul_nonneg hE hd) (capMax_nonneg hab hR hR0 i)]
  ring

theorem footprint_area_limits : FootprintConvergenceStatement :=
  ⟨absoluteFootprint_area_sum_tendsto, affineFootprint_area_sum_tendsto,
    halfheightFootprint_area_sum_tendsto⟩

end RadialFootprints

end

end OAI
