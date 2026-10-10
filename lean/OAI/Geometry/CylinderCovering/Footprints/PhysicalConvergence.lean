import OAI.Geometry.CylinderCovering.Footprints.PhysicalConvergenceDefinitions
import OAI.Geometry.CylinderCovering.Footprints.Projection
import OAI.Geometry.CylinderCovering.Footprints.Convergence

namespace OAI

noncomputable section
namespace RadialFootprints
open Set MeasureTheory Filter TriangularCovering
open scoped Topology InnerProductSpace
open CylinderCovering.RadialRiemann

private theorem physical_sum_tendsto {α β : ℝ} {e : Space} (he : ‖e‖ = 1)
    (p₀ a b : Space) (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (R : ℝ → ℝ) (w : ℝ → Space)
    (hw : ∀ t ∈ Icc α β, inner ℝ e (w t) = 0)
    (S : (N : ℕ) → Fin N → Set (ℝ × ℝ)) (tag : (N : ℕ) → Fin N → ℝ)
    (htag : ∀ N i, tag N i ∈ Icc α β)
    (hsum : Tendsto (fun N => ∑ i : Fin N,
      volume.real (S N i) * (1 / Real.sqrt (1 + ‖w (tag N i)‖^2))) atTop
      (𝓝 ((1/2 : ℝ) * ∫ t in α..β, R t^2 * (1 / Real.sqrt (1 + ‖w t‖^2))))) :
    Tendsto (fun N => ∑ i : Fin N,
      area (projectedCoordinateFootprint e (w (tag N i)) p₀ a b (S N i))) atTop
      (𝓝 (Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b)^2) *
        ∫ t in α..β, R t^2 / (2 * Real.sqrt (1 + ‖w t‖^2)))) := by
  have h := hsum.const_mul (Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b)^2))
  convert h using 1
  · funext N
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [projectedCoordinateFootprint_area p₀ a b (S N i) he ha hb (hw _ (htag N i))]
    ring
  · have hi : (∫ t in α..β, R t^2 / (2 * Real.sqrt (1 + ‖w t‖^2))) =
        (1/2 : ℝ) * ∫ t in α..β, R t^2 * (1 / Real.sqrt (1 + ‖w t‖^2)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp
      ring
    rw [hi]

theorem absoluteFootprint_physical_sum_tendsto {α β : ℝ} (hαβ : α < β)
    {e : Space} (he : ‖e‖ = 1) (p₀ a b : Space)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    {R : ℝ → ℝ} {w : ℝ → Space} (hR : ContinuousOn R (Icc α β))
    (hR0 : ∀ t ∈ Icc α β, 0 ≤ R t) (hw : ContinuousOn w (Icc α β))
    (hwperp : ∀ t ∈ Icc α β, inner ℝ e (w t) = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (tag shear : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged α β N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N,
      area (projectedCoordinateFootprint e (w (tag N i)) p₀ a b
        (absoluteFootprint A B (capMax R α β N i) (step α β N) (shear N i)))) atTop
      (𝓝 (Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b)^2) *
        ∫ t in α..β, R t^2 / (2 * Real.sqrt (1 + ‖w t‖^2)))) := by
  apply physical_sum_tendsto he p₀ a b ha hb R w hwperp _ tag
    (fun N i => cell_subset hαβ i (htag N i))
  exact absoluteFootprint_area_sum_tendsto hαβ hR (projection_weight_continuousOn hw)
    hR0 hA hB tag shear htag

theorem affineFootprint_physical_sum_tendsto {α β : ℝ} (hαβ : α < β)
    {e : Space} (he : ‖e‖ = 1) (p₀ a b : Space)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    {R : ℝ → ℝ} {w : ℝ → Space} (hR : ContinuousOn R (Icc α β))
    (hR0 : ∀ t ∈ Icc α β, 0 ≤ R t) (hw : ContinuousOn w (Icc α β))
    (hwperp : ∀ t ∈ Icc α β, inner ℝ e (w t) = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : A/2 ≤ B)
    (tag shear : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged α β N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N,
      area (projectedCoordinateFootprint e (w (tag N i)) p₀ a b
        (affineFootprint A B (capMax R α β N i) (step α β N) (shear N i)))) atTop
      (𝓝 (Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b)^2) *
        ∫ t in α..β, R t^2 / (2 * Real.sqrt (1 + ‖w t‖^2)))) := by
  apply physical_sum_tendsto he p₀ a b ha hb R w hwperp _ tag
    (fun N i => cell_subset hαβ i (htag N i))
  exact affineFootprint_area_sum_tendsto hαβ hR (projection_weight_continuousOn hw)
    hR0 hA hB tag shear htag

theorem halfheightFootprint_physical_sum_tendsto {α β : ℝ} (hαβ : α < β)
    {e : Space} (he : ‖e‖ = 1) (p₀ a b : Space)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    {R : ℝ → ℝ} {w : ℝ → Space} (hR : ContinuousOn R (Icc α β))
    (hR0 : ∀ t ∈ Icc α β, 0 ≤ R t) (hw : ContinuousOn w (Icc α β))
    (hwperp : ∀ t ∈ Icc α β, inner ℝ e (w t) = 0)
    {E : ℝ} (hE : 0 ≤ E)
    (tag shear : (N : ℕ) → Fin N → ℝ) (htag : ∀ N, IsTagged α β N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N,
      area (projectedCoordinateFootprint e (w (tag N i)) p₀ a b
        (halfheightFootprint (step α β N / 2) (E * step α β N)
          (capMax R α β N i) (shear N i)))) atTop
      (𝓝 (Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b)^2) *
        ∫ t in α..β, R t^2 / (2 * Real.sqrt (1 + ‖w t‖^2)))) := by
  apply physical_sum_tendsto he p₀ a b ha hb R w hwperp _ tag
    (fun N i => cell_subset hαβ i (htag N i))
  exact halfheightFootprint_area_sum_tendsto hαβ hR (projection_weight_continuousOn hw)
    hR0 hE tag shear htag

theorem physical_footprint_area_limits : PhysicalFootprintConvergenceStatement :=
  ⟨absoluteFootprint_physical_sum_tendsto, affineFootprint_physical_sum_tendsto,
    halfheightFootprint_physical_sum_tendsto⟩

end RadialFootprints

end

end OAI
