import OAI.MeasureTheory.Falconer.Radial.AllDimensionalSmoothRadialEstimate
import OAI.MeasureTheory.Falconer.Fourier.EuclideanSmoothConvolution

namespace OAI

/-! A radial moment bound uniform in the mollification radius. -/

namespace Falconer
open Set MeasureTheory Metric PlanarFalconer
open scoped ENNReal

theorem euclideanMollification_support_bound {d : ℕ} (α : Measure (Space d))
    [IsFiniteMeasure α] {K : Set (Space d)} (hα : ∀ᵐ z ∂α, z ∈ K)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (x : Space d) {D : ℝ}
    (hD : ∀ z ∈ K, dist z x ≤ D) :
    ∀ y, euclideanSmoothDensity α (euclideanMollifier ε hε) y ≠ 0 → dist y x ≤ D+1 := by
  intro y hy
  by_contra h
  apply hy
  apply integral_eq_zero_of_ae
  filter_upwards [hα] with z hz
  by_contra hb
  have hm : y-z ∈ ball (0 : Space d) ε := by
    rw [← euclideanMollifier_support ε hε]
    exact hb
  have hd : dist y z < ε := by
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hm
  exact h ((dist_triangle y z x).trans ((add_le_add hd.le (hD z hz)).trans
    (by simpa only [add_comm] using add_le_add_right hε1 D)))

theorem mollified_euclidean_radial_moment_bound (n : ℕ)
    (α β : Measure (Space (n+1))) [IsFiniteMeasure α] [IsFiniteMeasure β]
    {K : Set (Space (n+1))} (hK : IsCompact K) (hα : ∀ᵐ z ∂α, z ∈ K)
    {s t p q D : ℝ} (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (hs2 : s < 2*n)
    (ht : 0 < t) (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (hupt : (2*n-s)*p < t) (htr : t/(2-p) < n) (hD : 0 < D)
    (hdiam : ∀ᵐ z : Space (n+1) × Space (n+1) ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      (∫⁻ x, ∫⁻ w : Sphere (n+1),
        (euclideanRadialDensity (fun y => ENNReal.ofReal
          (euclideanSmoothDensity α (euclideanMollifier ε hε) y)) x w)^p
          ∂sphereMeasure (n+1) ∂β) ≤
        C * (rieszEnergyOn β t)^(1/2 : ℝ) * (rieszEnergyOn α s)^(p/2) := by
  obtain ⟨C,hC,h⟩ := smooth_euclidean_radial_moment_bound n hs0 hs hsn hs2 ht hpq hp2
    hupt htr (show 0 < D+1 by linarith)
  refine ⟨C,hC,?_⟩
  intro ε hε hε1
  let b := euclideanMollifier (d := n+1) ε hε
  have hc := euclideanMollifier_compact (d := n+1) ε hε
  have hb := euclideanMollifier_smooth (d := n+1) ε hε
  have hn := euclideanMollifier_nonneg (d := n+1) ε hε
  have hh := h (euclideanSmoothDensity α b)
    (euclideanSmoothDensity_compact α b hc hK hα) (euclideanSmoothDensity_smooth α b hc hb)
    (euclideanSmoothDensity_nonneg α b hn) β
    (hdiam.mono (fun z hz => by linarith only [hz]))
    (hbound.mono (fun x hx => euclideanMollification_support_bound α hα ε hε hε1 x hx))
  have he : rieszEnergyOn (euclideanDensityMeasure (euclideanSmoothDensity α b)) s ≤
      rieszEnergyOn α s := by
    rw [← euclideanSmoothDensity_measure α b hc hb.continuous hn]
    exact euclideanMollifier_energy_le α ε hε hs0 (by exact_mod_cast hsn)
  exact hh.trans (mul_le_mul_right
    (ENNReal.rpow_le_rpow he (show 0 ≤ p/2 by linarith [hpq.pos])) _)

end Falconer

end OAI
