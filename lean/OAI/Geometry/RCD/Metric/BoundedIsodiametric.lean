import OAI.Geometry.RCD.Metric.LocalToGlobalIsodiametric
import OAI.Geometry.RCD.Sobolev.EuclideanEnergyRatios

namespace OAI

/-! # The sharp diameter bound for arbitrary bounded Euclidean sets -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem bounded_isodiametric_of_compact {n : ℕ}
    (hcompact : ∀ A : Set (Euclidean n), IsCompact A →
      volume.real A ≤ volume.real (closedBall (0 : Euclidean n) (diam A/2)))
    {A : Set (Euclidean n)} (hA : Bornology.IsBounded A) :
    volume.real A ≤ volume.real (closedBall (0 : Euclidean n) (diam A/2)) := by
  have hcl : IsCompact (closure A) := isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure,hA.closure⟩
  have hh := hcompact (closure A) hcl
  rw [diam_closure] at hh
  exact (measureReal_mono subset_closure hcl.measure_lt_top.ne).trans hh

theorem bounded_volume_le_diameter_pow {n : ℕ} (hn : 0 < n)
    (hcompact : ∀ A : Set (Euclidean n), IsCompact A →
      volume.real A ≤ volume.real (closedBall (0 : Euclidean n) (diam A/2)))
    {A : Set (Euclidean n)} (hA : Bornology.IsBounded A) :
    volume.real A ≤ (volume.real (ball (0 : Euclidean n) 1)/2^n)*(diam A)^n := by
  have hh := bounded_isodiametric_of_compact hcompact hA
  rw [euclidean_closedBall_real hn 0 (by positivity)] at hh
  calc
    volume.real A ≤ (diam A/2)^n*volume.real (ball (0 : Euclidean n) 1) := hh
    _ = _ := by rw [div_pow]; ring

theorem bounded_volume_le_ediam_pow {n : ℕ} (hn : 0 < n)
    (hcompact : ∀ A : Set (Euclidean n), IsCompact A →
      volume.real A ≤ volume.real (closedBall (0 : Euclidean n) (diam A/2)))
    {A : Set (Euclidean n)} (hA : Bornology.IsBounded A) :
    volume A ≤ (volume (ball (0 : Euclidean n) 1)/2^n)*(ediam A)^n := by
  apply (ENNReal.toReal_le_toReal hA.measure_lt_top.ne ?_).mp
  · simpa only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,
      ENNReal.toReal_ofNat,Measure.real,Metric.diam] using
      bounded_volume_le_diameter_pow hn hcompact hA
  · exact ENNReal.mul_ne_top
      (ENNReal.div_ne_top measure_ball_ne_top (by positivity))
      (ENNReal.pow_ne_top hA.ediam_ne_top)

end RegularPointCoordinates

end

end OAI
