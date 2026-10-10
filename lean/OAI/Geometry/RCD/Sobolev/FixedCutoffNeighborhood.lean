import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.RegularDyadicData
import OAI.Geometry.RCD.Coordinates.UniformPolarizedError

namespace OAI

/-! # A single cutoff and time threshold for all nearby heat poles -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- The same actual cutoff works at every center in a smaller ball. Its
annular error has one dyadic starting index for all those centers. -/
theorem exists_fixed_cutoff_neighborhood {n : ℕ} {K R omega C : ℝ} {p : X}
    {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
    {M : PositiveBilinearMeasure X (Euclidean n)} {L : ℝ≥0}
    (G : ∀ v, LocalHarmonicEnergy μ hQ U M |K| p (4 * R) L v)
    (hg : HasCoordinateHeatBounds μ ker) (hR : 0 < R) (homega : 0 < omega)
    (hcurv : |K| * (16 * R) ^ 2 ≤ 1)
    (hvolume : ∀ y, dist p y ≤ 16 * R → ∀ s, 0 < s → s ≤ 32 * R →
      |μ.real (ball y s) / (omega * s ^ n) - 1| ≤ 1 / 2)
    (hcut : ∀ s, 0 < s → -1 ≤ K * s ^ 2 →
      Nonempty (GoodLaplacianCutoff μ hQ p s C)) :
    ∃ χ : GoodLaplacianCutoff μ hQ p (3 * R / 8) C, ∃ J : ℕ,
      ∀ q ∈ ball p (R / 32),
        (∀ x ∈ ball q (R / 4), (χ.weight : X → ℝ) x = 1) ∧
        (∀ x ∉ ball q R, (χ.weight : X → ℝ) x = 0) ∧
        ∀ i, J ≤ i → ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
          ‖harmonicHeatError μ hQ (k := ker) G χ t q‖ ≤ 1 := by
  have hρ : 0 < 3 * R / 8 := by positivity
  have hK : -1 ≤ K * (3 * R / 8) ^ 2 := by
    have hn := neg_abs_le K
    have hs : (3 * R / 8) ^ 2 ≤ (16 * R) ^ 2 := by nlinarith [sq_pos_of_pos hR]
    have h := mul_le_mul_of_nonneg_left hs (abs_nonneg K)
    have hk := mul_le_mul_of_nonneg_right hn (sq_nonneg (3 * R / 8))
    nlinarith
  obtain ⟨χ⟩ := hcut _ hρ hK
  have hv : ∀ y, 3 * R / 8 ≤ dist p y → dist p y ≤ 2 * (3 * R / 8) →
      ∀ s, 0 < s → s ≤ R → (omega / 2) * s ^ n ≤ μ.real (ball y s) := by
    intro y _ hy s hs hsR
    have hb := (abs_le.mp (hvolume y (by linarith) s hs (by linarith))).1
    have hd : 0 < omega * s ^ n := mul_pos homega (pow_pos hs n)
    have hh : (1 / 2 : ℝ) ≤ μ.real (ball y s) / (omega * s ^ n) := by linarith
    have hm := (le_div_iff₀ hd).mp hh
    nlinarith only [hm]
  obtain ⟨δ, hδ, he⟩ := harmonicHeatError_uniformly_small μ hQ hk hg G χ hρ hR
    (show 0 < omega / 2 by positivity) hv (by norm_num : (0 : ℝ) < 1)
  obtain ⟨J, hJ⟩ := eventual_dyadic_time_blocks hR hδ
  refine ⟨χ, J, ?_⟩
  intro q hq
  have hqp : dist q p < R / 32 := hq
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    apply χ.one
    have hxq : dist x q < R / 4 := hx
    change dist x p < 3 * R / 8
    have ht := dist_triangle x q p
    linarith
  · intro x hx
    apply χ.zero
    have hxq : R ≤ dist x q := by simpa only [mem_ball, not_lt] using hx
    have ht := dist_triangle x p q
    rw [dist_comm p q] at ht
    rw [dist_comm p x]
    linarith
  · intro i hi t ht
    obtain ⟨ht0, htδ⟩ := hJ i hi t ht
    exact (he t ht0 htδ q (by change dist q p < (3 * R / 8) / 2; linarith)).le

end RegularPointCoordinates

end

end OAI
