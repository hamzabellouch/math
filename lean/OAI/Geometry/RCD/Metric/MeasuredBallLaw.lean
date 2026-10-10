import OAI.Geometry.RCD.Coordinates.NormalizedProbabilityLaw

namespace OAI

/-! # Probability laws of the prescribed measured approximation maps -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

def normalizedBallPushforward {n : ℕ} (μ : Measure X) (p : X) (r S : ℝ)
    (v : X → Euclidean n) (hfin : μ (ball p (S*r))≠⊤) : ProbabilityMeasure (Euclidean n) := by
  let : Nonempty X := ⟨p⟩
  let : IsFiniteMeasure (μ.restrict (ball p (S*r))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  exact (normalizedProbabilityLaw (μ.restrict (ball p (S*r)))).map v

def euclideanBallProbability (n : ℕ) (S : ℝ) : ProbabilityMeasure (Euclidean n) := by
  let : IsFiniteMeasure (volume.restrict (ball (0:Euclidean n) S)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top (μ := (volume : Measure (Euclidean n))) (x := 0) (r := S))⟩
  exact normalizedProbabilityLaw (volume.restrict (ball (0:Euclidean n) S))

theorem normalizedBallPushforward_integral {n : ℕ} (μ : Measure X) (p : X) (r S : ℝ)
    (v : X → Euclidean n) (hfin : μ (ball p (S*r))≠⊤)
    (hpos : 0<μ.real (ball p (S*r))) (hv : Measurable v)
    {φ : Euclidean n → ℝ} (hφ : Continuous φ) :
    (∫ z, φ z ∂(normalizedBallPushforward μ p r S v hfin : Measure (Euclidean n)))=
      (μ.real (ball p (S*r)))⁻¹*(∫ x in ball p (S*r), φ (v x) ∂μ) := by
  let : Nonempty X := ⟨p⟩
  let : IsFiniteMeasure (μ.restrict (ball p (S*r))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  have hn : μ.restrict (ball p (S*r))≠0 := by
    intro he
    have hh := congrArg (fun ν : Measure X => ν.real univ) he
    simp [Measure.real] at hh
    exact (ne_of_gt hpos) hh
  simpa only [normalizedBallPushforward,Measure.real,Measure.restrict_apply_univ] using
    normalizedProbabilityLaw_map_integral (μ.restrict (ball p (S*r))) hn hv hφ

theorem euclideanBallProbability_integral {n : ℕ} {S : ℝ} (hS : 0<S)
    (φ : Euclidean n → ℝ) :
    (∫ z, φ z ∂(euclideanBallProbability n S : Measure (Euclidean n)))=
      (volume.real (ball (0:Euclidean n) S))⁻¹*(∫ z in ball 0 S, φ z) := by
  let : IsFiniteMeasure (volume.restrict (ball (0:Euclidean n) S)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top (μ := (volume : Measure (Euclidean n))) (x := 0) (r := S))⟩
  have hn : volume.restrict (ball (0:Euclidean n) S)≠0 := by
    intro he
    have hh := congrArg (fun ν : Measure (Euclidean n) => ν univ) he
    simp only [Measure.restrict_apply_univ,Measure.coe_zero,Pi.zero_apply] at hh
    exact (measure_ball_pos volume 0 hS).ne' hh
  simpa only [euclideanBallProbability,Measure.real,Measure.restrict_apply_univ] using
    normalizedProbabilityLaw_integral (volume.restrict (ball (0:Euclidean n) S)) hn φ

theorem measured_approximation_laws_tendsto {n : ℕ} {S : ℝ} (hS : 0<S)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {v : ℕ → X → Euclidean n}
    (hv : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (v k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hpos : ∀ k, 0<μ.real (ball (p k) (S*r k))) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => normalizedBallPushforward μ (p k) (r k) S (v k) (hfin k)) atTop
      (𝓝 (euclideanBallProbability n S)) := by
  apply MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ hbounded hLip
  obtain ⟨A,hA⟩ := hbounded
  obtain ⟨L,hL⟩ := hLip
  have hA0 : 0≤A := by simpa only [dist_self] using hA 0 0
  let B : ℝ≥0 := ⟨A+|φ 0|,add_nonneg hA0 (abs_nonneg _)⟩
  have hB (z : Euclidean n) : |φ z|≤B := by
    have hd := hA z 0
    rw [Real.dist_eq] at hd
    have ht := abs_add_le (φ z-φ 0) (φ 0)
    simp only [sub_add_cancel] at ht
    change |φ z|≤A+|φ 0|
    linarith
  let C : ℝ≥0 := L+B+1
  have hLC : L≤C := (le_add_of_nonneg_right (show (0:ℝ≥0)≤B from zero_le)).trans
    (le_add_of_nonneg_right zero_le_one)
  have hBC : B≤C := (le_add_of_nonneg_left (show (0:ℝ≥0)≤L from zero_le)).trans
    (le_add_of_nonneg_right zero_le_one)
  have ht := measured_approximation_test_tendsto hv hε (show 0<C by dsimp only [C]; positivity)
    (hL.weaken hLC) (fun z => (hB z).trans (by exact_mod_cast hBC))
  simp_rw [normalizedBallPushforward_integral μ _ _ _ _ _ (hpos _) (hv _).measurable hL.continuous,
    euclideanBallProbability_integral hS]
  exact ht

end RegularPointCoordinates

end

end OAI
