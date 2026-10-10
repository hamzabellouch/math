import OAI.Geometry.RCD.Metric.LocalizedLimitNorm
import OAI.Geometry.RCD.Metric.BallL2Exhaustion
import OAI.Geometry.RCD.Sobolev.NestedBallCutoff

namespace OAI

/-! # Global L2 normalization of a locally convergent measured value limit -/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem measured_value_limit_normalized (μ : Measure X)
    {n : ℕ} {S : ℝ} (hS : 0<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (v k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hmass : ∀ k, 0<μ.real (ball (p k) (S*r k)))
    (u : ℕ → X → ℝ) (g : Euclidean n → ℝ) (hgm : Measurable g)
    (hu : ∀ k, MemLp (u k) 2 (μ.restrict (ball (p k) (S*r k))))
    (hub : ∀ k, (μ.real (ball (p k) (S*r k)))⁻¹*
      (∫ x in ball (p k) (S*r k), (u k x)^2 ∂μ)≤1)
    (hg : ∀ ρ<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 ρ))
    (hconv : ∀ ρ : ℝ, 0<ρ → ρ<S → ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (ρ*r k)), |u k x-g (v k x)|≤η) :
    MemLp g 2 (volume.restrict (ball 0 S)) ∧
      (volume.real (ball (0:Euclidean n) S))⁻¹*(∫ z in ball 0 S, (g z)^2)≤1 := by
  have hV : 0<volume.real (ball (0:Euclidean n) S) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 hS).ne' measure_ball_ne_top
  let : IsFiniteMeasure (volume.restrict (ball (0:Euclidean n) S)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top (μ := (volume : Measure (Euclidean n))) (x := 0) (r := S))⟩
  have hlocal (ρ : ℝ) (hρ : 0<ρ) (hρS : ρ<S) :
      MemLp g 2 (volume.restrict (ball 0 ρ)) ∧
      (∫ z in ball 0 ρ, (g z)^2)≤volume.real (ball (0:Euclidean n) S) := by
    let σ := (ρ+S)/2
    let τ := (σ+S)/2
    have hρσ : ρ<σ := by dsimp only [σ]; linarith
    have hστ : σ<τ := by dsimp only [σ,τ]; linarith
    have hτS : τ<S := by dsimp only [σ,τ]; linarith
    have hτ : 0<τ := (hρ.trans hρσ).trans hστ
    let ψ := nestedBallCutoff (0:Euclidean n) ρ σ
    have hψ := nestedBallCutoff_lipschitz (0:Euclidean n) hρσ
    have hψb (z : Euclidean n) : |ψ z|≤1 := by
      rw [abs_of_nonneg (nestedBallCutoff_bounds 0 ρ σ z).1]
      exact (nestedBallCutoff_bounds 0 ρ σ z).2
    have hψ0 (z : Euclidean n) (hz : σ≤‖z‖) : ψ z=0 :=
      nestedBallCutoff_eq_zero 0 hρσ (by simpa only [dist_zero_left] using hz)
    obtain ⟨L,hgL⟩ := hg τ hτS
    obtain ⟨C,_,hF,hFb⟩ := interior_lipschitz_test_product (B := 1) hτ.le hgL hψ hψb
      (fun z hz => hψ0 z (hστ.le.trans hz.le))
    have hFp : MemLp (fun z => ψ z*g z) 2 (volume.restrict (ball 0 S)) :=
      MemLp.of_bound hF.continuous.aestronglyMeasurable C
        (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hFb z)
    have hsub : ball (0:Euclidean n) ρ ⊆ ball 0 S := ball_subset_ball hρS.le
    have heq : ∀ z∈ball (0:Euclidean n) ρ, ψ z*g z=g z := by
      intro z hz
      have hzρ : dist (0:Euclidean n) z≤ρ := by
        have hz' : dist z 0<ρ := hz
        simpa only [dist_comm] using hz'.le
      rw [show ψ z=1 from nestedBallCutoff_eq_one 0 hρσ hzρ,one_mul]
    have hgp : MemLp g 2 (volume.restrict (ball 0 ρ)) :=
      (memLp_congr_ae ((ae_restrict_mem measurableSet_ball).mono fun z hz => heq z hz)).mp
        (hFp.mono_measure (Measure.restrict_mono_set volume hsub))
    refine ⟨hgp,?_⟩
    have hcut := localized_limit_sq_le_one μ hτ.le hστ hτS.le p r ε v hr hεlim hv hfin hmass
      u g ψ hu hub hgL hψ hψb hψ0 (hconv τ hτ hτS)
    have hbound : (∫ z in ball 0 S, (ψ z*g z)^2)≤volume.real (ball (0:Euclidean n) S) := by
      simpa only [mul_one] using (inv_mul_le_iff₀ hV).mp hcut
    calc
      _ = ∫ z in ball 0 ρ, (ψ z*g z)^2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        rw [heq z hz]
      _ ≤ ∫ z in ball 0 S, (ψ z*g z)^2 :=
        setIntegral_mono_set hFp.integrable_sq (Eventually.of_forall fun _ => sq_nonneg _)
          (Eventually.of_forall fun _ hz => hsub hz)
      _ ≤ _ := hbound
  obtain ⟨hLp,hI⟩ := ball_L2_of_local_integral_bound volume hS hV.le g hgm
    (fun ρ hρ hρS => (hlocal ρ hρ hρS).1) (fun ρ hρ hρS => (hlocal ρ hρ hρS).2)
  refine ⟨hLp,?_⟩
  calc
    _ ≤ (volume.real (ball (0:Euclidean n) S))⁻¹*volume.real (ball (0:Euclidean n) S) :=
      mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hV.le)
    _ = 1 := inv_mul_cancel₀ hV.ne'

end RegularPointCoordinates

end

end OAI
