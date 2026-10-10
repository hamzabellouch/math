import OAI.Geometry.Perimeter.Regularity.HarmonicKernel

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem scaledHarmonicKernel_ball_bound {t : ℝ} (ht : 0 < t) (c x : Euc n) :
    |scaledHarmonicKernel t (c-x)| ≤
      (volume.real (Metric.ball (0:Euc n) 1)/harmonicKernelMass n) /
        volume.real (Metric.closedBall c (1/t)) := by
  have hω : 0 < volume.real (Metric.ball (0:Euc n) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume (0:Euc n) zero_lt_one).ne'
      measure_ball_lt_top.ne
  rw [Measure.addHaar_real_closedBall volume c (one_div_pos.mpr ht).le]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  calc
    _ ≤ t^n/harmonicKernelMass n := scaledHarmonicKernel_bound ht _
    _ = _ := by
      simp only [one_div,inv_pow]
      field_simp [ht.ne',hω.ne',(harmonicKernelMass_pos n).ne']

theorem scaledHarmonicKernel_ae_tendsto {u : Euc n → ℝ} (hu : LocallyIntegrable u volume) :
    ∀ᵐ c ∂volume, Tendsto (fun i : ℕ ↦
      ∫ x, scaledHarmonicKernel ((i:ℝ)+1) (c-x)*u x) atTop (𝓝 (u c)) := by
  have hd := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hu (1:ℝ)
  filter_upwards [hd] with c hc
  have hr : Tendsto (fun i : ℕ ↦ 1/((i:ℝ)+1)) atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun i ↦ (show 0 < 1/((i:ℝ)+1) from one_div_pos.mpr (by positivity))⟩
  have hm := hc (fun _ : ℕ ↦ c) (fun i : ℕ ↦ 1/((i:ℝ)+1)) hr (by
    apply Eventually.of_forall
    intro i
    exact Metric.mem_closedBall_self (by positivity))
  have h := tendsto_integral_smul_of_tendsto_average_norm_sub
    (g := fun i : ℕ ↦ fun x ↦ scaledHarmonicKernel ((i:ℝ)+1) (c-x))
    (volume.real (Metric.ball (0:Euc n) 1)/harmonicKernelMass n) hm
    (Eventually.of_forall fun i ↦ hu.integrableOn_isCompact (isCompact_closedBall _ _))
    (show Tendsto (fun i : ℕ ↦ ∫ x, scaledHarmonicKernel ((i:ℝ)+1) (c-x)) atTop (𝓝 1) by
      exact tendsto_const_nhds.congr (fun i ↦ (shifted_scaledHarmonicKernel_integral
        (by positivity : 0 < (i:ℝ)+1) c).symm))
    (Eventually.of_forall fun i ↦ shifted_scaledHarmonicKernel_support (by positivity) c)
    (Eventually.of_forall fun i x ↦ scaledHarmonicKernel_ball_bound (by positivity) c x)
  simpa only [smul_eq_mul] using h

end RPISingularHarnack

end

end OAI
