import Mathlib
import OAI.Analysis.BiholderTransport.Contact.ContactRelationChart
import OAI.Analysis.BiholderTransport.Contact.LowerTestContact

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section ActualLowerTestBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.lower_test_chart_det_bound (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} {rho0 rho1 : M → ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hrho0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (hrho1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (hdual : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b))
    {a b : M} {z : Model n} {r ε : ℝ} {T : Set M} {Da Cb : ℝ≥0}
    {φ : Model n → ℝ} {S : Model n → Model n} {J : Model n →L[ℝ] Model n}
    (hr : 0 < r) (hε : 0 < ε)
    (hchart : Metric.closedBall z r⊆(extChartAt 𝓘(ℝ,Model n) a).target)
    (hDa : LipschitzOnWith Da (extChartAt 𝓘(ℝ,Model n) a).symm (Metric.closedBall z r))
    (hCb : LipschitzOnWith Cb (extChartAt 𝓘(ℝ,Model n) b) T)
    (hφ : ContinuousOn φ (Metric.closedBall z r))
    (hz : u ((extChartAt 𝓘(ℝ,Model n) a).symm z)=φ z)
    (hgap : ∀ w∈Metric.closedBall z r,
      ε*dist w z^2≤u ((extChartAt 𝓘(ℝ,Model n) a).symm w)-φ w)
    (hSregion : ∀ w∈Metric.ball z r,
      S w∈(extChartAt 𝓘(ℝ,Model n) b).target ∧
        (extChartAt 𝓘(ℝ,Model n) b).symm (S w)∈T)
    (hmountain : ∀ w∈Metric.ball z r, ∀ q∈Metric.closedBall z r,
      φ w+cost ((extChartAt 𝓘(ℝ,Model n) a).symm w)
        ((extChartAt 𝓘(ℝ,Model n) b).symm (S w)) ≤
      φ q+cost ((extChartAt 𝓘(ℝ,Model n) a).symm q)
        ((extChartAt 𝓘(ℝ,Model n) b).symm (S w)))
    (hS : HasStrictFDerivAt S J z) : |J.det| ≤ (cap/lam)*((Cb:ℝ)*(Da:ℝ))^n := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let ψ := extChartAt 𝓘(ℝ,Model n) b
  let C := (cap/lam)*((Cb:ℝ)*(Da:ℝ))^n
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hχ : ContinuousOn χ.symm (Metric.closedBall z r) :=
    (continuousOn_extChartAt_symm a).mono hchart
  apply lower_test_abs_det_le (metricVolume n) hr hε hC
    (u.continuous.comp_continuousOn hχ) hφ
    (fun y => (continuous_cost_left (ψ.symm y)).comp_continuousOn hχ) hz hgap
    (R := chartContactRelation a b u v T) ?_ hmountain ?_ hS
  · intro w hw q hq hlocal
    exact ⟨(hSregion q hq).1,(hSregion q hq).2,
      hmtw.chart_local_contact_global u.continuous v.continuous hdual
        (hchart (Metric.ball_subset_closedBall hw)) hlocal⟩
  · intro A hA hAball
    have HA := chartContactRelation_volume_upper hlam hrho0 hrho1 hdual hmin hA
      (fun w hw => hchart (Metric.ball_subset_closedBall (hAball hw)))
      (hDa.mono (fun w hw => Metric.ball_subset_closedBall (hAball hw))) hCb
    have heq : ENNReal.ofReal lam*ENNReal.ofReal C=
        ENNReal.ofReal cap*((Cb:ℝ≥0∞)*(Da:ℝ≥0∞))^n := by
      rw [←ENNReal.ofReal_mul hlam.le]
      have H : lam*C=cap*((Cb:ℝ)*(Da:ℝ))^n := by dsimp only [C]; field_simp
      rw [H,ENNReal.ofReal_mul hcap,ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_coe_nnreal]
    apply (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_ne_zero_iff.mpr hlam)
      ENNReal.ofReal_ne_top).mp
    rw [←heq] at HA
    simpa only [mul_assoc,mul_left_comm,mul_comm] using HA

end ActualLowerTestBound
end WeakMTWTransport

end

end

end

end OAI
