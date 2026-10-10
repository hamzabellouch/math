import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.ChartLength
import OAI.Geometry.WeakMTW.Potentials.SmoothEnvelope

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal Manifold NNReal
namespace ChartMetric
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
 theorem chart_inverse_lipschitz_bound (z : M) {Z : E} {r : ℝ} {B : ℝ≥0} (hB : 1 ≤ B)
     (hT : Metric.ball Z r ⊆ (chartAt E z).target)
     (hG : ∀ X ∈ Metric.ball Z r, ‖metric z X‖ ≤ B) :
     LipschitzOnWith B (chartAt E z).symm (Metric.ball Z r) := by
   intro X hX Y hY
   let η := ContinuousAffineMap.lineMap (R := ℝ) X Y
   have hη (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : η t ∈ Metric.ball Z r :=
     (convex_ball Z r).mapsTo_lineMap hX hY ht
   have hc : ContDiffOn ℝ 1 η (Icc (0:ℝ) 1) := η.contDiff.contDiffOn
   have hct : ∀ t ∈ Icc (0:ℝ) 1, η t ∈ (chartAt E z).target := fun t ht => hT (hη t ht)
   have hmc := contMDiffOn_chart_symm.comp (contMDiffOn_iff_contDiffOn.mpr hc) hct
   have hed := riemannianEDist_le_pathELength hmc
     (by simp [η,ContinuousAffineMap.coe_lineMap_eq] : ((chartAt E z).symm ∘ η) 0 = (chartAt E z).symm X)
     (by simp [η,ContinuousAffineMap.coe_lineMap_eq] : ((chartAt E z).symm ∘ η) 1 = (chartAt E z).symm Y)
     (by norm_num : (0:ℝ) ≤ 1)
   rw [←IsRiemannianManifold.out,←coordinateLength_eq_pathELength z hc hct] at hed
   apply hed.trans
   rw [NormalNeighborhood.NormalFlow.coordinateLength]
   have hnorm (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
       Real.sqrt (metric z (η t) (deriv η t) (deriv η t)) ≤ B*‖Y-X‖ := by
     have hd : deriv η t = Y-X := by simp [η,ContinuousAffineMap.coe_lineMap_eq]
     rw [hd]
     have hn := ContinuousLinearMap.le_opNorm₂ (metric z (η t)) (Y-X) (Y-X)
     have hg := hG (η t) (hη t ht)
     have hb : (B:ℝ) ≤ (B:ℝ)^2 := by exact_mod_cast (le_self_pow₀ hB (by norm_num : 2 ≠ 0))
     have hh : metric z (η t) (Y-X) (Y-X) ≤ (B*‖Y-X‖)^2 := by
       have h := (le_abs_self (metric z (η t) (Y-X) (Y-X))).trans hn
       have h1 := mul_le_mul_of_nonneg_right hg (sq_nonneg ‖Y-X‖)
       have h2 := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖Y-X‖)
       nlinarith
     exact (Real.sqrt_le_iff).mpr ⟨by positivity,hh⟩
   calc
     _ ≤ ∫⁻ _t in Icc (0:ℝ) 1, ENNReal.ofReal (B*‖Y-X‖) :=
       setLIntegral_mono' measurableSet_Icc (fun t ht => ENNReal.ofReal_le_ofReal (hnorm t ht))
     _ = B*edist X Y := by
       simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,
         ENNReal.ofReal_one,mul_one,ENNReal.ofReal_mul B.coe_nonneg,ENNReal.ofReal_coe_nnreal]
       rw [ofReal_norm,← edist_eq_enorm_sub,edist_comm]

 theorem chart_inverse_local_lipschitz (z : M) :
     ∃ r : ℝ, ∃ B : ℝ≥0, 0 < r ∧ 0 < B ∧
       Metric.ball (chartAt E z z) r ⊆ (chartAt E z).target ∧
       LipschitzOnWith B (chartAt E z).symm (Metric.ball (chartAt E z z) r) := by
   let c := chartAt E z
   have hZ : c z ∈ c.target := c.map_source (mem_chart_source E z)
   have hcont : ContinuousAt (metric z) (c z) :=
     (metric_smooth z).continuousOn.continuousAt (c.open_target.mem_nhds hZ)
   let B : ℝ≥0 := ⟨‖metric z (c z)‖+1,by positivity⟩
   have hB : 1 ≤ B := by change (1:ℝ) ≤ ‖metric z (c z)‖+1; linarith [norm_nonneg (metric z (c z))]
   have hnear : ∀ᶠ X in 𝓝 (c z), ‖metric z X‖ ≤ B :=
     QuadraticEnvelope.norm_eventually_bound (f := metric z) (x := c z) hcont
   obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (c.open_target.mem_nhds hZ) hnear)
   refine ⟨r,B,hr,lt_of_lt_of_le zero_lt_one hB,fun X hX => (hball hX).1,?_⟩
   exact chart_inverse_lipschitz_bound z hB (fun X hX => (hball hX).1) (fun X hX => (hball hX).2)
end
end ChartMetric
end

end WeakMTWGlobalSupport

end OAI
