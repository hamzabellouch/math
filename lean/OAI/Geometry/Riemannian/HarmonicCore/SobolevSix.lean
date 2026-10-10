import OAI.Geometry.Riemannian.HarmonicCore.Sobolev

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal

namespace HarmonicCounterexample.Main.SmoothMetric3
open scoped NNReal ENNReal

noncomputable def sobolevSixConstant (R : ℝ) : ℝ≥0 :=
  eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure E3) (Metric.ball (0:E3) R) 2 6

lemma DirichletTest.sobolev_six {R : ℝ} (u : DirichletTest R) :
    eLpNorm (u.value : E3 → ℝ) 6 volume ≤
      (sobolevSixConstant R : ℝ≥0∞) * ENNReal.ofReal ‖u.derivative‖ := by
  have hh := eLpNorm_le_eLpNorm_fderiv_of_le (volume : Measure E3)
    (u.property.1.of_le (by norm_cast) : ContDiff ℝ 1 (u : E3 → ℝ))
    ((subset_tsupport (u:E3 → ℝ)).trans u.property.2.2) (p:=2) (q:=6) (by norm_num)
    (by norm_num [E3,finrank_euclideanSpace])
    (by norm_num [E3,finrank_euclideanSpace]) (Metric.isBounded_ball)
  have hn : eLpNorm (fderiv ℝ (u : E3 → ℝ)) 2 (volume : Measure E3) =
      eLpNorm (gradient (u : E3 → ℝ)) 2 (volume : Measure E3) :=
    eLpNorm_congr_norm_ae (u.property.1.continuous_fderiv (by simp)).aestronglyMeasurable
      u.derivative_memLp.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x ↦ (gradient_norm_fderiv u x).symm))
  norm_num only [ENNReal.coe_ofNat] at hh
  rw [hn] at hh
  rw [DirichletTest.value, eLpNorm_congr_ae u.value_memLp.coeFn_toLp]
  simpa only [sobolevSixConstant, DirichletTest.derivative,Lp.norm_toLp,
    ENNReal.ofReal_toReal u.derivative_memLp.ne] using hh

lemma sobolev_six (R : ℝ) (u : ZeroSobolev R) :
    eLpNorm (sobolevValue R u : E3 → ℝ) 6 volume ≤
      (sobolevSixConstant R : ℝ≥0∞) * ENNReal.ofReal ‖sobolevDerivative R u‖ := by
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp u.property
  have hval : Tendsto (fun n ↦ (v n).fst) atTop (𝓝 (sobolevValue R u)) :=
    (WithLp.fstL 2 ℝ ValueL2 DerivativeL2).continuous.continuousAt.tendsto.comp hlim
  have hder : Tendsto (fun n ↦ (v n).snd) atTop (𝓝 (sobolevDerivative R u)) :=
    (WithLp.sndL 2 ℝ ValueL2 DerivativeL2).continuous.continuousAt.tendsto.comp hlim
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hval).exists_seq_tendsto_ae
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 6)
    (fun n ↦ Lp.aestronglyMeasurable ((v (ns n)).fst)) (sobolevValue R u)
    (Lp.aestronglyMeasurable (sobolevValue R u)) hae
  have hbound : ∀ n, eLpNorm ((v n).fst : E3 → ℝ) 6 volume ≤
      (sobolevSixConstant R : ℝ≥0∞) * ENNReal.ofReal ‖(v n).snd‖ := by
    intro n
    obtain ⟨w,hw⟩ := hv n
    rw [← hw]
    exact w.sobolev_six
  have ht : Tendsto (fun n ↦ (sobolevSixConstant R : ℝ≥0∞) *
      ENNReal.ofReal ‖(v (ns n)).snd‖) atTop
      (𝓝 ((sobolevSixConstant R : ℝ≥0∞) * ENNReal.ofReal ‖sobolevDerivative R u‖)) :=
    (ENNReal.continuous_const_mul ENNReal.coe_ne_top).continuousAt.tendsto.comp
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hder.comp hns.tendsto_atTop).norm)
  exact (hfatou.trans (Filter.liminf_le_liminf (Eventually.of_forall (fun n ↦ hbound (ns n))))).trans_eq
    ht.liminf_eq

lemma sobolevValue_memLp_six (R : ℝ) (u : ZeroSobolev R) :
    MemLp (sobolevValue R u : E3 → ℝ) 6 volume :=
  (sobolev_six R u).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
