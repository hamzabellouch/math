import Mathlib
import OAI.Analysis.AffineBernstein.ProjectiveCone

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma projective_cone_lintegral_eq_global
    (f : WithLp 2 (F × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y in Metric.ball (0:WithLp 2 (F × ℝ)) 1 \ {0},
      if 0 < (WithLp.ofLp y).2 then f y else 0) =
    ∫⁻ t in Ioi (0:ℝ), ∫⁻ x : F,
      if ‖WithLp.toLp 2 (x,t)‖ < 1 then f (WithLp.toLp 2 (x,t)) else 0 := by
  let A := Metric.ball (0:WithLp 2 (F × ℝ)) 1 \ {0}
  let g : WithLp 2 (F × ℝ) → ℝ≥0∞ := fun y => if 0 < (WithLp.ofLp y).2 then f y else 0
  let G : F × ℝ → ℝ≥0∞ := fun q =>
    if 0 < q.2 then (if ‖WithLp.toLp 2 q‖ < 1 then f (WithLp.toLp 2 q) else 0) else 0
  have hG : Measurable G := by
    apply Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    · apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      · exact hf.comp (MeasurableEquiv.toLp 2 (F × ℝ)).measurable
      · exact measurable_const
    · exact measurable_const
  have he (q : F × ℝ) : A.indicator g (WithLp.toLp 2 q) = G q := by
    by_cases ht : 0 < q.2
    · have hq : WithLp.toLp 2 q ≠ 0 := by
        intro h
        have hh := congrArg (fun y : WithLp 2 (F × ℝ) => (WithLp.ofLp y).2) h
        have hq2 : q.2 = 0 := hh
        exact ht.ne' hq2
      simp [A,g,G,Set.indicator,Metric.mem_ball,dist_zero_right,ht,hq]
    · simp [A,g,G,Set.indicator,ht]
  change (∫⁻ y in A, g y) = _
  rw [← lintegral_indicator (Metric.isOpen_ball.measurableSet.diff (measurableSet_singleton _))]
  rw [← (WithLp.volume_preserving_toLp F ℝ).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (F × ℝ)).measurableEmbedding (A.indicator g)]
  simp_rw [he]
  rw [MeasureTheory.Measure.volume_eq_prod,lintegral_prod_symm G hG.aemeasurable]
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro t
  by_cases ht : 0 < t
  · simp [G,Set.indicator,ht]
  · simp [G,Set.indicator,ht]

/- Exact projective-coordinate formula for the genuine Euclidean hemisphere
measure. This is proved from Haar polar coordinates and ordinary-volume
scaling, not an assumed surface-area/Jacobian identity. The tangent space may
have dimension zero. -/
theorem projective_hemisphere_lintegral
    (f : WithLp 2 (F × ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hscale : ∀ (x : WithLp 2 (F × ℝ)) (t : ℝ), 0 < t → f (t • x) = f x) :
    (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
      if 0 < (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 then f e else 0 ∂volume.toSphere) =
    ∫⁻ x : F, ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
      (Module.finrank ℝ F+1)) * f (WithLp.toLp 2 (x,(1:ℝ))) := by
  let E := WithLp 2 (F × ℝ)
  let g : E → ℝ≥0∞ := fun y => if 0 < (WithLp.ofLp y).2 then f y else 0
  have hg : Measurable g := by
    apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) hf measurable_const
  have hgs (y : E) (t : ℝ) (ht : 0 < t) : g (t • y) = g y := by
    have hm : (WithLp.ofLp (t • y)).2 = t * (WithLp.ofLp y).2 := rfl
    dsimp only [g]
    simp only [hm,hscale y t ht,mul_pos_iff_of_pos_left ht]
  have hh := sphere_lintegral_mul_radial_eq (volume : Measure E)
    (hg.comp measurable_subtype_coe) (fun e r hr _ => (hgs e r hr).symm)
  have hd : Module.finrank ℝ E = Module.finrank ℝ F + 1 := by
    change Module.finrank ℝ (WithLp 2 (F × ℝ)) = _
    rw [(WithLp.linearEquiv 2 ℝ (F × ℝ)).finrank_eq,Module.finrank_prod,Module.finrank_self]
  rw [hd,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at hh
  rw [projective_cone_lintegral_eq_global f hf,projective_cone_lintegral f hf hscale] at hh
  let c : ℝ≥0∞ := ENNReal.ofReal (1/((Module.finrank ℝ F:ℝ)+1))
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hp : Measurable (fun x : F => ENNReal.ofReal
      (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^ (Module.finrank ℝ F+1)) * f (WithLp.toLp 2 (x,(1:ℝ)))) := by
    apply Measurable.mul
    · fun_prop
    · exact hf.comp (by fun_prop)
  have he (x : F) : ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
      (Module.finrank ℝ F+1)/(Module.finrank ℝ F+1)) * f (WithLp.toLp 2 (x,(1:ℝ))) =
      (ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
      (Module.finrank ℝ F+1)) * f (WithLp.toLp 2 (x,(1:ℝ)))) * c := by
    dsimp [c]
    rw [div_eq_mul_inv,ENNReal.ofReal_mul (by positivity)]
    simp only [one_div]
    ac_rfl
  simp_rw [he] at hh
  rw [lintegral_mul_const _ hp] at hh
  exact (ENNReal.mul_left_inj hc ENNReal.ofReal_ne_top).mp hh

end AffineBernstein
end

end OAI
