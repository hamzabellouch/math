import Mathlib
import OAI.Geometry.CAT0Fillings.Radial.ClosedInequality

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma radial_completed_pointwise {n g r d h : ℝ} (hn : 0 ≤ n) (hg : 0 ≤ g)
    (hd : d ≤ 1) :
    n*g*d+r*h-n/4*r^2*g ≤ n*(1-r*Real.sqrt (1-d))*g+r*h := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hd)
  have he : n*(1-r*Real.sqrt (1-d))*g+r*h -
      (n*g*d+r*h-n/4*r^2*g) = n*g*(Real.sqrt (1-d)-r/2)^2 := by
    nlinarith [congrArg (fun x : ℝ => n*g*x) hs]
  exact sub_nonneg.mp (he.symm ▸ mul_nonneg (mul_nonneg hn hg) (sq_nonneg _))

lemma memLp_radialCompletedA (o : X) :
    MemLp (fun w => (k+1:ℝ)*‖q.gradient (LipschitzWith.dist_right o) w‖^2-
      (k+1:ℝ)/4*dist o (q.atlasParam w)^2) 2 q.atlasMeasure := by
  have hd := (Lp.aestronglyMeasurable (q.gradient (LipschitzWith.dist_right o))).norm.pow 2
  have hr : AEStronglyMeasurable (fun w => dist o (q.atlasParam w)) q.atlasMeasure :=
    ((LipschitzWith.dist_right o).continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable
  apply MemLp.of_bound ((aestronglyMeasurable_const.mul hd).sub (aestronglyMeasurable_const.mul (hr.pow 2)))
    ((k+1:ℝ)+(k+1:ℝ)/4*(Metric.diam (univ : Set X))^2)
  filter_upwards [q.ae_gradient_bound (LipschitzWith.dist_right o)] with w hw
  rw [Real.norm_eq_abs]
  apply (abs_sub _ _).trans
  simp only [Pi.mul_apply,Pi.pow_apply] at *
  rw [abs_of_nonneg (by positivity : 0 ≤ (k+1:ℝ)*‖q.gradient (LipschitzWith.dist_right o) w‖^2),
    abs_of_nonneg (by positivity : 0 ≤ (k+1:ℝ)/4*dist o (q.atlasParam w)^2)]
  have hm := radius_bound o (q.atlasParam w)
  have hs : ‖q.gradient (LipschitzWith.dist_right o) w‖^2 ≤ 1 := by
      norm_num only [NNReal.coe_one] at hw
      simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr hw
  apply add_le_add
  · calc
      _ ≤ (k+1:ℝ)*1 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := mul_one _
  · gcongr

lemma completed_radial (o : X) (P : q.Sobolev)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hr : q.radialDefect o P ≤ 0) :
    (∫ w, ((k+1:ℝ)*‖q.gradient (LipschitzWith.dist_right o) w‖^2-
      (k+1:ℝ)/4*dist o (q.atlasParam w)^2)*q.inclusion P (q.atlasParam w)+
      dist o (q.atlasParam w)*inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.closedGradient P w) ∂q.atlasMeasure) ≤ 0 := by
  have hp := (Lp.memLp (q.inclusion P)).comp_measurePreserving q.atlas_preserving
  have hB : Integrable (fun w => inner ℝ (q.radialB o w) (q.closedGradient P w)) q.atlasMeasure := by
    apply (L2.integrable_inner (𝕜 := ℝ) ((q.memLp_radialB o).toLp _) (q.closedGradient P)).congr
    filter_upwards [(q.memLp_radialB o).coeFn_toLp] with w hw
    rw [hw]
  have hB' : Integrable (fun w => dist o (q.atlasParam w)*inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.closedGradient P w)) q.atlasMeasure := by
    simpa only [radialB,real_inner_smul_left] using hB
  apply le_trans (integral_mono_ae (((q.memLp_radialCompletedA o).integrable_mul hp).add hB')
    (((q.memLp_radialA o).integrable_mul hp).add hB) ?_) ?_
  · filter_upwards [q.atlas_preserving.quasiMeasurePreserving.ae hP,q.ae_gradient_bound (LipschitzWith.dist_right o)] with w hw hb
    have hd : ‖q.gradient (LipschitzWith.dist_right o) w‖^2 ≤ 1 := by
      norm_num only [NNReal.coe_one] at hb
      simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr hb
    dsimp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply,radialA,radialB]
    rw [real_inner_smul_left]
    convert radial_completed_pointwise (n := (k+1:ℝ)) (r := dist o (q.atlasParam w))
      (h := inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.closedGradient P w)) (by positivity) hw hd using 1
    ring
  · simp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply]
    rw [←q.radialDefect_eq_integral]
    exact hr
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
lemma scalar_added_cancel {A B C D κ β n : ℝ} (hr : A ≤ 0)
    (he : 4*β*B+n*C=n*D) : κ^2*(A+β*B+n/4*C) ≤ κ^2*n/4*D := by
  have hh : β*B+n/4*C=n/4*D := by linarith
  calc
    _ = κ^2*(A+(β*B+n/4*C)) := by ring
    _ ≤ κ^2*(n/4*D) := by rw [hh]; exact mul_le_mul_of_nonneg_left (add_le_of_nonpos_left hr) (sq_nonneg κ)
    _ = _ := by ring
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
noncomputable def completedExpression (o : X) (G : q.Sobolev) (z : ℕ × Euc (k+1)) : ℝ :=
  ((k+1:ℝ)*‖q.gradient (LipschitzWith.dist_right o) z‖^2-
    (k+1:ℝ)/4*dist o (q.atlasParam z)^2)*q.inclusion G (q.atlasParam z)+
    dist o (q.atlasParam z)*inner ℝ (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient G z)
lemma integrable_completedExpression (o : X) (G : q.Sobolev) :
    Integrable (q.completedExpression o G) q.atlasMeasure := by
  have hp := (Lp.memLp (q.inclusion G)).comp_measurePreserving q.atlas_preserving
  have hB : Integrable (fun z => inner ℝ (q.radialB o z) (q.closedGradient G z)) q.atlasMeasure := by
    apply (L2.integrable_inner (𝕜 := ℝ) ((q.memLp_radialB o).toLp _) (q.closedGradient G)).congr
    filter_upwards [(q.memLp_radialB o).coeFn_toLp] with z hz
    rw [hz]
  have hB' : Integrable (fun z => dist o (q.atlasParam z)*inner ℝ (q.gradient (LipschitzWith.dist_right o) z) (q.closedGradient G z)) q.atlasMeasure := by
    simpa only [radialB,real_inner_smul_left] using hB
  exact ((q.memLp_radialCompletedA o).integrable_mul hp).add hB'

lemma added_energy_integral (o : X) (v G Q : q.Sobolev) {β κ : ℝ}
    {E : ℕ × Euc (k+1) → ℝ}
    (hE : E =ᵐ[q.atlasMeasure] (fun z => κ^2*(q.completedExpression o G z+
      β*inner ℝ (q.closedGradient v z) (q.closedGradient Q z)+
      (k+1:ℝ)/4*(q.inclusion v (q.atlasParam z)*q.inclusion Q (q.atlasParam z)))))
    (hr : (∫ z, q.completedExpression o G z ∂q.atlasMeasure) ≤ 0)
    (heuler : 4*β*inner ℝ (q.closedGradient v) (q.closedGradient Q)+
      (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion Q) =
      (k+1:ℝ)*(∫ x, (q.inclusion v x)^(1+4*β)*q.inclusion Q x ∂MassMeasure.currentMassMeasure hT)) :
    Integrable E q.atlasMeasure ∧
      (∫ z, E z ∂q.atlasMeasure) ≤ κ^2*(k+1:ℝ)/4*
        (∫ x, (q.inclusion v x)^(1+4*β)*q.inclusion Q x ∂MassMeasure.currentMassMeasure hT) := by
  have hpair := L2.integrable_inner (𝕜 := ℝ) (q.closedGradient v) (q.closedGradient Q)
  have hval : Integrable (fun x => q.inclusion v x*q.inclusion Q x) (MassMeasure.currentMassMeasure hT) :=
    (Lp.memLp (q.inclusion v)).integrable_mul (Lp.memLp (q.inclusion Q))
  have hm := q.atlas_preserving.integrable_comp_of_integrable hval
  change Integrable (fun z => q.inclusion v (q.atlasParam z)*q.inclusion Q (q.atlasParam z)) q.atlasMeasure at hm
  have hi := (((q.integrable_completedExpression o G).add (hpair.const_mul β)).add
    (hm.const_mul ((k+1:ℝ)/4))).const_mul (κ^2)
  refine ⟨hi.congr hE.symm,?_⟩
  have hi1 : Integrable (fun z => q.completedExpression o G z+
      β*inner ℝ (q.closedGradient v z) (q.closedGradient Q z)) q.atlasMeasure :=
    (q.integrable_completedExpression o G).add (hpair.const_mul β)
  rw [integral_congr_ae hE,integral_const_mul,integral_add hi1 (hm.const_mul _),
    integral_add (q.integrable_completedExpression o G) (hpair.const_mul β),
    integral_const_mul,integral_const_mul,←L2.inner_def]
  have hmap : (∫ z, q.inclusion v (q.atlasParam z)*q.inclusion Q (q.atlasParam z) ∂q.atlasMeasure) =
      inner ℝ (q.inclusion v) (q.inclusion Q) := by
    have hmap := integral_map (μ := q.atlasMeasure)
      (f := fun x => q.inclusion v x*q.inclusion Q x)
      q.atlas_preserving.measurable.aemeasurable
      (by rw [q.atlas_preserving.map_eq]; exact hval.aestronglyMeasurable)
    rw [q.atlas_preserving.map_eq] at hmap
    rw [←hmap,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [RCLike.inner_apply,conj_trivial]
    exact mul_comm _ _
  rw [hmap]
  exact scalar_added_cancel hr heuler
end CAT0Fillings.ChartGeometry
end

end OAI
