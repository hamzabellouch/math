import OAI.Probability.PosteriorReplicas.Measures.DensityDifferentiation

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

def euclideanLabelLaw {d k : ℕ} (ν : Measure (Vec d)) (A : Rows d k) : Measure (Vec k) :=
  ν.map (fun x => WithLp.toLp 2 (labels A x))

instance {d k : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν] (A : Rows d k) :
    IsFiniteMeasure (euclideanLabelLaw ν A) := by unfold euclideanLabelLaw; infer_instance

lemma euclidean_map_density {k : ℕ} {h : Labels k → ℝ≥0∞} (hh : Measurable h) :
    (volume.withDensity h).map (WithLp.toLp 2) =
      (volume : Measure (Vec k)).withDensity (fun y => h (WithLp.ofLp y)) := by
  have ht : Measurable (WithLp.toLp 2 : Labels k → Vec k) := WithLp.measurable_toLp _ _
  have ho : Measurable (WithLp.ofLp : Vec k → Labels k) := WithLp.measurable_ofLp _ _
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg ht,
    lintegral_withDensity_eq_lintegral_mul _ hh (show Measurable (fun x => g (WithLp.toLp 2 x)) from hg.comp ht),
    lintegral_withDensity_eq_lintegral_mul _ (show Measurable (fun y => h (WithLp.ofLp y)) from hh.comp ho) hg]
  simp only [Pi.mul_apply]
  rw [← (PiLp.volume_preserving_toLp (Fin k)).lintegral_comp
      (show Measurable (fun y => h (WithLp.ofLp y) * g y) from (hh.comp ho).mul hg)]

lemma euclideanLabelLaw_density {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    euclideanLabelLaw ((base.measure d).withDensity f) A =
      volume.withDensity (fun y : Vec k => projectedDensity base f A (WithLp.ofLp y)) := by
  have ht : Measurable (WithLp.toLp 2 : Labels k → Vec k) := WithLp.measurable_toLp _ _
  have hl : Measurable (labels A) := by unfold labels; fun_prop
  have hp0 := (measurable_projectedDensity (d := d) (k := k) base hf).comp
    (show Measurable (fun y : Labels k => (A,y)) from measurable_const.prodMk measurable_id)
  simp only [Function.comp_def] at hp0
  have hp : Measurable (projectedDensity base f A) := hp0
  change Measure.map (WithLp.toLp 2 ∘ labels A) _ = _
  rw [← Measure.map_map ht hl, projected_measure hA hk base hf]
  exact euclidean_map_density hp

lemma euclideanLabelLaw_ball {d k : ℕ} (ν : Measure (Vec d)) (A : Rows d k)
    (y : Labels k) (r : ℝ) :
    euclideanLabelLaw ν A (ball (WithLp.toLp 2 y) r) =
      ν {x | labelNorm (labels A x - y) < r} := by
  rw [euclideanLabelLaw, Measure.map_apply (by fun_prop) measurableSet_ball]
  rfl

lemma euclidean_label_ball_volume {k : ℕ} (y : Labels k) (r : ℝ) :
    (volume : Measure (Vec k)) (ball (WithLp.toLp 2 y) r) =
      (volume : Measure (Labels k)) {v | labelNorm v < r} := by
  rw [Measure.addHaar_ball_center]
  rw [← (PiLp.volume_preserving_toLp (Fin k)).measure_preimage (by measurability)]
  congr 1
  ext v
  simp only [mem_preimage, mem_ball, dist_zero_right]
  rfl

lemma projectedDensity_uniform_bound {d k : ℕ} (hk : k + 2 ≤ d) (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} {L : ℝ≥0∞} (hfL : ∀ x, f x ≤ L) (A : Rows d k) (y : Labels k) :
    projectedDensity base f A y ≤
      ENNReal.ofReal (baseProjectionConstant base d k / Real.sqrt (rowGram A).det) * L :=
  mul_le_mul' (baseDensity_le_sup hk base A y) (tiltMass_le base hfL A y)

lemma ae_ballDensityVersion {d k : ℕ} (hk : 1 ≤ k) (hk' : k < d) (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞)
    (hfL : ∀ x, f x ≤ L) {A : Rows d k} (hA : LinearIndependent ℝ A) :
    projectedDensity base f A =ᵐ[volume]
      ballDensityVersion ((base.measure d).withDensity f) A := by
  have : NeZero d := ⟨by omega⟩
  have : NeZero k := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  have he0 := (measurable_projectedDensity (d := d) (k := k) base hf).comp
    (show Measurable (fun y : Vec k => (A,WithLp.ofLp y)) from
      measurable_const.prodMk (WithLp.measurable_ofLp 2 (Labels k)))
  simp only [Function.comp_def] at he0
  have he : Measurable (fun y : Vec k => projectedDensity base f A (WithLp.ofLp y)) := he0
  have hd := ae_ball_differentiation (E := Vec k) he
    (euclideanLabelLaw_density hA hk' base hf)
  have hde := (PiLp.volume_preserving_toLp (Fin k)).quasiMeasurePreserving.ae hd
  filter_upwards [hde] with y hy
  have hn : Tendsto (fun n : ℕ => (n+1:ℝ)⁻¹) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall (fun n => by change 0 < (n+1:ℝ)⁻¹; positivity)⟩
    simpa only [noiseScale, one_div] using
      (show Tendsto (fun n => noiseScale n) atTop (𝓝 0) from tendsto_noiseScale)
  have H := hy.comp hn
  simp only [euclideanLabelLaw_ball, euclidean_label_ball_volume] at H
  simpa only [ballDensityVersion, div_eq_mul_inv, mul_comm, Function.comp_def] using H.liminf_eq.symm

end PosteriorReplicas
end

end OAI
