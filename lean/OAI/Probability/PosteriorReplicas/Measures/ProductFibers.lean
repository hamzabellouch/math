import OAI.Probability.PosteriorReplicas.Geometry.BaseContinuity
import OAI.Probability.PosteriorReplicas.Geometry.BaseFunProp
import OAI.Probability.PosteriorReplicas.Measures.PiTools

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma base_pi_sample_representation {d k : ℕ} {A : Rows d k}
    (hA : LinearIndependent ℝ A) (hk : k < d) (base : BaseLaw) (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => volume.withDensity (baseDensity base A))).prod
      (gaussianRows d n)).map (fun z i => basePoint base A (z.1 i) (z.2 i)) =
        Measure.pi (fun _ : Fin n => base.measure d) := by
  have : IsProbabilityMeasure (volume.withDensity (baseDensity base A)) := by
    have : NeZero d := ⟨by omega⟩
    rw [← projected_base_measure hA hk]
    infer_instance
  have hm : Measurable (fun z : Labels k × Vec d => basePoint base A z.1 z.2) := by
    exact measurable_basePoint_comp base measurable_const measurable_fst measurable_snd
  have hsample : (Measure.pi (fun _ : Fin n =>
      (volume.withDensity (baseDensity base A)).prod (stdGaussian (Vec d)))).map
      (fun z i => basePoint base A (z i).1 (z i).2) = Measure.pi (fun _ => base.measure d) := by
    rw [Measure.pi_map_pi (fun _ => hm.aemeasurable)]
    simp_rw [base_sample_representation hA hk base]
  have he := measurePreserving_arrowProdEquivProdArrow (Labels k) (Vec d) (Fin n)
    (fun _ => volume.withDensity (baseDensity base A)) (fun _ => stdGaussian (Vec d))
  unfold gaussianRows
  rw [← he.map_eq, Measure.map_map (by fun_prop) he.measurable]
  exact hsample

lemma base_pi_lintegral {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {n : ℕ} {g : (Fin n → Vec d) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ v, g v ∂Measure.pi (fun _ => base.measure d) =
      ∫⁻ y : Fin n → Labels k, (∏ i, baseDensity base A (y i)) *
        ∫⁻ R, g (fun i => basePoint base A (y i) (R i)) ∂gaussianRows d n ∂volume := by
  have hb0 := (measurable_baseDensity (d := d) (k := k) base).comp
    (show Measurable (fun y : Labels k => (A,y)) from measurable_const.prodMk measurable_id)
  simp only [Function.comp_def] at hb0
  have hb : Measurable (baseDensity base A) := hb0
  have : IsProbabilityMeasure (volume.withDensity (baseDensity base A)) := by
    have : NeZero d := ⟨by omega⟩
    rw [← projected_base_measure hA hk]
    infer_instance
  have hs : Measurable (fun z : (Fin n → Labels k) × Rows d n =>
      g (fun i => basePoint base A (z.1 i) (z.2 i))) := hg.comp (by fun_prop)
  rw [← base_pi_sample_representation hA hk base n, lintegral_map hg (by fun_prop),
    lintegral_prod _ hs.aemeasurable, pi_withDensity _ _ (fun _ => hb),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hs.lintegral_prod_right]

  rfl

lemma baseFiber_pi_lintegral {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k)
    {n : ℕ} {g : (Fin n → Vec d) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ v, g v ∂Measure.pi (fun _ => baseFiber base A y) =
      ∫⁻ R, g (fun i => basePoint base A y (R i)) ∂gaussianRows d n := by
  simp_rw [baseFiber_eq_map]
  rw [← Measure.pi_map_pi (fun _ => (measurable_basePoint_fixed base A y).aemeasurable),
    lintegral_map hg (by fun_prop)]
  rfl

end PosteriorReplicas
end

end OAI
