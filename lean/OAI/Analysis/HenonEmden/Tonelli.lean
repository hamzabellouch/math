import OAI.Analysis.HenonEmden.SourceEndpoints

namespace OAI

universe uE

section Tonelli

open MeasureTheory Set Function
open scoped ENNReal
namespace HenonLaneEmden.LayerTonelli

variable {E : Type uE} [MeasurableSpace E]

/-- The literal positive source subgraph; no integrability is implicit. -/
def sourceSubgraph (f : E → ℝ) : Set (E × ℝ) := {z | 0 < z.2 ∧ z.2 < f z.1}

lemma measurableSet_sourceSubgraph {f : E → ℝ} (hf : Measurable f) :
    MeasurableSet (sourceSubgraph f) :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd (hf.comp measurable_fst))

noncomputable def layerMeasure (μ : Measure E) (f : E → ℝ) : Measure (E × ℝ) :=
  (μ.prod volume).restrict (sourceSubgraph f)

instance layerMeasure_sfinite (μ : Measure E) [SFinite μ] (f : E → ℝ) :
    SFinite (layerMeasure μ f) := inferInstanceAs (SFinite ((μ.prod volume).restrict _))

lemma lintegral_layerMeasure (μ : Measure E) [SFinite μ] {f : E → ℝ}
    (hf : Measurable f) {F : E × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z ∂layerMeasure μ f = ∫⁻ x, ∫⁻ t in Ioo 0 (f x), F (x,t) ∂volume ∂μ := by
  rw [layerMeasure,← lintegral_indicator (measurableSet_sourceSubgraph hf),
    lintegral_prod _ (hF.indicator (measurableSet_sourceSubgraph hf)).aemeasurable]
  apply lintegral_congr
  intro x
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro t
  simp only [indicator,sourceSubgraph,mem_Ioo,mem_ofPred]

lemma lintegral_layerMeasure_fst (μ : Measure E) [SFinite μ] {f : E → ℝ}
    (hf : Measurable f) {F : E → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z.1 ∂layerMeasure μ f = ∫⁻ x, ENNReal.ofReal (f x)*F x ∂μ := by
  rw [lintegral_layerMeasure μ hf (F := fun z => F z.1) (by fun_prop)]
  apply lintegral_congr
  intro x
  simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo,sub_zero,mul_comm]

/-- Newton potentials are kept as nonnegative extended integrals until their
finiteness has separately been supplied by the PDE. -/
noncomputable def potential (μ : Measure E) (k : E × E → ℝ≥0∞) (g : E → ℝ) (x : E) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (g y)*k (x,y) ∂μ

lemma measurable_potential (μ : Measure E) [SFinite μ] {k : E × E → ℝ≥0∞}
    {g : E → ℝ} (hk : Measurable k) (hg : Measurable g) :
    Measurable (potential μ k g) :=
  ((hg.comp measurable_snd).ennreal_ofReal.mul hk).lintegral_prod_right

lemma lintegral_layer_kernel (μ : Measure E) [SFinite μ] {g : E → ℝ}
    {k : E × E → ℝ≥0∞} (hg : Measurable g) (hk : Measurable k) (x : E) :
    ∫⁻ y, k (x,y.1) ∂layerMeasure μ g = potential μ k g x :=
  lintegral_layerMeasure_fst μ hg (hk.comp (measurable_const.prodMk measurable_id))

/-- This is the Tonelli recovery at an arbitrary measurable selected endpoint.
The selected point depends only on the first layer, never on the second layer. -/
lemma lintegral_pair_endpoint (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {a : E × ℝ → ℝ≥0∞} {endpoint : E × ℝ → E}
    (hg : Measurable g) (hk : Measurable k) (ha : Measurable a) (he : Measurable endpoint) :
    ∫⁻ z, a z.1*k (endpoint z.1,z.2.1) ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, a z*potential μ k g (endpoint z) ∂layerMeasure μ f := by
  rw [lintegral_prod (fun z : (E × ℝ) × (E × ℝ) => a z.1*k (endpoint z.1,z.2.1)) (by fun_prop)]
  apply lintegral_congr
  intro z
  change (∫⁻ y : E × ℝ, a z*k (endpoint z,y.1) ∂layerMeasure μ g) = _
  rw [lintegral_const_mul _ (show Measurable (fun y : E × ℝ => k (endpoint z,y.1)) by fun_prop),
    lintegral_layer_kernel μ hg hk]

lemma lintegral_pair_position (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {a : E × ℝ → ℝ≥0∞}
    (hg : Measurable g) (hk : Measurable k) (ha : Measurable a) :
    ∫⁻ z, a z.1*k (z.1.1,z.2.1) ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, a z*potential μ k g z.1 ∂layerMeasure μ f :=
  lintegral_pair_endpoint μ hg hk ha measurable_fst

lemma lintegral_pair_endpoint_average (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {k : E × E → ℝ≥0∞} {a : E × ℝ → ℝ≥0∞} {lo hi : E × ℝ → E}
    (hg : Measurable g) (hk : Measurable k) (ha : Measurable a)
    (hlo : Measurable lo) (hhi : Measurable hi) :
    ∫⁻ z, a z.1*((k (lo z.1,z.2.1)+k (hi z.1,z.2.1))/2)
        ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, a z*((potential μ k g (lo z)+potential μ k g (hi z))/2)
        ∂layerMeasure μ f := by
  simp only [ENNReal.div_eq_inv_mul,mul_add]
  simp_rw [← mul_assoc]
  rw [lintegral_add_left]
  · rw [lintegral_add_left]
    · congr 1
      · exact lintegral_pair_endpoint μ hg hk (ha.mul_const _) hlo
      · exact lintegral_pair_endpoint μ hg hk (ha.mul_const _) hhi
    · exact (ha.mul_const _).mul ((measurable_potential μ hk hg).comp hlo)
  · exact ((ha.comp measurable_fst).mul_const _).mul
      (hk.comp ((hlo.comp measurable_fst).prodMk measurable_snd.fst))

/-- Integrating any spatial nonnegative pair function over the two sets of
levels gives exactly the interaction with both source densities. -/
lemma lintegral_pair_spatial (μ : Measure E) [SFinite μ] {f g : E → ℝ}
    {F : E × E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hF : Measurable F) :
    ∫⁻ z, F (z.1.1,z.2.1) ∂(layerMeasure μ f).prod (layerMeasure μ g) =
      ∫⁻ z, ENNReal.ofReal (f z.1)*ENNReal.ofReal (g z.2)*F z ∂μ.prod μ := by
  calc
    _ = ∫⁻ x : E × ℝ, ∫⁻ y : E × ℝ, F (x.1,y.1) ∂layerMeasure μ g ∂layerMeasure μ f := by
      exact lintegral_prod _ (by fun_prop)
    _ = ∫⁻ x : E × ℝ, ∫⁻ y : E, ENNReal.ofReal (g y)*F (x.1,y) ∂μ ∂layerMeasure μ f := by
      apply lintegral_congr
      intro x
      exact lintegral_layerMeasure_fst μ hg (F := fun y => F (x.1,y)) (by fun_prop)
    _ = ∫⁻ x : E, ENNReal.ofReal (f x)*(∫⁻ y : E, ENNReal.ofReal (g y)*F (x,y) ∂μ) ∂μ := by
      exact lintegral_layerMeasure_fst μ hf
        (F := fun x => ∫⁻ y : E, ENNReal.ofReal (g y)*F (x,y) ∂μ)
        ((show Measurable (fun z : E × E => ENNReal.ofReal (g z.2)*F z) by fun_prop).lintegral_prod_right)
    _ = ∫⁻ z : E × E, ENNReal.ofReal (f z.1)*ENNReal.ofReal (g z.2)*F z ∂μ.prod μ := by
      rw [lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro x
      rw [← lintegral_const_mul _ (show Measurable (fun y => ENNReal.ofReal (g y)*F (x,y)) by fun_prop)]
      apply lintegral_congr
      intro y
      exact (mul_assoc _ _ _).symm

end HenonLaneEmden.LayerTonelli
end Tonelli

end OAI
