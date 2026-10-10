import OAI.Analysis.LienardCycles.ModelScaling

namespace OAI

universe uP uα

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter Asymptotics
open scoped Topology ContDiff
namespace QuinticLienard.SmallWidth
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma fiber_quotient_tendsto {f : P × ℝ → ℝ} {p₀ : P} {D : (P × ℝ) →L[ℝ] ℝ}
    (hf : HasStrictFDerivAt f D (p₀,(0:ℝ))) {α : Type uα} {l : Filter α}
    {p : α → P} {t : α → ℝ} (hp : Tendsto p l (𝓝 p₀)) (ht : Tendsto t l (𝓝 0))
    (hne : ∀ᶠ z in l, t z≠0) :
    Tendsto (fun z => (f (p z,t z)-f (p z,(0:ℝ)))/t z) l (𝓝 (D (0,1))) := by
  have hmap : Tendsto (fun z => ((p z,t z),(p z,(0:ℝ)))) l (𝓝 ((p₀,(0:ℝ)),(p₀,(0:ℝ)))) :=
    (hp.prodMk_nhds ht).prodMk_nhds (hp.prodMk_nhds tendsto_const_nhds)
  have ho := hf.isLittleO.comp_tendsto hmap
  have he (z : α) : D ((p z,t z)-(p z,(0:ℝ)))=t z*D (0,1) := by
    rw [show (p z,t z)-(p z,(0:ℝ))=t z • (0,1) by ext <;> simp]
    simp only [map_smul,smul_eq_mul]
  have ho' : (fun z => f (p z,t z)-f (p z,(0:ℝ))-t z*D (0,1)) =o[l] t := by
    apply Asymptotics.isLittleO_iff.mpr
    intro c hc
    filter_upwards [ho.bound hc] with z hz
    simp only [Function.comp_apply] at hz
    rw [he z] at hz
    simpa only [Prod.mk_sub_mk,sub_self,sub_zero,
      Prod.norm_def,norm_zero,max_eq_right (norm_nonneg (t z))] using hz
  have hh := ho'.tendsto_div_nhds_zero.add_const (D (0,1))
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [hne] with z hz
  field_simp [hz]
  ring

end QuinticLienard.SmallWidth

end OAI
