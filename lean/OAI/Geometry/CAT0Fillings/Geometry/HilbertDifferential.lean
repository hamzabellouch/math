import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.HilbertCharts

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory
open scoped RealInnerProductSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
theorem exists_bilinForm_of_seminorm_parallelogram (p : Seminorm ℝ E)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) :
    ∃ B : LinearMap.BilinForm ℝ E, B.IsSymm ∧
      (∀ v, B v v = (p v)^2) ∧
      ∀ u v, B u v = ((p (u+v))^2-(p (u-v))^2)/4 := by
  let : SeminormedAddCommGroup E := p.toAddGroupSeminorm.toSeminormedAddCommGroup
  let : NormedSpace ℝ E := { norm_smul_le := fun a v => le_of_eq (map_smul_eq_mul p a v) }
  let Q := SeparationQuotient E
  let f : E →ₗ[ℝ] Q := (SeparationQuotient.mkCLM ℝ E).toLinearMap
  have hf (v : E) : ‖f v‖ = p v := rfl
  have hpQ : ∀ u v : Q,
      ‖u+v‖*‖u+v‖+‖u-v‖*‖u-v‖ = 2*(‖u‖*‖u‖+‖v‖*‖v‖) := by
    intro u v
    obtain ⟨x,rfl⟩ := SeparationQuotient.surjective_mk u
    obtain ⟨y,rfl⟩ := SeparationQuotient.surjective_mk v
    change ‖f x+f y‖*‖f x+f y‖+‖f x-f y‖*‖f x-f y‖ =
      2*(‖f x‖*‖f x‖+‖f y‖*‖f y‖)
    rw [←map_add,←map_sub,hf,hf,hf,hf]
    nlinarith [hpara x y]
  let : InnerProductSpace ℝ Q := InnerProductSpace.ofNorm ℝ hpQ
  let B : LinearMap.BilinForm ℝ E := (innerₗ Q).compl₁₂ f f
  refine ⟨B,?_,?_,?_⟩
  · exact ⟨fun u v => (real_inner_comm (f u) (f v)).symm⟩
  · intro v
    change inner ℝ (f v) (f v) = (p v)^2
    rw [real_inner_self_eq_norm_sq,hf]
  · intro u v
    change inner ℝ (f u) (f v) = _
    have H := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℝ) (f u) (f v)
    change inner ℝ (f u) (f v) = (‖f u+f v‖*‖f u+f v‖-‖f u-f v‖*‖f u-f v‖)/4 at H
    rw [←map_add,←map_sub,hf,hf] at H
    simpa only [pow_two] using H

end CAT0Fillings
namespace CAT0Fillings.MetricDifferentiation
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X]

theorem exists_hilbertian_lipschitz_differential
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ (∞ : ℝ≥0∞)) {f : s → X} {K : ℝ≥0}
    (hf : LipschitzWith K f)
    (hQ : ∀ a b c d : s,
      dist (f a) (f c)^2+dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2+dist (f b) (f c)^2+dist (f c) (f d)^2+dist (f d) (f a)^2) :
    ∃ p : E → Seminorm ℝ E,
      (∀ v, Measurable (fun x => p x v)) ∧
      (∀ x, LipschitzWith K (p x)) ∧
      ∀ᵐ x ∂μ.restrict s, (∀ hx : x ∈ s,
        HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩) ∧
        (∀ u v, p x (u+v)^2+p x (u-v)^2 = 2*p x u^2+2*p x v^2) := by
  classical
  let Y := Set.range f
  let : SeparableSpace Y := (isSeparable_range hf.continuous).separableSpace
  let F : s → Y := fun x => ⟨f x,x,rfl⟩
  let e := kuratowskiEmbedding Y
  have he : Isometry e := kuratowskiEmbedding.isometry Y
  let F₀ : E → ↥(lp (fun _ : ℕ => ℝ) (⊤ : ENNReal)) :=
    fun x => if hx : x ∈ s then e (F ⟨x,hx⟩) else 0
  have hF₀ : LipschitzOnWith K F₀ s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    dsimp only [F₀]
    rw [dite_eq_left hx,dite_eq_left hy,he.dist_eq]
    exact hf.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨g,hg,heq⟩ := hF₀.extend_lp_infty
  let Z := Set.range g
  let : SeparableSpace Z := (isSeparable_range hg.continuous).separableSpace
  let : Nonempty Z := ⟨⟨g 0,0,rfl⟩⟩
  let G : E → Z := fun x => ⟨g x,x,rfl⟩
  have hG : LipschitzWith K G := by
    apply LipschitzWith.of_dist_le_mul
    exact hg.dist_le_mul
  have hdist (y z : s) : dist (G y) (G z) = dist (f y) (f z) := by
    change dist (g y) (g z) = _
    rw [←heq y.property, ←heq z.property]
    dsimp only [F₀]
    rw [dite_eq_left y.property,dite_eq_left z.property]
    exact he.dist_eq (F y) (F z)
  have hQG : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (G a) (G c)^2+dist (G b) (G d)^2 ≤
        dist (G a) (G b)^2+dist (G b) (G c)^2+dist (G c) (G d)^2+dist (G d) (G a)^2 := by
    intro a ha b hb c hc d hd
    simpa only [← hdist] using hQ ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ ⟨d,hd⟩
  refine ⟨metricSeminorm G,fun v => measurable_metricSeminorm_apply hG v,
    fun x => metricSeminorm_lipschitz hG x,?_⟩
  have hdiff := (ae_hasCenteredMetricDifferential μ hG).filter_mono
    (ae_mono (Measure.restrict_le_self (μ := μ) (s := s)))
  filter_upwards [hdiff, ae_metricSeminorm_parallelogram_on μ hG hs hsf hQG] with x hdx hpx
  refine ⟨?_,hpx⟩
  intro hx
  have hc : Tendsto (fun y : s => (y : E)) (𝓝 (⟨x,hx⟩ : s)) (𝓝 x) :=
    continuous_subtype_val.tendsto _
  have hr := hdx.comp_tendsto hc
  change (fun y : s => dist (G (y : E)) (G ((⟨x,hx⟩ : s) : E)) -
    metricSeminorm G x ((y : E)-x)) =o[𝓝 (⟨x,hx⟩ : s)] (fun y : s => (y : E)-x) at hr
  have hdist' (y : s) : dist (G (y : E)) (G x) = dist (f y) (f ⟨x,hx⟩) := hdist y ⟨x,hx⟩
  simpa only [HasCenteredMetricDifferentialWithin,hdist'] using hr
end CAT0Fillings.MetricDifferentiation
end
end

end OAI
