import Mathlib
import OAI.Probability.Ballisticity.Renewal.CurvePositiveScale

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience
lemma uniform_lower_mass_from_sequences (P : ℝ → ℝ≥0∞ → Prop)
    (hmono : ∀ r c c', c' ≤ c → P r c → P r c')
    (hseq : ∀ r : ℕ → ℝ, (∀ n, 0 < r n) → Tendsto r atTop atTop →
      ∃ (ns : ℕ → ℕ) (c : ℝ≥0∞), StrictMono ns ∧ 0 < c ∧ c ≤ 1 ∧ ∀ᶠ n in atTop, P (r (ns n)) c) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≤ 1 ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → P r c := by
  by_contra hn
  push Not at hn
  have hx (n : ℕ) : ∃ r : ℝ, (n:ℝ)+1 ≤ r ∧ ¬ P r (ENNReal.ofReal (dyadicCut n)) :=
    hn _ (ENNReal.ofReal_pos.mpr (dyadicCut_pos n)) (ENNReal.ofReal_le_one.mpr (dyadicCut_le_one n))
      ((n:ℝ)+1) (by positivity)
  choose r hre hrP using hx
  have hr : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by positivity) (hre n)
  have hrinf : Tendsto r atTop atTop := tendsto_atTop_mono hre
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).atTop_add tendsto_const_nhds)
  obtain ⟨ns,c,hns,hc,hc1,hgood⟩ := hseq r hr hrinf
  have hcn : Tendsto (fun n => ENNReal.ofReal (dyadicCut (ns n))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (dyadicCut_tendsto.comp hns.tendsto_atTop)
  obtain ⟨n,hn,hsmall⟩ := (hgood.and (hcn.eventually (gt_mem_nhds hc))).exists
  exact hrP (ns n) (hmono _ _ _ hsmall.le hn)
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

theorem clipping_uniform_origin {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {T η ε : ℝ} (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≤ 1 ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∃ θ : ℝ,
      (environmentLaw ν).real {ω | quenchedKernel (ω,0)
        (TubePrefix (realPosition (step e)) f 0 θ (η*r)
          ⌈T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) r⌉₊) < c} < ε := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  let S := commonIncrementProcess ℓ f 0
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ hp
  let P := fun r c => ∃ θ : ℝ, (environmentLaw ν).real {ω | quenchedKernel (ω,0)
    (TubePrefix ℓ f 0 θ (η*r) ⌈T*fluctuationScale μ S r⌉₊) < c} < ε
  apply uniform_lower_mass_from_sequences P
  · intro r c c' hcc' hP
    obtain ⟨θ,hθ⟩ := hP
    refine ⟨θ,lt_of_le_of_lt ?_ hθ⟩
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hω
    exact hω.trans_le hcc'
  · intro r hr hrinf
    obtain ⟨ns,F,F₀,hns,hF,hFb,hF1,hFa,hF₀,hFlim,hFle⟩ := exists_dyadic_variance_profile μ S
      (measurable_commonIncrementProcess ℓ f 0) (independent_commonWordIncrement_nonzero ν hue e f hef htrans) r hr
    have hri : Tendsto (fun n => r (ns n)) atTop atTop := hrinf.comp hns.tendsto_atTop
    by_cases hzero : F₀=0
    · have hFlim0 : Tendsto F atTop (𝓝 0) := hzero ▸ hFlim
      obtain ⟨c,hc,hc1,hh⟩ := clipping_zero_profile ν hue e f hef htrans
        (fun n => r (ns n)) (fun n => hr (ns n)) hri F hFlim0 hF hT hη hε
      exact ⟨ns,c,hns,hc,hc1,hh⟩
    · have hpos : 0 < F₀ := lt_of_le_of_ne hF₀.1 (Ne.symm hzero)
      obtain ⟨c,hc,hc1,hh⟩ := clipping_positive_profile ν hue e f hef htrans
        (fun n => r (ns n)) (fun n => hr (ns n)) hri F hpos hF₀.2 hFle hFlim hF hT hη hε
      exact ⟨ns,c,hns,hc,hc1,hh⟩
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience
lemma quenchedTube_translation {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (θ z : ℝ) (H : ℕ) (ω : Environment d) :
    quenchedKernel (ω,x) (TubePrefix ℓ f x θ z H) =
      quenchedKernel ((fun y => ω (x+y)),0) (TubePrefix ℓ f 0 θ z H) := by
  have hm : Measurable (fun X : Path d => fun n => X n-x) := by fun_prop
  rw [←tubePrefix_translation,←Measure.map_apply hm (measurableSet_tubePrefix ℓ f 0 θ z H)]
  simpa only [add_zero] using congrArg (fun μ : Measure (Path d) => μ (TubePrefix ℓ f 0 θ z H))
    (quenched_translation ω x 0)
lemma quenchedTube_probability_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (x : Lattice d) (θ z : ℝ) (H : ℕ) (c : ℝ≥0∞) :
    (environmentLaw ν).real {ω | quenchedKernel (ω,x) (TubePrefix ℓ f x θ z H) < c} =
      (environmentLaw ν).real {ω | quenchedKernel (ω,0) (TubePrefix ℓ f 0 θ z H) < c} := by
  have hm : Measurable (fun ω : Environment d => quenchedKernel (ω,0) (TubePrefix ℓ f 0 θ z H)) :=
    (Kernel.measurable_coe _ (measurableSet_tubePrefix ℓ f 0 θ z H)).comp (measurable_id.prodMk measurable_const)
  have he := congrArg (fun μ : Measure (Environment d) => μ {ω | quenchedKernel (ω,0) (TubePrefix ℓ f 0 θ z H) < c})
    (environment_translation ν x)
  rw [Measure.map_apply (by fun_prop) (measurableSet_lt hm measurable_const)] at he
  apply congrArg ENNReal.toReal
  convert he using 1
  congr 1
  ext ω
  exact Iff.of_eq (congrArg (fun y : ℝ≥0∞ => y < c) (quenchedTube_translation ℓ f x θ z H ω))
lemma quenchedTube_zero {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (θ : ℝ) {z : ℝ} (hz : 0 ≤ z) (ω : Environment d) :
    quenchedKernel (ω,x) (TubePrefix ℓ f x θ z 0)=1 := by
  apply (measure_congr ?_).trans measure_univ
  filter_upwards [quenched_initial_ae (ω,x)] with X hX
  exact propext (iff_of_true (tubePrefix_zero_of_initial ℓ f x θ z hz X hX) (Set.mem_univ X))

theorem clipping_uniform {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {T η ε : ℝ} (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≤ 1 ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∃ θ : ℝ,
      ∀ (x : Lattice d) (H : ℕ), (H:ℝ) ≤ T*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r →
      (environmentLaw ν).real {ω | quenchedKernel (ω,x)
        (TubePrefix (realPosition (step e)) f x θ (η*r) H) < c} < ε := by
  obtain ⟨c,hc,hc1,R,hR,hh⟩ := clipping_uniform_origin ν hue e f hef htrans hT hη hε
  refine ⟨c,hc,hc1,R,hR,fun r hr => ?_⟩
  obtain ⟨θ,hθ⟩ := hh r hr
  refine ⟨θ,fun x H hH => ?_⟩
  rw [quenchedTube_probability_translation]
  by_cases hH0 : H=0
  · subst H
    have hz : 0 ≤ η*r := mul_nonneg hη.le (hR.le.trans hr)
    simp only [quenchedTube_zero _ _ _ _ hz,not_lt.mpr hc1,Set.ofPred_false,measureReal_empty]
    exact hε
  · apply lt_of_le_of_lt _ hθ
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hω
    exact (quenchedTube_mono_height e f 0 θ (η*r) (Nat.pos_of_ne_zero hH0)
      (by exact_mod_cast hH.trans (Nat.le_ceil _)) ω).trans_lt hω
end DirectionalTransience

end

end

end OAI
