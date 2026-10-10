import OAI.MeasureTheory.SelfSimilar.BallIntegrability

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter EntropyRateDimension.Bernoulli
open scoped Topology BigOperators ENNReal
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩

theorem head_point_measurable (S : System ι) :
    Measurable (fun ω : ℕ → ι => (ω 0,point S ω)) :=
  (measurable_pi_apply 0).prodMk (point_measurable S)

theorem head_point_law (S : System ι) :
    (addressMeasure S).map (fun ω => (ω 0,point S ω)) =
      ∑ i, (Measure.dirac i).prod (S.component (law S) i) := by
  classical
  let f : ι × ℝ → ι × ℝ := fun z => (z.1,S.affine z.1 z.2)
  have hf : Measurable f := by
    apply measurable_fst.prodMk
    exact (((measurable_of_finite S.ratio).comp measurable_fst).mul measurable_snd).add
      ((measurable_of_finite S.offset).comp measurable_fst)
  have hh := congrArg (Measure.map f) (head_tail_point_law S)
  have hp : Measurable (fun ω : ℕ → ι => (ω 0,point S (shift ω))) :=
    (measurable_pi_apply 0).prodMk ((point_measurable S).comp shift_measurable)
  rw [Measure.map_map hf hp] at hh
  have he : f ∘ (fun ω => (ω 0,point S (shift ω))) = fun ω => (ω 0,point S ω) := by
    funext ω
    exact Prod.ext rfl (point_shift S ω).symm
  rw [he] at hh
  rw [hh]
  change ((∑ i, ENNReal.ofReal (S.weight i) • Measure.dirac i).prod (law S)).map f = _
  rw [← Measure.sum_fintype,Measure.prod_sum_left,Measure.sum_fintype,
    Measure.map_finset_sum hf.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.prod_smul_left,Measure.map_smul _ hf.aemeasurable,Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left,System.component,Measure.prod_smul_right,
    Measure.dirac_prod,Measure.map_map measurable_prodMk_left (S.affine_continuous i).measurable]
  rfl

theorem ae_head_point (S : System ι) {P : ι → ℝ → Prop}
    (hP : ∀ i, ∀ᵐ x ∂S.component (law S) i, P i x) :
    ∀ᵐ ω ∂addressMeasure S, P (ω 0) (point S ω) := by
  have hh : ∀ᵐ z ∂(addressMeasure S).map (fun ω => (ω 0,point S ω)), P z.1 z.2 := by
    rw [head_point_law,ae_finsetSum_measure_iff]
    intro i _
    rw [Measure.dirac_prod,(measurableEmbedding_prodMk_left i).ae_map_iff]
    exact hP i
  exact ae_of_ae_map (head_point_measurable S).aemeasurable hh

theorem integrable_head_point (S : System ι) {f : ι → ℝ → ℝ}
    (hfm : ∀ i, Measurable (f i)) (hf : ∀ i, Integrable (f i) (S.component (law S) i)) :
    Integrable (fun ω => f (ω 0) (point S ω)) (addressMeasure S) := by
  have hm : Measurable (fun z : ι × ℝ => f z.1 z.2) :=
    measurable_from_prod_countable_right hfm
  have hi : Integrable (fun z : ι × ℝ => f z.1 z.2)
      ((addressMeasure S).map (fun ω => (ω 0,point S ω))) := by
    rw [head_point_law,integrable_finsetSum_measure]
    intro i _
    rw [Measure.dirac_prod,integrable_map_measure hm.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable]
    exact hf i
  exact hi.comp_measurable (head_point_measurable S)

noncomputable def envelope (S : System ι) (ω : ℕ → ι) : ℝ :=
  BallRatios.logEnvelope (law S) (S.component (law S) (ω 0)) (point S ω)

theorem envelope_joint_measurable (S : System ι) : Measurable (fun z : ι × ℝ =>
    BallRatios.logEnvelope (law S) (S.component (law S) z.1) z.2) := by
  apply measurable_from_prod_countable_right
  intro i
  exact BallRatios.logEnvelope_measurable (law S) (S.component (law S) i)

theorem envelope_measurable (S : System ι) : Measurable (envelope S) := by
  unfold envelope
  have hh := (envelope_joint_measurable S).comp (head_point_measurable S)
  exact hh

omit [Nonempty ι] in
theorem envelope_nonneg (S : System ι) (ω : ℕ → ι) : 0 ≤ envelope S ω :=
  BallRatios.logEnvelope_nonneg _ _ _

theorem envelope_integrable (S : System ι) : Integrable (envelope S) (addressMeasure S) :=
  integrable_head_point S (fun i => BallRatios.logEnvelope_measurable _ (S.component (law S) i))
    (fun i => BallRatios.logEnvelope_integrable _ (S.component (law S) i))

noncomputable def corr (S : System ι) (n : ℕ) (ω : ℕ → ι) : ℝ :=
  BallRatios.logRatio (law S) (S.component (law S) (ω 0)) (point S ω) |slope S ω n|

noncomputable def corrLimit (S : System ι) (ω : ℕ → ι) : ℝ :=
  Real.log ((law S).rnDeriv (S.component (law S) (ω 0)) (point S ω)).toReal

theorem corr_joint_measurable (S : System ι) : Measurable (fun z : ι × (ℝ × ℝ) =>
    BallRatios.logRatio (law S) (S.component (law S) z.1) z.2.1 z.2.2) := by
  apply measurable_from_prod_countable_right
  intro i
  exact BallRatios.logRatio_measurable (law S) (S.component (law S) i)

theorem corr_measurable (S : System ι) (n : ℕ) : Measurable (corr S n) := by
  unfold corr
  have hh := (corr_joint_measurable S).comp ((measurable_pi_apply 0).prodMk
    ((point_measurable S).prodMk (slope_measurable S n).abs))
  exact hh

theorem corrLimit_measurable (S : System ι) : Measurable (corrLimit S) := by
  have hm : Measurable (fun z : ι × ℝ =>
      Real.log ((law S).rnDeriv (S.component (law S) z.1) z.2).toReal) := by
    apply measurable_from_prod_countable_right
    intro i
    exact ((law S).measurable_rnDeriv (S.component (law S) i)).ennreal_toReal.log
  exact hm.comp (head_point_measurable S)

theorem ae_corr_bounds (S : System ι) : ∀ᵐ ω ∂addressMeasure S, ∀ n : ℕ, 0 < n →
    0 ≤ corr S n ω ∧ corr S n ω ≤ envelope S ω := by
  filter_upwards [ae_head_point S (fun i => BallRatios.logRatio_bounds _ _
    (S.component_le _ (law_selfSimilar S) i))] with ω hω
  intro n hn
  exact hω _ (abs_slope_pos S ω n) (abs_slope_lt_one S ω hn)

theorem ae_corr_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => corr S n ω) atTop (𝓝 (corrLimit S ω)) := by
  filter_upwards [ae_head_point S (fun i => BallRatios.ae_logRatio_limit _ _
    (S.component_le _ (law_selfSimilar S) i))] with ω hω
  apply hω.2.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨slope_tendsto_zero S ω,
    Eventually.of_forall (abs_slope_pos S ω)⟩

end EntropyRateDimension.Coding

end

end OAI
