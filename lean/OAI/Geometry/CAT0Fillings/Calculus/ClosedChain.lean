import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.Multiplier
import OAI.Geometry.CAT0Fillings.Sobolev.Constant

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma atlas_preserving : MeasurePreserving q.atlasParam q.atlasMeasure
    (MassMeasure.currentMassMeasure hT) := ⟨q.measurable_atlasParam,q.map_atlasMeasure⟩

noncomputable def composeValue {F : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (f : Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) : Lp ℝ 2 (MassMeasure.currentMassMeasure hT) :=
  (hF.sub (LipschitzWith.const (F 0))).compLp (by simp) f + q.inclusion (q.constant (F 0))

lemma composeValue_ae {F : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (f : Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) :
    q.composeValue hF f =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => F (f x)) := by
  filter_upwards [Lp.coeFn_add ((hF.sub (LipschitzWith.const (F 0))).compLp (by simp) f)
    (value (hT := hT) (LipschitzWith.const (F 0))),
    (hF.sub (LipschitzWith.const (F 0))).coeFn_compLp (by simp) f,
    ((Foundations.boundedLip_of_lipschitz (LipschitzWith.const (F 0))).memLp
      (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp] with x ha hb hc
  rw [composeValue,constant,q.inclusion_lipSobolev,ha]
  change ((hF.sub (LipschitzWith.const (F 0))).compLp (by simp) f) x + (value (hT := hT) (LipschitzWith.const (F 0))) x = _
  change (value (hT := hT) (LipschitzWith.const (F 0))) x = F 0 at hc
  rw [hb,hc]
  simp only [Function.comp_apply,sub_add_cancel]

lemma continuous_composeValue {F : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F) :
    Continuous (q.composeValue hF) :=
  ((hF.sub (LipschitzWith.const (F 0))).continuous_compLp (by simp)).add continuous_const

lemma composeValue_value {F : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.composeValue hF (value hu) = value (hF.comp hu) := by
  apply Lp.ext
  filter_upwards [q.composeValue_ae hF (value hu),
    ((Foundations.boundedLip_of_lipschitz hu).memLp (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp,
    ((Foundations.boundedLip_of_lipschitz (hF.comp hu)).memLp
      (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp] with x ha hb hc
  exact ha.trans ((congrArg F hb).trans hc.symm)

lemma closed_chain {F F' : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hdF : ∀ t, HasDerivAt F (F' t) t) (hcF : Continuous F')
    {C : ℝ} (hC : 0 ≤ C) (hbF : ∀ t, |F' t| ≤ C) (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F ((q.inclusion P) x)) ∧
      (q.closedGradient Q : (ℕ × Euc (k+1)) → Euc (k+1)) =ᵐ[q.atlasMeasure]
        (fun w => F' ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w) := by
  obtain ⟨u,K,hu,hl⟩ := q.exists_lipschitz_approximants P
  have hv := (q.valueProjection.continuous.tendsto (P : q.GraphAmbient)).comp hl
  have hg := (q.gradientProjection.continuous.tendsto (P : q.GraphAmbient)).comp hl
  change Tendsto (fun j => value (hu j)) atTop (𝓝 (q.inclusion P)) at hv
  change Tendsto (fun j => q.gradient (hu j)) atTop (𝓝 (q.closedGradient P)) at hg
  obtain ⟨s,hs,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hnames : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, ∀ j,
      (value (hT := hT) (hu (s j))) x = u (s j) x := by
    apply ae_all_iff.mpr
    intro j
    exact ((Foundations.boundedLip_of_lipschitz (hu (s j))).memLp 2).coeFn_toLp
  have hae' : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT,
      Tendsto (fun j => u (s j) x) atTop (𝓝 ((q.inclusion P) x)) := by
    filter_upwards [hae,hnames] with x hx he
    simpa only [he] using hx
  let b (j : ℕ) (w : ℕ × Euc (k+1)) := F' (u (s j) (q.atlasParam w))
  let c (w : ℕ × Euc (k+1)) := F' ((q.inclusion P) (q.atlasParam w))
  have hb (j : ℕ) : AEStronglyMeasurable (b j) q.atlasMeasure :=
    (hcF.measurable.comp ((hu (s j)).continuous.measurable.comp q.measurable_atlasParam)).aestronglyMeasurable
  have hc : AEStronglyMeasurable c q.atlasMeasure :=
    hcF.comp_aestronglyMeasurable ((Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving)
  have hbC (j : ℕ) : ∀ᵐ w ∂q.atlasMeasure, |b j w| ≤ C := Eventually.of_forall fun w => hbF _
  have hcC : ∀ᵐ w ∂q.atlasMeasure, |c w| ≤ C := Eventually.of_forall fun w => hbF _
  have hbc : ∀ᵐ w ∂q.atlasMeasure, Tendsto (fun j => b j w) atTop (𝓝 (c w)) := by
    have ha : ∀ᵐ w ∂q.atlasMeasure,
        Tendsto (fun j => u (s j) (q.atlasParam w)) atTop (𝓝 ((q.inclusion P) (q.atlasParam w))) := by
      apply ae_of_ae_map (μ := q.atlasMeasure) (p := fun x =>
        Tendsto (fun j => u (s j) x) atTop (𝓝 ((q.inclusion P) x))) q.measurable_atlasParam.aemeasurable
      rwa [q.map_atlasMeasure]
    filter_upwards [ha] with w hw
    exact (hcF.tendsto _).comp hw
  have hgl := ClosedCalculus.mulLp_tendsto hb hc hC hbC hcC hbc (hg.comp hs.tendsto_atTop)
  have he (j : ℕ) : ClosedCalculus.mulLp (hb j) (hbC j) (q.gradient (hu (s j))) =
      q.gradient (hF.comp (hu (s j))) := by
    apply Lp.ext
    exact (ClosedCalculus.mulLp_ae (hb j) (hbC j) _).trans (q.gradient_chain_ae (hu (s j)) hF hdF).symm
  simp only [Function.comp_apply,he] at hgl
  have hvl := (q.continuous_composeValue hF).tendsto (q.inclusion P) |>.comp (hv.comp hs.tendsto_atTop)
  simp only [Function.comp_def,q.composeValue_value] at hvl
  obtain ⟨Q,hQ,hG⟩ := q.closedGradient_closed (q.composeValue hF (q.inclusion P))
    (ClosedCalculus.mulLp hc hcC (q.closedGradient P))
    (fun j => q.lipSobolev (hF.comp (hu (s j)))) hvl hgl
  refine ⟨Q,?_,?_⟩
  · rw [hQ]
    exact q.composeValue_ae hF (q.inclusion P)
  · rw [hG]
    exact ClosedCalculus.mulLp_ae hc hcC _

end CAT0Fillings.ChartGeometry
end

end OAI
