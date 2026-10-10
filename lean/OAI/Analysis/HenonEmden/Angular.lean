import OAI.Analysis.HenonEmden.ShortComponents

namespace OAI

universe uE

section Angular

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal Pointwise
noncomputable section
namespace HenonLaneEmden.Angular
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Polar lower bound contributed by a set of directions whose full radial
segment has source at least `t`. Surface measure here is not normalized. -/
lemma ray_mass_le {f : E → ℝ≥0∞} {S : Set (sphere (0:E) 1)}
    (hS : MeasurableSet S) {l : ℝ} (hl : 0 < l) (t : ℝ≥0∞)
    (h : ∀ e ∈ S, ∀ r ∈ Ioo 0 l, t ≤ f (r • e.1)) :
    t * μ.toSphere S * ENNReal.ofReal (l ^ Module.finrank ℝ E / Module.finrank ℝ E)
      ≤ ∫⁻ z, f z ∂μ := by
  let L : Ioi (0:ℝ) := ⟨l,hl⟩
  let T := S ×ˢ Iio L
  have hm : MeasurableSet T := hS.prod measurableSet_Iio
  rw [Polar.lintegral_polar_prod μ]
  have hb : ∀ z : sphere (0:E) 1 × Ioi (0:ℝ), T.indicator (fun _ => t) z ≤ f (z.2.1 • z.1.1) := by
    intro z
    by_cases hz : z ∈ T
    · rw [indicator_of_mem hz]
      exact h z.1 hz.1 z.2.1 ⟨z.2.2,hz.2⟩
    · simp only [indicator_of_notMem hz,zero_le]
  have he : ∫⁻ z, T.indicator (fun _ => t) z
      ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1)) =
      t * μ.toSphere S * ENNReal.ofReal (l ^ Module.finrank ℝ E / Module.finrank ℝ E) := by
    rw [lintegral_indicator hm,lintegral_const,Measure.restrict_apply_univ,
      Measure.prod_prod,volumeIoiPow_apply_Iio]
    have hn : Module.finrank ℝ E-1+1 = Module.finrank ℝ E :=
      Nat.sub_add_cancel (Module.finrank_pos : 0 < Module.finrank ℝ E)
    have hnr : ((Module.finrank ℝ E-1 : ℕ) : ℝ)+1 = Module.finrank ℝ E := by
      exact_mod_cast hn
    simp only [hn,hnr,L,mul_assoc]
  exact he ▸ lintegral_mono hb

open LineComponents

/-- The long-component alternative on a line uses either forward or backward
rays. In particular it requires no independence of any cap weight and layer. -/
lemma long_component_mass_le {f : E → ℝ≥0∞}
    {U : Set (sphere (0:E) 1 × ℝ)} (hU : IsOpen U)
    {l : ℝ} (hl : 0 < l) (t : ℝ≥0∞)
    (h : ∀ e r, |r| ≤ l/2 → (e,r) ∈ U → t ≤ f (r • e.1)) :
    t * ENNReal.ofReal ((l/2)^Module.finrank ℝ E / Module.finrank ℝ E) *
      μ.toSphere {e | ENNReal.ofReal l < componentLength U e} ≤
      2 * ∫⁻ z, f z ∂μ := by
  let F := {e | ENNReal.ofReal (l/2) < forwardExit U e}
  let G := {e | ENNReal.ofReal (l/2) < backwardExit U e}
  have hF : MeasurableSet F := measurableSet_lt measurable_const (measurable_forwardExit hU)
  have hG : MeasurableSet G := measurableSet_lt measurable_const (measurable_backwardExit hU)
  have hs : {e | ENNReal.ofReal l < componentLength U e} ⊆ F ∪ G := by
    intro e he
    by_contra hn
    have hne : ¬ e ∈ F ∧ ¬ e ∈ G := not_or.mp hn
    have hh : componentLength U e ≤ ENNReal.ofReal l := by
      calc
        componentLength U e ≤ ENNReal.ofReal (l/2) + ENNReal.ofReal (l/2) :=
          add_le_add (le_of_not_gt hne.1) (le_of_not_gt hne.2)
        _ = ENNReal.ofReal l := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    exact (not_lt_of_ge hh) he
  have hforward := ray_mass_le μ hF (half_pos hl) t (f := f) (by
    intro e he r hr
    have hin : SegmentInside U e (l/2) := (lt_forwardExit_iff hU (by positivity)).mp he
    exact h e r (by rw [abs_of_pos hr.1]; exact hr.2.le) (hin r (by rw [uIcc_of_le (by positivity)]; exact ⟨hr.1.le,hr.2.le⟩)))
  have hbackward := ray_mass_le μ hG (half_pos hl) t (f := fun z => f (-z)) (by
    intro e he r hr
    have hin : SegmentInside U e (-(l/2)) := (lt_backwardExit_iff hU (by positivity)).mp he
    have hm := hin (-r) (by rw [uIcc_of_ge (by linarith)]; constructor <;> linarith [hr.1,hr.2])
    simpa only [neg_smul] using h e (-r) (by rw [abs_neg,abs_of_pos hr.1]; exact hr.2.le) hm)
  rw [lintegral_neg_eq_self] at hbackward
  have hmeasure : μ.toSphere {e | ENNReal.ofReal l < componentLength U e} ≤
      μ.toSphere F + μ.toSphere G := (measure_mono hs).trans (measure_union_le F G)
  calc
    _ ≤ t * ENNReal.ofReal ((l/2)^Module.finrank ℝ E / Module.finrank ℝ E) *
          (μ.toSphere F + μ.toSphere G) := by gcongr
    _ = t * μ.toSphere F * ENNReal.ofReal ((l/2)^Module.finrank ℝ E / Module.finrank ℝ E) +
        t * μ.toSphere G * ENNReal.ofReal ((l/2)^Module.finrank ℝ E / Module.finrank ℝ E) := by ring
    _ ≤ (∫⁻ z, f z ∂μ) + ∫⁻ z, f z ∂μ := add_le_add hforward hbackward
    _ = _ := (two_mul _).symm

/-- Translation of the ray estimate to a local source; the only quantitative
input is its mass on the fixed ball `B₄`. -/
lemma long_component_local_mass_le {f : E → ℝ} {x : E} (hx : ‖x‖ ≤ 2)
    {t l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1)
    (hU : IsOpen {z : sphere (0:E) 1 × ℝ | t < f (x + z.2 • z.1.1)}) :
    ENNReal.ofReal t * ENNReal.ofReal ((l/2)^Module.finrank ℝ E / Module.finrank ℝ E) *
      μ.toSphere {e | ENNReal.ofReal l < componentLength
        {z : sphere (0:E) 1 × ℝ | t < f (x + z.2 • z.1.1)} e} ≤
      2 * ∫⁻ z in ball (0:E) 4, ENNReal.ofReal (f z) ∂μ := by
  let F : E → ℝ≥0∞ := (ball (0:E) 4).indicator (fun z => ENNReal.ofReal (f z))
  have hh := long_component_mass_le μ hU hl (ENNReal.ofReal t)
    (f := fun z => F (x+z)) (by
      intro e r hr ht
      have hn : ‖(e:E)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using e.2
      have hb : x+r • (e:E) ∈ ball (0:E) 4 := by
        rw [mem_ball,dist_zero_right]
        have hs := norm_add_le x (r • (e:E))
        rw [norm_smul,Real.norm_eq_abs,hn,mul_one] at hs
        linarith
      change ENNReal.ofReal t ≤ (ball (0:E) 4).indicator (fun z => ENNReal.ofReal (f z)) (x+r • (e:E))
      rw [indicator_of_mem hb]
      exact ENNReal.ofReal_le_ofReal ht.le)
  rwa [lintegral_add_left_eq_self,lintegral_indicator measurableSet_ball] at hh

end HenonLaneEmden.Angular

namespace HenonLaneEmden
/-- With value zero assigned at the origin, the positive source subgraph is
open jointly in spatial location and positive level. -/
lemma isOpen_source_subgraph {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x) (q B : ℝ) :
    IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < source u q B z.1} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hx : z.1 ≠ 0 := by
    intro he
    simpa [he,source_zero] using hz.1.trans hz.2
  have hc : ContinuousAt (source u q B) z.1 :=
    (regular_source hu hup q B).continuousOn.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds hx)
  exact (continuousAt_const.eventually_lt continuousAt_snd hz.1).and
    (continuousAt_snd.eventually_lt (hc.comp continuousAt_fst) hz.2)

lemma isOpen_source_lineLayer {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x) (q B : ℝ)
    (x : Space n) {t : ℝ} (ht : 0 < t) :
    IsOpen {z : sphere (0:Space n) 1 × ℝ | t < source u q B (x + z.2 • z.1.1)} := by
  have hh := (isOpen_source_subgraph hu hup q B).preimage
    (show Continuous (fun z : sphere (0:Space n) 1 × ℝ => (x+z.2 • z.1.1,t)) from
      (continuous_const.add (continuous_snd.smul continuous_fst.subtype_val)).prodMk continuous_const)
  simpa only [Set.mem_ofPred_eq,true_and,ht,Set.preimage_ofPred_eq] using hh

end HenonLaneEmden
end
end Angular

end OAI
