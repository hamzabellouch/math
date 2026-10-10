import Mathlib
import OAI.Probability.Ballisticity.Estimates.CommonWidthProcess
import OAI.Probability.Ballisticity.Estimates.TightIidDifferenceTranslations
import OAI.Probability.Ballisticity.Walk.PathPointMean

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def GridLinear (q : ℝ) (f : C(unitInterval,ℝ)) : Prop :=
  ∀ (j : ℕ) (u v t : unitInterval), q*(u:ℝ) = j → q*(v:ℝ) = j+1 →
    (u:ℝ) ≤ t → (t:ℝ) ≤ v →
    f t = (1-(q*(t:ℝ)-j))*f u+(q*(t:ℝ)-j)*f v

lemma isClosed_gridLinear (q : ℝ) : IsClosed {f : C(unitInterval,ℝ) | GridLinear q f} := by
  simp only [GridLinear,Set.ofPred_forall]
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro u
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro t
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  exact isClosed_eq (continuous_eval_const t) (by fun_prop)

noncomputable def pathRestrictScale (a : unitInterval) : C(unitInterval,ℝ) →L[ℝ] C(unitInterval,ℝ) :=
  ContinuousMap.compCLM ℝ ℝ ⟨fun t => a*t,by fun_prop⟩

lemma pathRestrictScale_apply (a t : unitInterval) (f : C(unitInterval,ℝ)) :
    pathRestrictScale a f t = f (a*t) := rfl

lemma gridLinear_uniform_on_shorter (q : ℕ → ℝ) (hq : Tendsto q atTop atTop)
    (f : ℕ → C(unitInterval,ℝ)) (hf : ∀ n, GridLinear (q n) (f n))
    (m : C(unitInterval,ℝ))
    (hgrid : ∀ ε > 0, ∀ᶠ n in atTop, ∀ (j : ℕ) (u : unitInterval),
      q n*(u:ℝ) = j → |f n u-m u| < ε)
    (a : unitInterval) (ha : (a:ℝ) < 1) :
    Tendsto (fun n => pathRestrictScale a (f n)) atTop (𝓝 (pathRestrictScale a m)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous m.continuous)
    (ε/4) (by linarith)
  have he := hgrid (ε/4) (by linarith)
  have hbig := hq.eventually (eventually_gt_atTop (max (1/δ) (1/(1-(a:ℝ)))))
  rw [eventually_atTop] at he hbig
  obtain ⟨N,hN⟩ := he
  obtain ⟨M,hM⟩ := hbig
  refine ⟨max N M,fun n hn => ?_⟩
  have hqδ := lt_of_le_of_lt (le_max_left _ _) (hM n (le_trans (le_max_right _ _) hn))
  have hqa := lt_of_le_of_lt (le_max_right _ _) (hM n (le_trans (le_max_right _ _) hn))
  have hqpos : 0 < q n := lt_trans (one_div_pos.mpr hδ) hqδ
  have hqinvδ : 1/q n < δ := (one_div_lt hqpos hδ).mpr hqδ
  have hqinva : 1/q n < 1-(a:ℝ) := (one_div_lt hqpos (sub_pos.mpr ha)).mpr hqa
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ?_ (half_lt_self hε)
  apply (ContinuousMap.norm_le_of_nonempty _).2
  intro t
  let z : unitInterval := a*t
  let j := ⌊q n*(z:ℝ)⌋₊
  have hz : 0 ≤ q n*(z:ℝ) := mul_nonneg hqpos.le z.2.1
  have hj : (j:ℝ) ≤ q n*(z:ℝ) := Nat.floor_le hz
  have hj' : q n*(z:ℝ) < (j:ℝ)+1 := Nat.lt_floor_add_one _
  have hza : (z:ℝ) ≤ (a:ℝ) := mul_le_of_le_one_right a.2.1 t.2.2
  have hu0 : 0 ≤ (j:ℝ)/q n := div_nonneg (Nat.cast_nonneg _) hqpos.le
  have hu1 : (j:ℝ)/q n ≤ (z:ℝ) := (div_le_iff₀ hqpos).2 (by simpa [mul_comm] using hj)
  have hv0 : 0 ≤ ((j:ℝ)+1)/q n := div_nonneg (by positivity) hqpos.le
  have hv1 : ((j:ℝ)+1)/q n ≤ 1 := by
    rw [add_div]
    linarith
  let u : unitInterval := ⟨(j:ℝ)/q n,hu0,hu1.trans z.2.2⟩
  let v : unitInterval := ⟨((j:ℝ)+1)/q n,hv0,hv1⟩
  have hqu : q n*(u:ℝ) = j := by dsimp [u]; field_simp
  have hqv : q n*(v:ℝ) = j+1 := by dsimp [v]; field_simp
  have hzv : (z:ℝ) ≤ v := (le_div_iff₀ hqpos).2 (by nlinarith)
  have hdu : dist u z < δ := by
    rw [Subtype.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hu1)]
    have hh : (z:ℝ)-(u:ℝ) < 1/q n := by
      apply (lt_div_iff₀ hqpos).2
      dsimp only [u]
      field_simp
      nlinarith
    linarith
  have hdv : dist v z < δ := by
    rw [Subtype.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hzv)]
    have hh : (v:ℝ)-(z:ℝ) ≤ 1/q n := by
      apply (le_div_iff₀ hqpos).2
      dsimp only [v]
      field_simp
      nlinarith
    linarith
  have hmu := hmod hdu
  have hmv := hmod hdv
  rw [Real.dist_eq] at hmu hmv
  have hgu := hN n (le_trans (le_max_left _ _) hn) j u hqu
  have hgv := hN n (le_trans (le_max_left _ _) hn) (j+1) v (by simpa using hqv)
  have heu : |f n u-m z| ≤ ε/2 := by
    calc _ ≤ |f n u-m u|+|m u-m z| := by simpa only [sub_add_sub_cancel] using abs_add_le (f n u-m u) (m u-m z)
      _ ≤ ε/2 := by linarith
  have hev : |f n v-m z| ≤ ε/2 := by
    calc _ ≤ |f n v-m v|+|m v-m z| := by simpa only [sub_add_sub_cancel] using abs_add_le (f n v-m v) (m v-m z)
      _ ≤ ε/2 := by linarith
  have hb := abs_convex_sub_le (q := q n*(z:ℝ)-j) (by linarith) (by linarith) heu hev
  rw [← hf n j u v z hqu hqv hu1 hzv] at hb
  simpa only [ContinuousMap.sub_apply,pathRestrictScale_apply,Real.norm_eq_abs] using hb

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma weak_sub_const_tendsto {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (hμ : Tendsto μ atTop (𝓝 ν)) {c : ℕ → E} {b : E} (hc : Tendsto c atTop (𝓝 b)) :
    Tendsto (fun n => (μ n).map (fun point => point-c n))
      atTop (𝓝 (ν.map (fun point => point-b))) := by
  have he : Continuous (fun p : E × E => p.1-p.2) := continuous_fst.sub continuous_snd
  have hh := (ProbabilityMeasure.continuous_map he).tendsto
    (ν.prod (diracProba b)) |>.comp
    (ProbabilityMeasure.continuous_prod.tendsto (ν,diracProba b) |>.comp
      (hμ.prodMk_nhds (continuous_diracProba.tendsto b |>.comp hc)))
  have hid (V : ProbabilityMeasure E) (u : E) :
      (V.prod (diracProba u)).map (fun pair => pair.1-pair.2) =
        V.map (fun point => point-u) := by
    apply Subtype.ext
    change ((V : Measure E).prod (Measure.dirac u)).map _ = _
    rw [Measure.prod_dirac,Measure.map_map he.measurable (by fun_prop)]
    rfl
  change Tendsto (fun n => ((μ n).prod (diracProba (c n))).map (fun pair => pair.1-pair.2))
    atTop (𝓝 ((ν.prod (diracProba b)).map (fun pair => pair.1-pair.2))) at hh
  simpa only [hid] using hh

lemma weak_sequence_tight {E : Type*} [MetricSpace E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (hμ : Tendsto μ atTop (𝓝 ν)) :
    IsTightMeasureSet (Set.range (fun n => (μ n : Measure E))) := by
  have hc : IsCompact (closure (Set.range μ)) :=
    hμ.isCompact_insert_range.closure_of_subset (Set.subset_insert _ _)
  have h := isTightMeasureSet_of_isCompact_closure hc
  convert h using 1
  ext x
  simp

lemma GridLinear.sub {q : ℝ} {f g : C(unitInterval,ℝ)}
    (hf : GridLinear q f) (hg : GridLinear q g) : GridLinear q (f-g) := by
  intro j u v t hu hv htu htv
  simp only [ContinuousMap.sub_apply,hf j u v t hu hv htu htv,hg j u v t hu hv htu htv]
  ring

theorem path_grid_median_limit_from_iid_difference
    (μ : ℕ → ProbabilityMeasure C(unitInterval,ℝ)) (W : ProbabilityMeasure C(unitInterval,ℝ))
    (T : ℝ) (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw T I)
    (hd : Tendsto (fun n => ((μ n).prod (μ n)).map
      (fun pair => pair.1-pair.2)) atTop (𝓝 W))
    (q : ℕ → ℝ) (hq : Tendsto q atTop atTop)
    (hμ : ∀ n, ∀ᵐ f ∂(μ n : Measure C(unitInterval,ℝ)), GridLinear (q n) f)
    (b : ℕ → C(unitInterval,ℝ)) (hbl : ∀ n, GridLinear (q n) (b n))
    (hb : ∀ n (j : ℕ) (t : unitInterval), q n*(t:ℝ) = j →
      (1/2 : ℝ≥0∞) ≤ ((μ n : Measure C(unitInterval,ℝ)).map (fun g => g t)) (Set.Iic (b n t)) ∧
      (1/2 : ℝ≥0∞) ≤ ((μ n : Measure C(unitInterval,ℝ)).map (fun g => g t)) (Set.Ici (b n t)))
    (s : ℝ) (hs : s^2 = 1/2) (a : unitInterval) (ha : (a:ℝ) < 1) :
    Tendsto (fun n => (μ n).map (fun path => pathRestrictScale a (path-b n))) atTop
      (𝓝 (W.map (fun path => s • pathRestrictScale a path))) := by
  have ht := weak_sequence_tight hd
  obtain ⟨c,hc,htc⟩ := tight_iid_difference_translations_support
    (fun n => (μ n : Measure C(unitInterval,ℝ))) (fun n => {f | GridLinear (q n) f}) hμ ht
  let V : ℕ → ProbabilityMeasure C(unitInterval,ℝ) := fun n =>
    (μ n).map (fun path => path-c n)
  have hcpt : IsCompact (closure (Set.range V)) := isCompact_closure_of_isTightMeasureSet (S := Set.range V) (by
    have he : {M : Measure C(unitInterval,ℝ) | ∃ Q ∈ Set.range V, (Q : Measure C(unitInterval,ℝ)) = M} =
        Set.range (fun i => (μ i : Measure C(unitInterval,ℝ)).map (fun x => x-c i)) := by
      ext M
      constructor
      · rintro ⟨Q,⟨i,rfl⟩,rfl⟩
        exact ⟨i,rfl⟩
      · rintro ⟨i,rfl⟩
        exact ⟨V i,⟨i,rfl⟩,rfl⟩
    rw [he]
    exact htc)
  apply Filter.tendsto_of_subseq_tendsto
  intro k hk
  obtain ⟨G,_,l,hl,hG⟩ := hcpt.tendsto_subseq (fun j => subset_closure (Set.mem_range_self (k j)))
  let n := k ∘ l
  have hn : Tendsto n atTop atTop := hk.comp hl.tendsto_atTop
  have hdG : ((G : Measure C(unitInterval,ℝ)).prod G).map
      (fun p : C(unitInterval,ℝ) × C(unitInterval,ℝ) => p.1-p.2) = W := by
    have h := weak_iid_difference_tendsto hG
    have he (i : ℕ) : ((V (n i)).prod (V (n i))).map
        (fun pair => pair.1-pair.2) =
        ((μ (n i)).prod (μ (n i))).map (fun pair => pair.1-pair.2) := by
      apply Subtype.ext
      exact iid_diff_translation (μ (n i)) (c (n i))
    change Tendsto (fun i => ((V (n i)).prod (V (n i))).map
      (fun pair => pair.1-pair.2)) atTop _ at h
    simp only [he] at h
    exact congrArg (fun Q : ProbabilityMeasure C(unitInterval,ℝ) => (Q : Measure C(unitInterval,ℝ)))
      (tendsto_nhds_unique h (hd.comp hn))
  obtain ⟨m,hm,hcenter⟩ := path_iid_difference_centered G W T hW hdG s hs
  have hg := path_of_iid_difference_gaussian G W T hW hdG
  have hmed : ∀ ε > 0, ∀ᶠ i in atTop, ∀ (j : ℕ) (t : unitInterval),
      q (n i)*(t:ℝ) = j → |(b (n i)-c (n i)) t-m t| < ε := by
    intro ε hε
    have h := weak_path_grid_medians_uniform hG (pathPointMean G) _
      (path_marginal_eq_gaussian G hg) (fun i => {t | ∃ j : ℕ, q (n i)*(t:ℝ) = j})
      (fun i t => (b (n i)-c (n i)) t) ?_ hε
    · filter_upwards [h] with i hi j t ht
      simpa only [hm t] using hi t ⟨j,ht⟩
    · intro i t ht
      obtain ⟨j,hjt⟩ := ht
      have hbt := hb (n i) j t hjt
      change (1/2 : ℝ≥0∞) ≤ ((V (n i) : Measure C(unitInterval,ℝ)).map (fun g => g t)) _ ∧
        (1/2 : ℝ≥0∞) ≤ ((V (n i) : Measure C(unitInterval,ℝ)).map (fun g => g t)) _
      change (1/2 : ℝ≥0∞) ≤ (((μ (n i) : Measure C(unitInterval,ℝ)).map (fun g => g-c (n i))).map (fun g => g t)) _ ∧
        (1/2 : ℝ≥0∞) ≤ (((μ (n i) : Measure C(unitInterval,ℝ)).map (fun g => g-c (n i))).map (fun g => g t)) _
      rw [Measure.map_map (continuous_eval_const t).measurable (by fun_prop)]
      rw [Measure.map_apply (by fun_prop) measurableSet_Iic,Measure.map_apply (by fun_prop) measurableSet_Ici]
      rw [Measure.map_apply (continuous_eval_const t).measurable measurableSet_Iic,
        Measure.map_apply (continuous_eval_const t).measurable measurableSet_Ici] at hbt
      simpa only [Function.comp_def,Set.preimage,Set.mem_Iic,Set.mem_Ici,
        ContinuousMap.sub_apply,sub_le_sub_iff_right] using hbt
  have hmconv := gridLinear_uniform_on_shorter (q ∘ n) (hq.comp hn)
    (fun i => b (n i)-c (n i)) (fun i => (hbl _).sub (hc _)) m hmed a ha
  have hVres := (ProbabilityMeasure.continuous_map (pathRestrictScale a).continuous).tendsto G |>.comp hG
  have hcconv := weak_sub_const_tendsto hVres hmconv
  refine ⟨l,?_⟩
  have he (i : ℕ) : ((V (n i)).map (pathRestrictScale a)).map
      (fun path => path-pathRestrictScale a (b (n i)-c (n i))) =
      (μ (n i)).map (fun path => pathRestrictScale a (path-b (n i))) := by
    apply Subtype.ext
    change (((μ (n i) : Measure C(unitInterval,ℝ)).map _).map _).map _ = _
    rw [Measure.map_map (by fun_prop) (pathRestrictScale a).measurable,
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext f
    simp only [Function.comp_apply,← map_sub]
    congr 1
    abel
  have heG : (G.map (pathRestrictScale a)).map
      (fun path => path-pathRestrictScale a m) =
      W.map (fun path => s • pathRestrictScale a path) := by
    apply Subtype.ext
    change ((G : Measure C(unitInterval,ℝ)).map (pathRestrictScale a)).map
      (fun f => f-pathRestrictScale a m) =
        (W : Measure C(unitInterval,ℝ)).map (fun g => s • pathRestrictScale a g)
    rw [Measure.map_map (by fun_prop) (pathRestrictScale a).measurable]
    have hh := congrArg (fun M : Measure C(unitInterval,ℝ) => M.map (pathRestrictScale a)) hcenter
    rw [Measure.map_map (pathRestrictScale a).measurable (by fun_prop),
      Measure.map_map (pathRestrictScale a).measurable (by fun_prop)] at hh
    simpa only [Function.comp_def,map_sub,map_smul] using hh
  change Tendsto (fun i => ((V (n i)).map (pathRestrictScale a)).map _)
    atTop (𝓝 ((G.map (pathRestrictScale a)).map _)) at hcconv
  simp only [he,heG] at hcconv
  convert hcconv using 1
  funext i
  apply Subtype.ext
  rfl

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
