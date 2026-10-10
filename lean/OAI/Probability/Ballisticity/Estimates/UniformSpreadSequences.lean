import Mathlib
import OAI.Probability.Ballisticity.Estimates.EndpointPrefixConditionedReal
import OAI.Probability.Ballisticity.Estimates.NonCollapsedSums

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma uniform_spread_of_no_collapse {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : ℝ → Ω → ℝ)
    (hnot : ∀ (r : ℕ → ℝ), Tendsto r atTop atTop →
      ¬ TendstoInMeasure μ (fun i ω => F (r i) ω/r i) atTop 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r →
      c ≤ μ.real {ω | c*r < |F r ω|} := by
  by_contra hn
  push Not at hn
  have hx (i : ℕ) : ∃ r : ℝ, (i:ℝ)+1 ≤ r ∧ μ.real {ω | dyadicCut i*r < |F r ω|} < dyadicCut i :=
    hn (dyadicCut i) (dyadicCut_pos i) ((i:ℝ)+1) (by positivity)
  choose r hr hb using hx
  have hrpos (i) : 0 < r i := lt_of_lt_of_le (by positivity) (hr i)
  have hrinf : Tendsto r atTop atTop := tendsto_atTop_mono hr
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).atTop_add tendsto_const_nhds)
  apply hnot r hrinf
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ dyadicCut_tendsto
  filter_upwards [dyadicCut_tendsto.eventually (gt_mem_nhds hε)] with i hi
  apply le_trans (measureReal_mono (μ := μ) ?_ (measure_ne_top _ _)) (hb i).le
  intro ω hω
  change ε ≤ |F (r i) ω/r i| at hω
  change dyadicCut i*r i < |F (r i) ω|
  rw [abs_div,abs_of_pos (hrpos i),le_div_iff₀ (hrpos i)] at hω
  exact (mul_lt_mul_of_pos_right hi (hrpos i)).trans_le hω
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem transverse_uniform_spread {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r →
      c ≤ (independentConditionedPairLaw ν (realPosition (step e))).real
        {P | c*r < |firstHitPairGap (realPosition (step e)) f
          ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊ P|} := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  let X := commonIncrementProcess ℓ f
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  apply uniform_spread_of_no_collapse μ
  intro r hr hcollapse
  let n := fun i => fluctuationScale μ (X 0) (r i)
  have hI := independent_commonWordIncrement_integrable ν hue ℓ (signed_direction_unit e)
    htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hn : Tendsto n atTop atTop :=
    (fluctuationScale_tendsto μ (X 0) (measurable_commonIncrementProcess ℓ f 0) hI hne).comp hr
  have hc := zero_lt_one.trans_le (commonMeanWidth_ge_one ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e))
  have hk := double_floor_ratio n hn hc
  have herr := transverse_firstHit_fixed_sum_error ν hue e f hef htrans r hr
    (fun i => ⌊n i⌋₊) (show (0:ℝ)≤1 by norm_num) (Eventually.of_forall fun i => by
      change (⌊n i⌋₊:ℝ) ≤ 1*n i
      rw [one_mul]
      exact Nat.floor_le (fluctuationScale_nonneg _ _ _))
  have hs := inMeasure_sub_zero μ _ _ hcollapse herr
  have hs' : TendstoInMeasure μ (fun i P => realPartialSum (fun j => X j P)
      ⌊(⌊n i⌋₊:ℝ)/commonMeanWidth ν ℓ⌋₊/r i) atTop 0 := by
    apply hs.congr_left
    intro i
    filter_upwards [] with P
    dsimp only [X,ℓ,μ,n]
    ring
  exact iid_fluctuation_not_collapse μ X (measurable_commonIncrementProcess ℓ f)
    (commonIncrements_independent ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f)
    (commonIncrements_identDistrib ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f)
    (independent_commonWordIncrement_symmetric ν ℓ htrans f) hI hne r hr _
    (by positivity) hk hs'
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma bounded_mean_probability_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : Measurable F)
    (hF0 : ∀ ω, 0 ≤ F ω) (hF1 : ∀ ω, F ω ≤ 1) {q : ℝ} (hq : 0 ≤ q)
    (hmean : q ≤ ∫ ω, F ω ∂μ) :
    q/2 ≤ μ.real {ω | q/2 ≤ F ω} := by
  let A := {ω | q/2 ≤ F ω}
  have hA : MeasurableSet A := measurableSet_le measurable_const hF
  have hFi : Integrable F μ := (integrable_const (1:ℝ)).mono' hF.aestronglyMeasurable
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (hF0 ω)]; exact hF1 ω)
  have hAi : Integrable (A.indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator hA
  have hb := integral_mono hFi ((integrable_const (q/2)).add hAi) (fun ω => ?_)
  · change (∫ ω, F ω ∂μ) ≤ ∫ ω, q/2+A.indicator (fun _ => (1:ℝ)) ω ∂μ at hb
    rw [integral_add (integrable_const _) hAi,integral_indicator hA] at hb
    simp only [integral_const,smul_eq_mul,one_mul,mul_one,
      Measure.real,Measure.restrict_apply_univ,measure_univ, ENNReal.toReal_one] at hb
    change q/2 ≤ μ.real A
    change (∫ ω, F ω ∂μ) ≤ q/2+μ.real A at hb
    linarith
  · change F ω ≤ q/2+A.indicator (fun _ => (1:ℝ)) ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      linarith [hF1 ω]
    · rw [Set.indicator_of_notMem hω,add_zero]
      exact le_of_not_ge hω
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem uniform_raw_jump {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ a j R : ℝ, 0 < a ∧ 0 < j ∧ 0 < R ∧ ∀ r : ℝ, R ≤ r →
      let H := ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊
      0 < H ∧ ∀ b : ℝ, ∃ s : ℝ, (s=1 ∨ s= -1) ∧ ∀ x : Lattice d,
      j ≤ (environmentLaw ν).real {ω | j ≤ (quenchedKernel (ω,x)).real
        (EndpointPrefix (realPosition (step e)) x H
          {z | a*r < s*(signedCoordinate f (z-x)-b)})} := by
  let ℓ := realPosition (step e)
  let μ₁ := conditionedLaw ν ℓ
  let n := fun r => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) r
  have hp := noDrop_positive_of_directionallyTransient ν ℓ htrans
  let : IsProbabilityMeasure μ₁ := conditionedLaw_probability ν ℓ (ne_of_gt hp)
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) := independentConditionedPairLaw_probability ν ℓ (ne_of_gt hp)
  let p := (annealedLaw ν).real (NoDrop ℓ 0)
  have hp0 : 0 < p := ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _)
  obtain ⟨c,hc,R,hR,hspread⟩ := transverse_uniform_spread ν hue e f hef htrans
  have hn : Tendsto n atTop atTop := fluctuationScale_tendsto _ _
    (measurable_commonIncrementProcess ℓ f 0)
    (independent_commonWordIncrement_integrable ν hue ℓ (signed_direction_unit e) htrans
      (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f)
    (independent_commonWordIncrement_nonzero ν hue e f hef htrans)
  obtain ⟨R₁,hR₁⟩ := Filter.eventually_atTop.1 (hn.eventually (eventually_ge_atTop (1:ℝ)))
  refine ⟨c/2,p*c/8,max R R₁,by positivity,by positivity,hR.trans_le (le_max_left _ _),fun r hr => ?_⟩
  have hrR := (le_max_left R R₁).trans hr
  have hn1 := hR₁ r ((le_max_right R R₁).trans hr)
  let H := ⌊n r⌋₊
  have hH : 0 < H := Nat.floor_pos.mpr hn1
  refine ⟨hH,fun b => ?_⟩
  have hsp : c ≤ (μ₁.prod μ₁).real
      {P | 2*(c/2*r) < |signedCoordinate f (recordIndexPosition ℓ H P.1)-signedCoordinate f (recordIndexPosition ℓ H P.2)|} := by
    have he : 2*(c/2*r)=c*r := by ring
    simpa only [he,firstHitPairGap,independentConditionedPairLaw,μ₁,ℓ,H,n] using hspread r hrR
  obtain ⟨s,hs,hdev⟩ := scalar_pair_tail_one_side μ₁
    (fun X => signedCoordinate f (recordIndexPosition ℓ H X)) b (c/2*r) c hsp
  refine ⟨s,hs,fun x => ?_⟩
  let A := EndpointPrefix ℓ x H {z | c/2*r < s*(signedCoordinate f (z-x)-b)}
  have hmean : p*c/4 ≤ (annealedFrom ν x).real A := by
    have hh := endpointPrefix_conditioned_real ν e htrans x hH
      {z | c/2*r < s*(signedCoordinate f z-b)}
    have hm := mul_le_mul_of_nonneg_left hdev hp0.le
    have hm' : p*c/4 ≤ p*μ₁.real {X | c/2*r < s*(signedCoordinate f (recordIndexPosition ℓ H X)-b)} := by
      simpa only [mul_div_assoc] using hm
    exact hm'.trans hh
  let F := fun ω : Environment d => (quenchedKernel (ω,x)).real A
  have hF : Measurable F := ((Kernel.measurable_coe _ (measurableSet_endpointPrefix ℓ x H _)).comp
    (measurable_id.prodMk measurable_const)).ennreal_toReal
  have hm : p*c/4 ≤ ∫ ω, F ω ∂environmentLaw ν := by
    simpa only [F,annealedFrom_real_integral ν x A (measurableSet_endpointPrefix ℓ x H _)] using hmean
  have hh := bounded_mean_probability_lower (environmentLaw ν) F hF
    (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one) (by positivity : 0 ≤ p*c/4) hm
  have he : (p*c/4)/2=p*c/8 := by ring
  simpa only [he,F,A] using hh
end DirectionalTransience

end

end

end OAI
