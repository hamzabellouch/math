import Mathlib
import OAI.Probability.Perceptron.Control.FreshControl
import OAI.Probability.Perceptron.Control.ContactControl
import OAI.Probability.Perceptron.Variational.ContactDensity
import OAI.Probability.Perceptron.Cascade.Poissonization
import OAI.Probability.Perceptron.Variational.Field
import OAI.Probability.Perceptron.Variational.BoundaryEstimate
import OAI.Probability.Perceptron.Cavity.FreshDensity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem sourceStepContactObjective_eventual_lower (k : ℕ)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P)
    (g : Jet3) (p d : ℕ → ℕ)
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
    (w : Fin (k+1) → ℝ) (q r : Fin (k+1) → Time)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
    (hq1 : (q (Fin.last k):ℝ)<1) (hr : Monotone r) (hr1 : (r (Fin.last k):ℝ)<1)
    {η : ℝ} (hη : 0<η) (hqr : ∀ i, (q i:ℝ)+η≤(r i:ℝ))
    (α : ℝ≥0) (H : ℝ) (hH0 : 0≤H)
    (hH : (entropy (weightedStepTrial w r (fun i => (hw i).le) hw1)).toReal+
      2*(α:ℝ)*‖g.f‖ ≤ η*w (Fin.last k)*H)
    {δ ε : ℝ} (hδ : 0<δ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a ∈ sourceContactCompactDomain n k α H,
      -ε ≤ sourceStepContactObjective n k P g.f (fun i => p i.val) (fun i => d i.val)
        w q (fun i => (hw i).le) hw1 δ a := by
  choose c hc hm using fun n => source_global_contact_exists n k P g.f
    (fun i => p i.val) (fun i => d i.val) w q hw hw1 δ α hH0
  have hmin n := source_global_contact_perturbation_min n k P g.f
    (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ α H (hc n) (hm n)
  have he : ∀ᶠ n : ℕ in atTop, -ε ≤ sourceStepContactObjective n k P g.f
      (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ (c n) := by
    by_contra hnot
    have hf : ∃ᶠ n : ℕ in atTop, sourceStepContactObjective n k P g.f
        (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ (c n)< -ε := by
      simpa only [not_eventually,not_le] using hnot
    obtain ⟨v,hv,hneg⟩ := extraction_of_frequently_atTop hf
    obtain ⟨ν,s,hs,hlim⟩ := compact_array_law_subsequence (fun n =>
      sourceGibbsArrayLaw (v n) k g.f (fun i => p i.val) (fun i => d i.val)
        (c (v n)).2.1 (c (v n)).2.2 (stepCumulative w) (c (v n)).1)
    let b := v ∘ s
    have hb : StrictMono b := hv.comp hs
    have hl : Tendsto (fun n => sourceGibbsArrayLaw (b n) k g.f
        (fun i => p i.val) (fun i => d i.val) (c (b n)).2.1 (c (b n)).2.2
          (stepCumulative w) (c (b n)).1) atTop (𝓝 ν) := hlim
    have ht : ∀ᶠ n in atTop, 0<(c (b n)).1 := by
      filter_upwards [hb.tendsto_atTop.eventually
        (sourceNegativeContact_positive_density w hw hw1 H hε)] with n hn
      exact hn P g.f _ _ q hq hq1 δ α (c (b n)) (hc (b n)) (hneg (s n))
    have hcap : ∀ᶠ n in atTop, (c (b n)).2.1 (Fin.last k)<H := by
      filter_upwards [hb.tendsto_atTop.eventually
        (sourceNegativeContact_field_interior w hw hw1 P g.f q r hr hr1 hη hqr α H hH hε)] with n hn
      exact hn _ _ δ hδ.le (c (b n)) (hc (b n)) (hneg (s n))
    have hord := source_global_contact_control_order_along k P g p d w q hw hw1 hq δ α H c
      hc hm hH0 hcover hb hl hcap hB
    have hfresh := source_contact_freshLog_control k g p d (stepCumulative w)
      (stepCumulative_strictMono w hw) (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)
      (fun n => (c n).1) (fun n => (c n).2.1) (fun n => (hc n).2.1.1.1)
      (fun n => (hc n).2.1.2) (fun n => (c n).2.2) (fun n => (hc n).2.2) hmin hH0
      (fun n => (hc n).2.1.1.2 0) (T := (α:ℝ)) (fun n => (hc n).1.2) hcover hb hl P hB
    have hderiv : controlValue P g.f (weightedStepTrial w q (fun i => (hw i).le) hw1)+δ ≤
        controlValue P g.f (quantileTrial (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))) := by
      apply ge_of_tendsto hfresh
      filter_upwards [ht] with n hn
      rw [←sourceDensityIncrement_eq_fresh (b n) k g.f _ _ _
        (hc (b n)).2.1.1.1 (hc (b n)).2.1.2 _ _
        (stepCumulative_strictMono w hw) (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)]
      exact source_global_contact_density (b n) k P g.f _ _ w q hw hw1 δ α H (hc (b n)) (hm (b n)) hn
    linarith
  filter_upwards [he] with n hn
  intro a ha
  exact hn.trans (hm n ha)


lemma source_depoisson_error_tendsto (f : ℝ →ᵇ ℝ) (α : ℝ≥0) :
    Tendsto (fun n : ℕ => ‖f‖/(n+1:ℕ)*(Real.sqrt ((n+1:ℕ)*(α:ℝ))+1)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h1 : Tendsto (fun n : ℕ => (α:ℝ)/(n+1:ℕ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have h2 : Tendsto (fun n : ℕ => (1:ℝ)/(n+1:ℕ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have he (n : ℕ) : ‖f‖/(n+1:ℕ)*(Real.sqrt ((n+1:ℕ)*(α:ℝ))+1)=
      ‖f‖*(Real.sqrt ((α:ℝ)/(n+1:ℕ))+1/(n+1:ℕ)) := by
    have hn0 : (0:ℝ)<(n+1:ℕ) := by positivity
    have hs : Real.sqrt ((n+1:ℕ)*(α:ℝ))/(n+1:ℕ)=Real.sqrt ((α:ℝ)/(n+1:ℕ)) := by
      calc
        _ = Real.sqrt (((n+1:ℕ)*(α:ℝ))/((n+1:ℕ):ℝ)^2) := by
          rw [Real.sqrt_div (by positivity),Real.sqrt_sq hn0.le]
        _ = _ := by congr 1; field_simp
    calc
      _ = ‖f‖*(Real.sqrt ((n+1:ℕ)*(α:ℝ))/(n+1:ℕ)+1/(n+1:ℕ)) := by ring
      _ = _ := by rw [hs]
  simp_rw [he]
  simpa using (h1.sqrt.add h2).const_mul ‖f‖

lemma source_zeroField_original_compare (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (z : Fin k→ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (α : ℝ≥0) :
    expectedPressure (α:ℝ) 1 f (n+1) ≤
      sourceExpectedPressure n k f p d (fun _ => 0) z α (fun _ => 3/2)+
      8*perturbationScale (n+1)^2+‖f‖/(n+1:ℕ)*(Real.sqrt ((n+1:ℕ)*(α:ℝ))+1) := by
  have hp := sourceExpectedPressure_perturbation_comparison n k f p d (fun _ => 0)
    (fun _ => le_rfl) monotone_const z hz hz0 hz1 α
    (u := fun _ => 0) (v := fun _ => 3/2)
    (fun _ => ⟨le_rfl,by norm_num⟩) (fun _ => by constructor <;> norm_num)
  change |sourceExpectedPressure n k f p d (fun _ => 0) z α (fun _ => 3/2)-
    sourceExpectedPressure n k f p d (fun _ => 0) z α (fun _ => 0)|≤_ at hp
  have hd := sourceExpectedPressure_floor_count_compare n k f p d (fun _ => 0) z
    (fun _ => 0) hz hz0 hz1 α
  have ho := sourceCountExpectedLog_original (α:ℝ) 1 f n k p d z hz hz0 hz1
  simp only [one_smul,patternCount,mul_comm (α:ℝ)] at ho
  rw [ho] at hd
  linarith [(abs_le.mp hp).1,(abs_le.mp hd).1]

theorem expectedPressure_upper_weightedStep (k : ℕ)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P)
    (g : Jet3) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
    (hq1 : (q (Fin.last k):ℝ)<1) (α : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, expectedPressure (α:ℝ) 1 g.f (n+1) ≤
      (entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal+
      (α:ℝ)*controlValue P g.f (weightedStepTrial w q (fun i => (hw i).le) hw1)+ε := by
  let r : Fin (k+1)→Time := fun i => ⟨((q i:ℝ)+1)/2,by
    constructor <;> linarith [(q i).2.1,(q i).2.2]⟩
  have hr : Monotone r := by
    intro i j hij
    change ((q i:ℝ)+1)/2 ≤ ((q j:ℝ)+1)/2
    have he : (q i:ℝ)≤(q j:ℝ) := hq hij
    linarith
  have hr1 : (r (Fin.last k):ℝ)<1 := by dsimp [r]; linarith
  let η : ℝ := (1-(q (Fin.last k):ℝ))/2
  have hη : 0<η := by dsimp [η]; linarith
  have hqr i : (q i:ℝ)+η≤(r i:ℝ) := by
    have he : (q i:ℝ)≤(q (Fin.last k):ℝ) := hq (Fin.le_last i)
    dsimp [η,r]
    linarith
  let A := (entropy (weightedStepTrial w r (fun i => (hw i).le) hw1)).toReal+2*(α:ℝ)*‖g.f‖
  let H := A/(η*w (Fin.last k))
  have hH0 : 0≤H := by
    apply div_nonneg _ (mul_pos hη (hw _)).le
    dsimp [A]
    positivity
  have hH : A≤η*w (Fin.last k)*H := by
    dsimp [H]
    rw [mul_div_cancel₀ _ (ne_of_gt (mul_pos hη (hw _)))]
  let δ := ε/(4*((α:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hd : (α:ℝ)*δ≤ε/4 := by
    dsimp [δ]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    have hc : (α:ℝ)*ε≤ε*((α:ℝ)+1) := by nlinarith [α.coe_nonneg]
    have he : (α:ℝ)*(ε/(4*((α:ℝ)+1)))*4=(α:ℝ)*ε/((α:ℝ)+1) := by
      field_simp
    rw [he]
    exact (div_le_iff₀ (by positivity)).mpr hc
  let p : ℕ→ℕ := fun i => (Nat.unpair i).1
  let d : ℕ→ℕ := fun i => (Nat.unpair i).2
  have hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b := by
    intro a b _
    exact ⟨Nat.pair a b,by simp [p,d]⟩
  have hc := sourceStepContactObjective_eventual_lower k P hB g p d hcover w q r hw hw1
    hq hq1 hr hr1 hη hqr α H hH0 hH hδ (show 0<ε/4 by positivity)
  have ht : Tendsto (fun n : ℕ => 8*perturbationScale (n+1)^2) atTop (𝓝 0) := by
    simpa using perturbationScale_tendsto_zero.pow 2 |>.const_mul 8
  filter_upwards [hc,ht.eventually (gt_mem_nhds (show (0:ℝ)<ε/4 by positivity)),
    (source_depoisson_error_tendsto g.f α).eventually (gt_mem_nhds (show (0:ℝ)<ε/4 by positivity))]
    with n hn ht' he'
  have ha : (α,fun _ => 0,fun _ : Fin (n+1) => 3/2)∈sourceContactCompactDomain n k α H := by
    refine ⟨⟨zero_le,le_rfl⟩,⟨⟨fun _ => le_rfl,fun _ => hH0⟩,monotone_const⟩,?_⟩
    constructor <;> intro j <;> norm_num
  have hh := hn _ ha
  simp only [sourceStepContactObjective,sourceJointPressure,quadraticBoxPenalty,
    sub_self,zero_pow (by norm_num : 2≠0),mul_zero,Finset.sum_const_zero,sub_zero,add_zero] at hh
  have ho := source_zeroField_original_compare n k g.f (fun i => p i.val) (fun i => d i.val)
    (stepCumulative w) (stepCumulative_strictMono w hw) (stepCumulative_pos w hw)
    (stepCumulative_lt_one w hw hw1) α
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
