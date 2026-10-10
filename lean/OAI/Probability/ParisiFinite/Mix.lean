import Mathlib
import OAI.Probability.ParisiFinite.MeasurableStepParam

namespace OAI

/-! Mix. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath
namespace BoundedCoefficient
variable {β : ℝ≥0}

def mix (c d : BoundedCoefficient β) (θ : ℝ≥0) (hθ : θ≤1) : BoundedCoefficient β where
  val := fun t => (1-θ)*c.val t+θ*d.val t
  mono := fun s t h => add_le_add (mul_le_mul_of_nonneg_left (c.mono h) (by positivity))
    (mul_le_mul_of_nonneg_left (d.mono h) (by positivity))
  bound := fun t => (add_le_add (mul_le_mul_of_nonneg_left (c.bound t) (by positivity))
    (mul_le_mul_of_nonneg_left (d.bound t) (by positivity))).trans_eq (by rw [←add_mul,tsub_add_cancel_of_le hθ,one_mul])

lemma mix_real (c d : BoundedCoefficient β) (θ : ℝ≥0) (hθ : θ≤1) (t : ℝ) :
    (c.mix d θ hθ).real t=(1-(θ:ℝ))*c.real t+(θ:ℝ)*d.real t := by
  simp only [mix,real,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_sub hθ,NNReal.coe_one]

lemma mix_difference (c d : BoundedCoefficient β) (θ : ℝ≥0) (hθ : θ≤1) (t : ℝ) :
    (c.mix d θ hθ).real t-c.real t=(θ:ℝ)*(d.real t-c.real t) := by rw [mix_real];ring

lemma mix_tendsto (c d : BoundedCoefficient β) {Θ : ℕ → ℝ≥0} (hΘ : ∀ n,Θ n≤1)
    (hθ : Tendsto Θ atTop (𝓝 0)) (t : ℝ≥0) :
    Tendsto (fun n => (c.mix d (Θ n) (hΘ n)).val t) atTop (𝓝 (c.val t)) := by
  apply NNReal.tendsto_coe.mp
  have hθ' := NNReal.continuous_coe.continuousAt.tendsto.comp hθ
  simpa only [mix,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_sub (hΘ _),NNReal.coe_one,
    NNReal.coe_zero,sub_zero,one_mul,zero_mul,add_zero,Function.comp_def] using
    (((tendsto_const_nhds (x := (1:ℝ))).sub hθ').mul_const (c.val t:ℝ)).add (hθ'.mul_const (d.val t:ℝ))

lemma norm_direction_le (c d : BoundedCoefficient β) (t : ℝ) : ‖(d.real t-c.real t)/2‖≤β := by
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hh : |d.real t-c.real t|≤β := abs_le.mpr ⟨by linarith [c.real_le t,d.real_nonneg t],
    by linarith [d.real_le t,c.real_nonneg t]⟩
  linarith [β.coe_nonneg]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {K M : ℝ≥0}

def variationIntegral (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (c d e f : BoundedCoefficient β) (b : Drift K M) : ℝ :=
  ∫ t in (0:ℝ)..1,(d.real t-c.real t)/2*expectedProduct P W e f b t

lemma variation_integrable (hW : IsBrownianReal W P) (hβ : 0<β)
    (c d e f : BoundedCoefficient β) (b : Drift K M) :
    IntervalIntegrable (fun t => (d.real t-c.real t)/2*expectedProduct P W e f b t) volume 0 1 :=
  (((d.real_intervalIntegrable 0 1).sub (c.real_intervalIntegrable 0 1)).div_const 2).mul_continuousOn
    (expectedProduct_continuous hW e f hβ b).continuousOn

lemma variationIntegral_tendsto (hW : IsBrownianReal W P) (hβ : 0<β)
    (c d : BoundedCoefficient β) {E F : ℕ → BoundedCoefficient β} {e f : BoundedCoefficient β}
    (hE : ∀ t,Tendsto (fun n => (E n).val t) atTop (𝓝 (e.val t)))
    (hF : ∀ t,Tendsto (fun n => (F n).val t) atTop (𝓝 (f.val t)))
    {B : ℕ → Drift K M} {b : Drift K M}
    (hB : ∀ t x,Tendsto (fun n => (B n).val t x) atTop (𝓝 (b.val t x))) :
    Tendsto (fun n => variationIntegral P W c d (E n) (F n) (B n)) atTop
      (𝓝 (variationIntegral P W c d e f b)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (β:ℝ))
    (Eventually.of_forall fun n => by
      simpa only [uIoc_of_le zero_le_one] using
        (variation_integrable hW hβ c d (E n) (F n) (B n)).1.aestronglyMeasurable)
    (Eventually.of_forall fun n => ?_) intervalIntegrable_const
  · exact ae_of_all _ fun t _ => (expectedProduct_tendsto hW hβ hE hF hB t).const_mul _
  · exact ae_of_all _ fun t _ => by
      rw [norm_mul]
      exact (mul_le_mul (norm_direction_le c d t) (expectedProduct_bound hW (E n) (F n) hβ (B n) t)
        (norm_nonneg _) β.coe_nonneg).trans_eq (mul_one _)

 

theorem field_first_variation (hW : IsBrownianReal W P) (hβ : 0<β) (c d : BoundedCoefficient β)
    {Θ : ℕ → ℝ≥0} (hΘ : ∀ n,Θ n≤1) (hΘpos : ∀ n,0<Θ n) (hθ : Tendsto Θ atTop (𝓝 0)) :
    Tendsto (fun n => (field β (c.mix d (Θ n) (hΘ n)).val 0 0-field β c.val 0 0)/(Θ n:ℝ)) atTop
      (𝓝 (variationIntegral P W c d c c (c.driftData hβ))) := by
  let C (n : ℕ) := c.mix d (Θ n) (hΘ n)
  have hC : ∀ t,Tendsto (fun n => (C n).val t) atTop (𝓝 (c.val t)) := mix_tendsto c d hΘ hθ
  have hl := variationIntegral_tendsto hW hβ c d hC hC
    (B := fun _ => c.driftData hβ) (b := c.driftData hβ) (fun _ _ => tendsto_const_nhds)
  have hu := variationIntegral_tendsto hW hβ c d
    (E := fun _ => c) (F := fun _ => c) (e := c) (f := c) (fun _ => tendsto_const_nhds)
    (fun _ => tendsto_const_nhds) (B := fun n => (C n).driftData hβ)
    (b := c.driftData hβ) (drift_tendsto hβ hC)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
  · intro n
    have hh := field_comparison_lower hW (C n) c hβ
    have he : (∫ t in (0:ℝ)..1,((C n).real t-c.real t)/2*expectedProduct P W (C n) (C n) (c.driftData hβ) t)=
        (Θ n:ℝ)*variationIntegral P W c d (C n) (C n) (c.driftData hβ) := by
      rw [variationIntegral,←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [C]
      rw [mix_difference]
      ring
    rw [he] at hh
    exact (le_div_iff₀ (show (0:ℝ)<Θ n from hΘpos n)).mpr (by nlinarith)
  · intro n
    have hh := field_comparison_upper hW (C n) c hβ
    have he : (∫ t in (0:ℝ)..1,((C n).real t-c.real t)/2*expectedProduct P W c c ((C n).driftData hβ) t)=
        (Θ n:ℝ)*variationIntegral P W c d c c ((C n).driftData hβ) := by
      rw [variationIntegral,←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [C]
      rw [mix_difference]
      ring
    rw [he] at hh
    exact (div_le_iff₀ (show (0:ℝ)<Θ n from hΘpos n)).mpr (by nlinarith)

lemma penalty_mix_sub (c d : BoundedCoefficient β) (θ : ℝ≥0) (hθ : θ≤1) :
    coefficientPenalty (c.mix d θ hθ).val 0 1-coefficientPenalty c.val 0 1=
      (θ:ℝ)*(∫ t in (0:ℝ)..1,t*(d.real t-c.real t)/2) := by
  simp only [coefficientPenalty,zero_add,NNReal.coe_zero,NNReal.coe_one]
  change (∫ t in (0:ℝ)..1,t*(c.mix d θ hθ).real t/2)-(∫ t in (0:ℝ)..1,t*c.real t/2)=_
  have h1 : IntervalIntegrable (fun t => t*(c.mix d θ hθ).real t/2) volume 0 1 :=
    coefficient_integrable (c.mix d θ hθ).mono 0 1
  have h2 : IntervalIntegrable (fun t => t*c.real t/2) volume 0 1 := coefficient_integrable c.mono 0 1
  rw [←intervalIntegral.integral_sub h1 h2,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [mix_real]
  ring

def firstVariation (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (hβ : 0<β)
    (c d : BoundedCoefficient β) : ℝ :=
  ∫ t in (0:ℝ)..1,(d.real t-c.real t)/2*(expectedProduct P W c c (c.driftData hβ) t-t)

lemma firstVariation_eq (hW : IsBrownianReal W P) (hβ : 0<β) (c d : BoundedCoefficient β) :
    firstVariation P W hβ c d=variationIntegral P W c d c c (c.driftData hβ)-
      (∫ t in (0:ℝ)..1,t*(d.real t-c.real t)/2) := by
  have hp : IntervalIntegrable (fun t => t*(d.real t-c.real t)/2) volume 0 1 := by
    have hh := (coefficient_integrable d.mono 0 1).sub (coefficient_integrable c.mono 0 1)
    convert! hh using 1
    ext t
    dsimp only [real]
    ring
  rw [variationIntegral,←intervalIntegral.integral_sub (variation_integrable hW hβ c d c c _) hp]
  apply intervalIntegral.integral_congr
  intro t _
  ring

 

theorem functional_first_variation (hW : IsBrownianReal W P) (hβ : 0<β) (c d : BoundedCoefficient β)
    {Θ : ℕ → ℝ≥0} (hΘ : ∀ n,Θ n≤1) (hΘpos : ∀ n,0<Θ n) (hθ : Tendsto Θ atTop (𝓝 0)) :
    Tendsto (fun n => (orderParameterFunctional β (c.mix d (Θ n) (hΘ n)).val-
      orderParameterFunctional β c.val)/(Θ n:ℝ)) atTop (𝓝 (firstVariation P W hβ c d)) := by
  have hh := (field_first_variation hW hβ c d hΘ hΘpos hθ).sub_const
    (∫ t in (0:ℝ)..1,t*(d.real t-c.real t)/2)
  rw [←firstVariation_eq hW hβ c d] at hh
  convert! hh using 1
  ext n
  have he := penalty_mix_sub c d (Θ n) (hΘ n)
  have hne : (Θ n:ℝ)≠0 := (show (0:ℝ)<Θ n from hΘpos n).ne'
  simp only [orderParameterFunctional,field,tsub_zero]
  field_simp
  nlinarith

end BoundedCoefficient
end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite

def probabilityMix (ρ ν : ProbabilityMeasure OrderPoint) (θ : ℝ≥0) (hθ : θ≤1) :
    ProbabilityMeasure OrderPoint :=
  ⟨(1-θ) • (ρ:Measure OrderPoint)+θ • (ν:Measure OrderPoint),by
    apply isProbabilityMeasure_iff.mpr
    simp only [Measure.add_apply,Measure.coe_nnreal_smul_apply,measure_univ,mul_one]
    rw [←ENNReal.coe_add,tsub_add_cancel_of_le hθ]
    rfl⟩

lemma probabilityMix_real (ρ ν : ProbabilityMeasure OrderPoint) (θ : ℝ≥0) (hθ : θ≤1)
    (s : Set OrderPoint) :
    (probabilityMix ρ ν θ hθ:Measure OrderPoint).real s=
      (1-(θ:ℝ))*(ρ:Measure OrderPoint).real s+(θ:ℝ)*(ν:Measure OrderPoint).real s := by
  change (((1-θ) • (ρ:Measure OrderPoint)+θ • (ν:Measure OrderPoint)) s).toReal=_
  rw [Measure.add_apply,ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  simp only [Measure.coe_nnreal_smul_apply,ENNReal.toReal_mul,ENNReal.coe_toReal,
    NNReal.coe_sub hθ,NNReal.coe_one,Measure.real]

lemma probabilityMix_coefficient_real (β : ℝ≥0) (ρ ν : ProbabilityMeasure OrderPoint)
    (θ : ℝ≥0) (hθ : θ≤1) (t : ℝ≥0) :
    (measureCoefficient (probabilityMix ρ ν θ hθ) β t:ℝ)=
      (1-(θ:ℝ))*(measureCoefficient ρ β t:ℝ)+(θ:ℝ)*(measureCoefficient ν β t:ℝ) := by
  simp only [measureCoefficient,NNReal.coe_mul,Real.coe_toNNReal _ measureReal_nonneg,
    ]
  rw [probabilityMix_real]
  ring

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite
open ParisiPath BoundedCoefficient

lemma probabilityMix_coefficient (β : ℝ≥0) (ρ ν : ProbabilityMeasure OrderPoint)
    (θ : ℝ≥0) (hθ : θ≤1) :
    measureCoefficient (probabilityMix ρ ν θ hθ) β=((ofMeasure β ρ).mix (ofMeasure β ν) θ hθ).val := by
  funext t
  apply NNReal.eq
  rw [probabilityMix_coefficient_real]
  simp only [BoundedCoefficient.mix,ofMeasure,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_sub hθ,NNReal.coe_one]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {β : ℝ≥0}

 

theorem measureFunctional_first_variation (hW : IsBrownianReal W P) (hβ : 0<β)
    (ρ ν : ProbabilityMeasure OrderPoint) {Θ : ℕ → ℝ≥0} (hΘ : ∀ n,Θ n≤1)
    (hΘpos : ∀ n,0<Θ n) (hθ : Tendsto Θ atTop (𝓝 0)) :
    Tendsto (fun n => (measureFunctional β (probabilityMix ρ ν (Θ n) (hΘ n))-
      measureFunctional β ρ)/(Θ n:ℝ)) atTop
      (𝓝 (firstVariation P W hβ (ofMeasure β ρ) (ofMeasure β ν))) := by
  have hh := functional_first_variation hW hβ (ofMeasure β ρ) (ofMeasure β ν) hΘ hΘpos hθ
  convert! hh using 1
  ext n
  rw [measureFunctional,probabilityMix_coefficient]
  rfl

 

theorem minimizingParisi_firstVariation_nonneg (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    (ν : ProbabilityMeasure OrderPoint) :
    0≤firstVariation P W hβ (ofMeasure β ρ) (ofMeasure β ν) := by
  let Θ (n : ℕ) : ℝ≥0 := 1/(n+1:ℕ)
  have hp (n : ℕ) : 0<Θ n := by dsimp [Θ];positivity
  have hb (n : ℕ) : Θ n≤1 := by
    apply (div_le_one (by positivity : (0:ℝ≥0)<(n+1:ℕ))).mpr
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have ht : Tendsto Θ atTop (𝓝 0) := by
    apply NNReal.tendsto_coe.mp
    simpa only [Θ,NNReal.coe_div,NNReal.coe_one,NNReal.coe_natCast,NNReal.coe_zero] using
      SKCavity.tendsto_succ_reciprocal
  apply ge_of_tendsto (measureFunctional_first_variation hW hβ ρ ν hb hp ht)
  exact Eventually.of_forall fun n => div_nonneg (sub_nonneg.mpr (hρ _)) (hp n).le

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite
open ParisiPath BoundedCoefficient

lemma integral_cdf_mul (ρ : ProbabilityMeasure OrderPoint) {f : ℝ → ℝ}
    (hf : Continuous f) {B : ℝ} (hB : 0≤B) (hb : ∀ t∈Icc (0:ℝ) 1,‖f t‖≤B) :
    (∫ t in (0:ℝ)..1,(ρ:Measure OrderPoint).real {x | (x:ℝ)≤t}*f t)=
      ∫ x,(∫ t in (x:ℝ)..1,f t) ∂(ρ:Measure OrderPoint) := by
  let k (x : OrderPoint) (t : ℝ) : ℝ := if (x:ℝ)≤t then f t else 0
  have hkm : Measurable (uncurry k) := by
    apply Measurable.ite (measurableSet_le (by fun_prop) measurable_snd)
      (hf.measurable.comp measurable_snd) measurable_const
  have hk : Integrable (uncurry k) ((ρ:Measure OrderPoint).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    apply Integrable.of_bound hkm.aestronglyMeasurable B
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le hkm.norm measurable_const)]
    filter_upwards [] with x
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    dsimp only [uncurry,k]
    split_ifs
    · exact hb t ht
    · simpa using hB
  have hx (x : OrderPoint) : (∫ t,k x t ∂(volume.restrict (Icc (0:ℝ) 1)))=
      ∫ t in (x:ℝ)..1,f t := by
    change (∫ t,(Ici (x:ℝ)).indicator f t ∂(volume.restrict (Icc (0:ℝ) 1)))=_
    rw [integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
    have he : Ici (x:ℝ)∩Icc (0:ℝ) 1=Icc (x:ℝ) 1 := by
      ext t
      simp only [mem_inter_iff,mem_Ici,mem_Icc]
      constructor
      · rintro ⟨h1,h2,h3⟩; exact ⟨h1,h3⟩
      · rintro ⟨h1,h2⟩;exact ⟨h1,x.property.1.trans h1,h2⟩
    rw [he,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le x.property.2]
  have ht (t : ℝ) : (∫ x,k x t ∂(ρ:Measure OrderPoint))=
      (ρ:Measure OrderPoint).real {x | (x:ℝ)≤t}*f t := by
    change (∫ x,({x : OrderPoint | (x:ℝ)≤t}).indicator (fun _ => f t) x ∂(ρ:Measure OrderPoint))=_
    rw [integral_indicator_const _ (by measurability)]
    rfl
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
  calc
    _ = ∫ t,∫ x,k x t ∂(ρ:Measure OrderPoint) ∂(volume.restrict (Icc (0:ℝ) 1)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun t => (ht t).symm
    _ = ∫ x,∫ t,k x t ∂(volume.restrict (Icc (0:ℝ) 1)) ∂(ρ:Measure OrderPoint) := (integral_integral_swap hk).symm
    _ = _ := integral_congr_ae (ae_of_all _ hx)

lemma measureCDF_mono (ρ : ProbabilityMeasure OrderPoint) :
    Monotone (fun t : ℝ => (ρ:Measure OrderPoint).real {x | (x:ℝ)≤t}) := by
  intro s t h
  apply measureReal_mono (fun x hx => hx.trans h)

lemma ofMeasure_real (β : ℝ≥0) (ρ : ProbabilityMeasure OrderPoint) (t : ℝ) (ht : 0≤t) :
    (ofMeasure β ρ).real t=(ρ:Measure OrderPoint).real {x | (x:ℝ)≤t}*(β:ℝ) := by
  simp only [ofMeasure,BoundedCoefficient.real,measureCoefficient,NNReal.coe_mul,
    Real.coe_toNNReal t ht,Real.coe_toNNReal _ measureReal_nonneg]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {β : ℝ≥0}

def deviation (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (hβ : 0<β)
    (c : BoundedCoefficient β) (t : ℝ) : ℝ :=
  expectedProduct P W c c (c.driftData hβ) t-t

def variationalPotential (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (hβ : 0<β)
    (c : BoundedCoefficient β) (t : ℝ) : ℝ :=
  ∫ s in t..1,deviation P W hβ c s

lemma continuous_deviation (hW : IsBrownianReal W P) (hβ : 0<β) (c : BoundedCoefficient β) :
    Continuous (deviation P W hβ c) := (expectedProduct_continuous hW c c hβ _).sub continuous_id

lemma norm_deviation_le (hW : IsBrownianReal W P) (hβ : 0<β) (c : BoundedCoefficient β)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : ‖deviation P W hβ c t‖≤2 := by
  apply (norm_sub_le _ _).trans
  have ht' : ‖t‖≤1 := by rw [Real.norm_eq_abs,abs_of_nonneg ht.1];exact ht.2
  linarith [expectedProduct_bound hW c c hβ (c.driftData hβ) t]

lemma hasDerivAt_variationalPotential (hW : IsBrownianReal W P) (hβ : 0<β)
    (c : BoundedCoefficient β) (t : ℝ) :
    HasDerivAt (variationalPotential P W hβ c) (-deviation P W hβ c t) t :=
  intervalIntegral.integral_hasDerivAt_left ((continuous_deviation hW hβ c).intervalIntegrable _ _)
    (continuous_deviation hW hβ c).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_deviation hW hβ c).continuousAt

lemma continuous_variationalPotential (hW : IsBrownianReal W P) (hβ : 0<β)
    (c : BoundedCoefficient β) : Continuous (variationalPotential P W hβ c) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_variationalPotential hW hβ c t).continuousAt

lemma variationalPotential_integrable (hW : IsBrownianReal W P) (hβ : 0<β)
    (c : BoundedCoefficient β) (ν : ProbabilityMeasure OrderPoint) :
    Integrable (fun x : OrderPoint => variationalPotential P W hβ c x) (ν:Measure OrderPoint) := by
  have hc : Continuous (fun x : OrderPoint => variationalPotential P W hβ c x) :=
    (continuous_variationalPotential hW hβ c).comp continuous_subtype_val
  simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact (μ := (ν:Measure OrderPoint)) isCompact_univ

lemma firstVariation_potential (hW : IsBrownianReal W P) (hβ : 0<β)
    (ρ ν : ProbabilityMeasure OrderPoint) :
    firstVariation P W hβ (ofMeasure β ρ) (ofMeasure β ν)=(β:ℝ)/2*
      ((∫ x,variationalPotential P W hβ (ofMeasure β ρ) x ∂(ν:Measure OrderPoint))-
        (∫ x,variationalPotential P W hβ (ofMeasure β ρ) x ∂(ρ:Measure OrderPoint))) := by
  let c := ofMeasure β ρ
  have hD := continuous_deviation hW hβ c
  have hb := norm_deviation_le hW hβ c
  have hi (μ : ProbabilityMeasure OrderPoint) : IntervalIntegrable
      (fun t => (μ:Measure OrderPoint).real {x | (x:ℝ)≤t}*deviation P W hβ c t) volume 0 1 :=
    (measureCDF_mono μ).intervalIntegrable.mul_continuousOn hD.continuousOn
  change (∫ t in (0:ℝ)..1,((ofMeasure β ν).real t-c.real t)/2*deviation P W hβ c t)=_
  change _=(β:ℝ)/2*((∫ x,(∫ t in (x:ℝ)..1,deviation P W hβ c t) ∂(ν:Measure OrderPoint))-
    (∫ x,(∫ t in (x:ℝ)..1,deviation P W hβ c t) ∂(ρ:Measure OrderPoint)))
  rw [←integral_cdf_mul ν hD (by norm_num) hb,←integral_cdf_mul ρ hD (by norm_num) hb,
    ←intervalIntegral.integral_sub (hi ν) (hi ρ),←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  dsimp only [c]
  rw [ofMeasure_real β ν t ht.1,ofMeasure_real β ρ t ht.1]
  ring

lemma minimizingParisi_potential_average_le (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    (ν : ProbabilityMeasure OrderPoint) :
    (∫ x,variationalPotential P W hβ (ofMeasure β ρ) x ∂(ρ:Measure OrderPoint))≤
      (∫ x,variationalPotential P W hβ (ofMeasure β ρ) x ∂(ν:Measure OrderPoint)) := by
  have hh := minimizingParisi_firstVariation_nonneg hW hβ hρ ν
  rw [firstVariation_potential hW hβ ρ ν] at hh
  have hp : (0:ℝ)<β := hβ
  nlinarith

lemma minimizingParisi_potential_average_le_point (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ) (t : OrderPoint) :
    (∫ x,variationalPotential P W hβ (ofMeasure β ρ) x ∂(ρ:Measure OrderPoint))≤
      variationalPotential P W hβ (ofMeasure β ρ) t := by
  have hh := minimizingParisi_potential_average_le hW hβ hρ ⟨Measure.dirac t,inferInstance⟩
  change _ ≤ ∫ x,variationalPotential P W hβ (ofMeasure β ρ) x ∂Measure.dirac t at hh
  simpa only [integral_dirac] using hh

 

theorem minimizingParisi_support_potential (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {t : OrderPoint} (ht : t∈(ρ:Measure OrderPoint).support) :
    ∀ s : OrderPoint,variationalPotential P W hβ (ofMeasure β ρ) t≤
      variationalPotential P W hβ (ofMeasure β ρ) s := by
  let g (x : OrderPoint) := variationalPotential P W hβ (ofMeasure β ρ) x
  let A := ∫ x,g x ∂(ρ:Measure OrderPoint)
  have hg : Continuous g := (continuous_variationalPotential hW hβ (ofMeasure β ρ)).comp continuous_subtype_val
  have hi : Integrable g (ρ:Measure OrderPoint) := variationalPotential_integrable hW hβ _ ρ
  have hlow : ∀ x,A≤g x := minimizingParisi_potential_average_le_point hW hβ hρ
  have hz : (fun x => g x-A)=ᵐ[(ρ:Measure OrderPoint)] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => sub_nonneg.mpr (hlow x))
      (hi.sub (integrable_const _))).mp
    rw [integral_sub hi (integrable_const _)]
    simp [A]
  have he : ∀ᵐ x ∂(ρ:Measure OrderPoint),g x=A := by
    filter_upwards [hz] with x hx
    exact sub_eq_zero.mp hx
  have hsup := (ρ:Measure OrderPoint).support_subset_of_isClosed (isClosed_eq hg continuous_const) he
  have ht' : g t=A := hsup ht
  intro s
  change g t≤g s
  rw [ht']
  exact hlow s

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite
open ParisiPath BoundedCoefficient
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {β : ℝ≥0}

lemma expectedProduct_zero (hW : IsBrownianReal W P) (hβ : 0<β)
    (c : BoundedCoefficient β) : expectedProduct P W c c (c.driftData hβ) 0=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [brownianPath_eq_ae hW,hW.eval_zero_ae_eq_zero] with ω hω h0
  rw [spin_eq _ _ _ (by simp),extend_of_mem _ (by simp),solution_zero,hω]
  simp only [Real.toNNReal_zero,Pi.zero_apply]
  change fieldGradient β c.val 0 (W 0 ω)*fieldGradient β c.val 0 (W 0 ω)=0
  rw [h0,fieldGradient_zero β hβ c.mono c.bound]
  simp

lemma expectedProduct_one_lt (hW : IsBrownianReal W P) (hβ : 0<β)
    (c : BoundedCoefficient β) : expectedProduct P W c c (c.driftData hβ) 1<1 := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let Z (ω : Ω) := c.spin (solution (c.driftData hβ) (brownianPath W ω)) 1
  have hZ (ω : Ω) : Z ω*Z ω<1 := by
    dsimp only [Z]
    rw [spin_eq _ _ _ (by simp)]
    simp only [Real.toNNReal_one,fieldGradient_terminal β hβ]
    simpa only [pow_two] using Real.tanh_sq_lt_one ((β:ℝ)*
      extend (solution (c.driftData hβ) (brownianPath W ω)) 1)
  have hi : Integrable (fun ω => 1-Z ω*Z ω) P :=
    (integrable_const 1).sub (spin_product_integrable hW c c hβ _ 1)
  have hp : 0<∫ ω,1-Z ω*Z ω ∂P := by
    apply (integral_pos_iff_support_of_nonneg (fun ω => sub_nonneg.mpr (hZ ω).le) hi).mpr
    have hs : Function.support (fun ω => 1-Z ω*Z ω)=univ := by
      ext ω
      simp only [Function.mem_support,mem_univ,iff_true]
      exact (sub_pos.mpr (hZ ω)).ne'
    rw [hs]
    simp
  rw [integral_sub (integrable_const _) (spin_product_integrable hW c c hβ _ 1)] at hp
  simpa [expectedProduct,Z] using hp

lemma minimizingParisi_deviation_interior (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {t : OrderPoint} (ht : t∈(ρ:Measure OrderPoint).support)
    (h0 : 0<(t:ℝ)) (h1 : (t:ℝ)<1) : deviation P W hβ (ofMeasure β ρ) t=0 := by
  have hl : IsLocalMin (variationalPotential P W hβ (ofMeasure β ρ)) (t:ℝ) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with s hs
    exact minimizingParisi_support_potential hW hβ hρ ht ⟨s,hs.1.le,hs.2.le⟩
  have hh := hl.hasDerivAt_eq_zero (hasDerivAt_variationalPotential hW hβ _ t)
  exact neg_eq_zero.mp hh

lemma minimizingParisi_one_not_mem_support (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ) :
    (⟨1,by simp⟩ : OrderPoint)∉(ρ:Measure OrderPoint).support := by
  intro ht
  let c := ofMeasure β ρ
  have hl : IsLocalMinOn (variationalPotential P W hβ c) (Icc (0:ℝ) 1) 1 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact minimizingParisi_support_potential hW hβ hρ ht ⟨s,hs⟩
  have htang : (-1:ℝ)∈posTangentConeAt (Icc (0:ℝ) 1) 1 := by
    have hh := sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0:ℝ) 1).segment_subset (show (1:ℝ)∈Icc (0:ℝ) 1 by simp)
        (show (0:ℝ)∈Icc (0:ℝ) 1 by simp))
    simpa using hh
  have hh := hl.hasFDerivWithinAt_nonneg
    (hasDerivAt_variationalPotential hW hβ c 1).hasFDerivAt.hasFDerivWithinAt htang
  have he := expectedProduct_one_lt hW hβ c
  have hh' : 1≤expectedProduct P W c c (c.driftData hβ) 1 := by
    simpa [ContinuousLinearMap.smulRight_apply,smul_eq_mul,deviation] using hh
  exact (not_lt_of_ge hh') he

 

theorem minimizingParisi_selfConsistency (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {t : OrderPoint} (ht : t∈(ρ:Measure OrderPoint).support) :
    expectedProduct P W (ofMeasure β ρ) (ofMeasure β ρ) ((ofMeasure β ρ).driftData hβ) t=t := by
  by_cases h0 : (t:ℝ)=0
  · rw [h0]
    exact expectedProduct_zero hW hβ _
  by_cases h1 : (t:ℝ)=1
  · have he : t=(⟨1,by simp⟩ : OrderPoint) := Subtype.ext h1
    exact (minimizingParisi_one_not_mem_support hW hβ hρ (he ▸ ht)).elim
  exact sub_eq_zero.mp (minimizingParisi_deviation_interior hW hβ hρ ht
    (lt_of_le_of_ne t.property.1 (Ne.symm h0)) (lt_of_le_of_ne t.property.2 h1))

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath
namespace BoundedCoefficient
variable {β : ℝ≥0}

def curvature (c : BoundedCoefficient β) (X : Path) (t : ℝ) : ℝ :=
  fieldCurvature β c.val (Real.toNNReal (projIcc 0 1 zero_le_one t)) (extend X t)

lemma curvature_eq (c : BoundedCoefficient β) (X : Path) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    c.curvature X t=fieldCurvature β c.val (Real.toNNReal t) (extend X t) := by
  simp only [curvature,projIcc_of_mem zero_le_one ht]

lemma continuous_curvature (c : BoundedCoefficient β) (hβ : 0<β) (X : Path) :
    Continuous (c.curvature X) := by
  change Continuous ((fun q : OrderPoint × ℝ => fieldCurvature β c.val (Real.toNNReal q.1) q.2) ∘
    (fun t => (projIcc (0:ℝ) 1 zero_le_one t,extend X t)))
  exact (continuous_fieldCurvature_joint β hβ c.mono c.bound).comp
    ((show Continuous (projIcc (0:ℝ) 1 zero_le_one) from continuous_projIcc).prodMk (continuous_extend X))

lemma norm_curvature_le (c : BoundedCoefficient β) (hβ : 0<β) (X : Path) (t : ℝ) :
    ‖c.curvature X t‖≤β := fieldCurvature_abs β hβ c.mono c.bound _ _

lemma curvature_pos (c : BoundedCoefficient β) (hβ : 0<β) (X : Path) (t : ℝ) :
    0<c.curvature X t := (fieldCurvature_bounds β hβ c.mono c.bound _ _).1

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {K M : ℝ≥0}

lemma curvature_aestronglyMeasurable (hW : IsBrownianReal W P) (c : BoundedCoefficient β)
    (hβ : 0<β) (b : Drift K M) (t : ℝ) :
    AEStronglyMeasurable (fun ω => c.curvature (solution b (brownianPath W ω)) t) P := by
  exact ((fieldCurvature_lipschitz β hβ c.mono c.bound _).continuous.measurable.comp_aemeasurable
    (aemeasurable_solution_eval b (brownianPath W) (brownianPath_aemeasurable_eval hW)
      (projIcc 0 1 zero_le_one t))).aestronglyMeasurable

lemma curvature_square_integrable (hW : IsBrownianReal W P) (c : BoundedCoefficient β)
    (hβ : 0<β) (b : Drift K M) (t : ℝ) :
    Integrable (fun ω => (c.curvature (solution b (brownianPath W ω)) t)^2) P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine Integrable.of_bound ((c.curvature_aestronglyMeasurable hW hβ b t).pow 2) ((β:ℝ)^2) ?_
  filter_upwards [] with ω
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (c.norm_curvature_le hβ _ t) 2

def expectedSquareCurvature (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (c : BoundedCoefficient β) (hβ : 0<β) (t : ℝ) : ℝ :=
  ∫ ω,(c.curvature (solution (c.driftData hβ) (brownianPath W ω)) t)^2 ∂P

lemma expectedSquareCurvature_continuous (hW : IsBrownianReal W P)
    (c : BoundedCoefficient β) (hβ : 0<β) : Continuous (c.expectedSquareCurvature P W hβ) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  apply continuous_of_dominated (bound := fun _ => (β:ℝ)^2)
    (fun t => (curvature_square_integrable hW c hβ _ t).aestronglyMeasurable)
    (fun t => ae_of_all _ fun ω => ?_) (integrable_const _)
    (ae_of_all _ fun ω => (c.continuous_curvature hβ _).pow 2)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (c.norm_curvature_le hβ _ t) 2

lemma spin_mean_square_evolution (hW : IsBrownianReal W P)
    (hβ : 0<β) (c : BoundedCoefficient β) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    expectedProduct P W c c (c.driftData hβ) t=
      ∫ s in (0:ℝ)..t,c.expectedSquareCurvature P W hβ s := by
  let r := Real.toNNReal t
  have hr0 : r≠0 := ne_of_gt (Real.toNNReal_pos.mpr ht.1)
  have hrt : (r:ℝ)=t := Real.coe_toNNReal _ ht.1.le
  have hr1 : r<1 := by exact_mod_cast (show (r:ℝ)<1 by rw [hrt];exact ht.2)
  have hh := canonical_square_verification hW (c.driftData hβ) (c.drift_joint_ae_continuous hβ)
    β hβ c.mono c.bound r hr0 hr1
  rw [fieldGradient_zero β hβ c.mono c.bound,zero_pow (by norm_num : 2≠0),sub_zero] at hh
  have hterm : (∫ ω,(fieldGradient β c.val r
      (solution (c.driftData hβ) (brownianPath W ω) ⟨r,r.coe_nonneg,by exact_mod_cast hr1.le⟩))^2 ∂P)=
      expectedProduct P W c c (c.driftData hβ) t := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [spin_eq _ _ _ ⟨ht.1.le,ht.2.le⟩,extend_of_mem _ ⟨ht.1.le,ht.2.le⟩]
    rw [pow_two]
    have he : (⟨r,r.coe_nonneg,by exact_mod_cast hr1.le⟩ : Icc (0:ℝ) 1)=⟨t,ht.1.le,ht.2.le⟩ := Subtype.ext hrt
    rw [he]
  rw [hterm,hrt] at hh
  rw [hh]
  apply intervalIntegral.integral_congr_Ioo_of_le ht.1.le
  intro s hs
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [curvature_eq _ _ _ ⟨hs.1.le,hs.2.le.trans ht.2.le⟩]
  dsimp only [squareKernel,driftData,drift,BoundedCoefficient.real]
  ring

lemma hasDerivAt_expectedProduct_self (hW : IsBrownianReal W P)
    (hβ : 0<β) (c : BoundedCoefficient β) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (expectedProduct P W c c (c.driftData hβ))
      (c.expectedSquareCurvature P W hβ t) t := by
  have hc := c.expectedSquareCurvature_continuous hW hβ
  have hh := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact spin_mean_square_evolution hW hβ c s hs

end BoundedCoefficient
end ParisiFinite

end

end OAI
