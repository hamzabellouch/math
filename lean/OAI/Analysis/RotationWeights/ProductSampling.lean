import OAI.Analysis.RotationWeights.Discrepancy

namespace OAI

noncomputable section

universe uΩ uι uκ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate

namespace ContinuousCircleWeight.Sampling

lemma phasePairLaw_fst_ac {a b c d : ℝ} (hab : a<b) (hc : 0<c) :
    Measure.map Prod.fst (phasePairLaw a b c d) ≪ (volume : Measure CircleX) := by
  let := phasePairLaw_probability hab c d
  apply Measure.AbsolutelyContinuous.mk
  intro A hA h0
  rw [Measure.map_apply measurable_fst hA]
  apply (measureReal_eq_zero_iff (by finiteness)).mp
  apply le_antisymm _ measureReal_nonneg
  have h := phasePairLaw_marginal_fst (d := d) hab hc A hA
  simpa [Measure.real,h0] using h

lemma phasePairLaw_snd_ac {a b c d : ℝ} (hab : a<b) (hd : 0<d) :
    Measure.map Prod.snd (phasePairLaw a b c d) ≪ (volume : Measure CircleX) := by
  let := phasePairLaw_probability hab c d
  apply Measure.AbsolutelyContinuous.mk
  intro A hA h0
  rw [Measure.map_apply measurable_snd hA]
  apply (measureReal_eq_zero_iff (by finiteness)).mp
  apply le_antisymm _ measureReal_nonneg
  have h := phasePairLaw_marginal_snd (c := c) hab hd A hA
  simpa [Measure.real,h0] using h

lemma product_weight_discrepancy {a b c d B ε : ℝ} (hab : a<b) (hc : 0<c) (hd : 0<d)
    (hB : 0≤B) {u : CircleX → ℝ} (hu : Measurable u)
    (hu0 : ∀ t, 0≤u t) (huB : ∀ t, u t≤B)
    (harc : ∀ r>0, CircleSampling.IsTwoArcs {t | r<u t})
    (hdisc : ∀ x y : CircleX, ∀ r s : ℝ,
      |(phasePairLaw a b c d).real (Metric.ball x r ×ˢ Metric.ball y s) -
        volume.real (Metric.ball x r)*volume.real (Metric.ball y s)| ≤ ε) :
    |(∫ γ, u ((c*γ : ℝ) : CircleX)*u ((d*γ : ℝ) : CircleX) ∂intervalLaw a b) -
      (∫ t, u t)^2| ≤ 4*B^2*ε := by
  let := phasePairLaw_probability hab c d
  let μ := phasePairLaw a b c d
  let ν := (volume : Measure CircleX).prod (volume : Measure CircleX)
  have hν1 : Measure.map Prod.fst ν ≪ (volume : Measure CircleX) := by
    dsimp [ν]
    rw [Measure.map_fst_prod,measure_univ,one_smul]
  have hν2 : Measure.map Prod.snd ν ≪ (volume : Measure CircleX) := by
    dsimp [ν]
    rw [Measure.map_snd_prod,measure_univ,one_smul]
  have h := CircleSampling.superlevel_discrepancy (μ := μ) (ν := ν) hB
    (hu.comp measurable_fst) (hu.comp measurable_snd)
    (fun z ↦ hu0 z.1) (fun z ↦ huB z.1) (fun z ↦ hu0 z.2) (fun z ↦ huB z.2)
    (ε := 4*ε) (by
      intro r hr s hs
      change |μ.real ({t | r<u t} ×ˢ {t | s<u t}) -
        ν.real ({t | r<u t} ×ˢ {t | s<u t})| ≤ _
      apply CircleSampling.twoArcs_rectangle_discrepancy (phasePairLaw_fst_ac hab hc)
        (phasePairLaw_snd_ac hab hd) hν1 hν2 ?_ (harc r hr.1) (harc s hs.1)
      intro x y r s
      simpa only [ν,Measure.real,Measure.prod_prod,ENNReal.toReal_mul] using hdisc x y r s)
  have hμ : (∫ z, u z.1*u z.2 ∂μ) =
      ∫ γ, u ((c*γ : ℝ) : CircleX)*u ((d*γ : ℝ) : CircleX) ∂intervalLaw a b := by
    apply integral_phasePairLaw
    exact ((hu.comp measurable_fst).mul (hu.comp measurable_snd)).aestronglyMeasurable
  have hν : (∫ z, u z.1*u z.2 ∂ν)=(∫ t, u t)^2 := by
    rw [show (∫ z, u z.1*u z.2 ∂ν)=(∫ t, u t)*(∫ t, u t) from integral_prod_mul u u]
    ring
  change |(∫ z, u z.1*u z.2 ∂μ) - (∫ z, u z.1*u z.2 ∂ν)| ≤ B^2*(4*ε) at h
  rw [hμ,hν] at h
  convert! h using 1; ring

end ContinuousCircleWeight.Sampling

namespace CircleSampling
open ContinuousCircleWeight.Sampling

def orientedWeight (positive : Bool) (ℓ α : ℝ) (s t : CircleX) : ℝ :=
  if positive then uPos ℓ α s t else uNeg ℓ α s t

lemma measurable_orientedWeight (positive : Bool) (ℓ α : ℝ) :
    Measurable (Function.uncurry (orientedWeight positive ℓ α)) := by
  cases positive <;> first | exact measurable_uNeg ℓ α | exact measurable_uPos ℓ α

lemma orientedWeight_bounds (positive : Bool) {ℓ α : ℝ} (hℓ : 0<ℓ) (hα : 0<α)
    (s t : CircleX) : 0≤orientedWeight positive ℓ α s t ∧
      orientedWeight positive ℓ α s t≤1/(ℓ*α) := by
  cases positive <;> exact weight_bounds hℓ hα _ _

lemma orientedWeight_isTwoArcs (positive : Bool) {ℓ α r : ℝ} (hℓ : 0<ℓ)
    (hℓ1 : ℓ<1) (hα : 0<α) (s : CircleX) (hr : 0<r) :
    IsTwoArcs {t | r<orientedWeight positive ℓ α s t} := by
  cases positive
  · exact uNeg_isTwoArcs hℓ hℓ1 hα hr s
  · exact uPos_isTwoArcs hℓ hℓ1 hα hr s

lemma orientedWeight_mean (positive : Bool) {ℓ α : ℝ} (hℓ : 0<ℓ)
    (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2) :
    (∫ s : CircleX, ∫ t : CircleX, orientedWeight positive ℓ α s t)=1-2*α := by
  cases positive
  · exact integral_uNeg hℓ hℓ1 hα hα2
  · exact integral_uPos hℓ hℓ1 hα hα2

lemma orientedWeight_sq (positive : Bool) {ℓ α : ℝ} (hℓ : 0<ℓ)
    (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2) :
    (∫ s : CircleX, ∫ t : CircleX, (orientedWeight positive ℓ α s t)^2)=
      (2/ℓ)*Real.log (1/(2*α)) := by
  cases positive
  · exact integral_uNeg_sq hℓ hℓ1 hα hα2
  · exact integral_uPos_sq hℓ hℓ1 hα hα2

lemma orientedWeight_mean_sq (positive : Bool) {ℓ α : ℝ} (hℓ : 0<ℓ)
    (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2) :
    (∫ s : CircleX, (∫ t : CircleX, orientedWeight positive ℓ α s t)^2) ≤
      1+(2*ℓ/(1-ℓ))^2+2*(1+ℓ)*α := by
  cases positive
  · exact integral_uNeg_mean_sq hℓ hℓ1 hα hα2
  · have he : (fun s : CircleX ↦ (∫ t : CircleX, uPos ℓ α s t)^2)=
        (fun s : CircleX ↦ ∫ t : CircleX, uPos ℓ α s t) := by
      ext s
      rw [uPos_integral_t hℓ hℓ1 hα]
      split_ifs <;> norm_num
    change (∫ s : CircleX, (∫ t : CircleX, uPos ℓ α s t)^2) ≤ _
    rw [he,integral_uPos hℓ hℓ1 hα hα2]
    nlinarith [sq_nonneg (2*ℓ/(1-ℓ))]

lemma bounded_integrable {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {B : ℝ}
    (hb : ∀ x, 0≤f x ∧ f x≤B) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable B
  exact ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hb x).1]; exact (hb x).2

lemma bounded_sq_integrable {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {B : ℝ}
    (hb : ∀ x, 0≤f x ∧ f x≤B) : Integrable (fun x ↦ (f x)^2) μ := by
  apply bounded_integrable μ (hf.pow_const 2)
  exact fun x ↦ ⟨sq_nonneg _,pow_le_pow_left₀ (hb x).1 (hb x).2 2⟩

lemma bounded_pair_integrable {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) {B : ℝ}
    (hB : 0≤B) (hfb : ∀ x, 0≤f x ∧ f x≤B) (hgb : ∀ x, 0≤g x ∧ g x≤B) :
    Integrable (fun x ↦ f x*g x) μ := by
  apply bounded_integrable μ (hf.mul hg)
  exact fun x ↦ ⟨mul_nonneg (hfb x).1 (hgb x).1,
    (mul_le_mul (hfb x).2 (hgb x).2 (hgb x).1 hB).trans_eq (pow_two B).symm⟩

lemma trial_mean_lower {a b c ℓ α A : ℝ} (hab : a<b) (hc : 0<c)
    (hℓ : 0<ℓ) (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2)
    (positive : Bool) (hA : A≤1-1/(c*(b-a))) :
    A*(1-2*α) ≤ ∫ z : CircleX × ℝ,
      orientedWeight positive ℓ α z.1 ((c*z.2 : ℝ) : CircleX)
      ∂(volume.prod (intervalLaw a b)) := by
  let := intervalLaw_probability hab
  let u := orientedWeight positive ℓ α
  have hm : Measurable (Function.uncurry u) := measurable_orientedWeight positive ℓ α
  have hb := orientedWeight_bounds positive hℓ hα
  have htrial : Measurable (fun z : CircleX × ℝ ↦ u z.1 ((c*z.2 : ℝ) : CircleX)) :=
    hm.comp (measurable_fst.prodMk ((AddCircle.continuous_mk' 1).measurable.comp (measurable_const.mul measurable_snd)))
  have hit := bounded_integrable (volume.prod (intervalLaw a b)) htrial
    (fun z ↦ hb z.1 _)
  have hiu := bounded_integrable (volume.prod volume) hm (fun z ↦ hb z.1 z.2)
  rw [integral_prod _ hit]
  have hle (s : CircleX) : A*(∫ t : CircleX, u s t) ≤
      ∫ γ, u s ((c*γ : ℝ) : CircleX) ∂intervalLaw a b := by
    have hm' : Measurable (u s) := hm.comp (measurable_const.prodMk measurable_id)
    have hnon : 0≤∫ t : CircleX, u s t := integral_nonneg fun t ↦ (hb s t).1
    exact (mul_le_mul_of_nonneg_right hA hnon).trans
      (circle_scaled_integral_bounds (bounded_integrable volume hm' (hb s))
        (fun t ↦ (hb s t).1) hab hc).1
  have h := integral_mono (hiu.integral_prod_left.const_mul A) hit.integral_prod_left hle
  dsimp only [Function.uncurry,u] at h
  rw [integral_const_mul,orientedWeight_mean positive hℓ hℓ1 hα hα2] at h
  exact h

lemma trial_sq_upper {a b c ℓ α D : ℝ} (hab : a<b) (hc : 0<c)
    (hℓ : 0<ℓ) (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2)
    (positive : Bool) (hD : 1+1/(c*(b-a))≤D) :
    (∫ z : CircleX × ℝ, (orientedWeight positive ℓ α z.1 ((c*z.2 : ℝ) : CircleX))^2
      ∂(volume.prod (intervalLaw a b))) ≤ D*((2/ℓ)*Real.log (1/(2*α))) := by
  let := intervalLaw_probability hab
  let u := orientedWeight positive ℓ α
  have hm : Measurable (Function.uncurry u) := measurable_orientedWeight positive ℓ α
  have hb := orientedWeight_bounds positive hℓ hα
  have htrial : Measurable (fun z : CircleX × ℝ ↦ u z.1 ((c*z.2 : ℝ) : CircleX)) :=
    hm.comp (measurable_fst.prodMk ((AddCircle.continuous_mk' 1).measurable.comp (measurable_const.mul measurable_snd)))
  have hit := bounded_sq_integrable (volume.prod (intervalLaw a b)) htrial (fun z ↦ hb z.1 _)
  have hiu := bounded_sq_integrable (volume.prod volume) hm (fun z ↦ hb z.1 z.2)
  rw [integral_prod _ hit]
  have hle (s : CircleX) : (∫ γ, (u s ((c*γ : ℝ) : CircleX))^2 ∂intervalLaw a b) ≤
      D*(∫ t : CircleX, (u s t)^2) := by
    have hm' : Measurable (u s) := hm.comp (measurable_const.prodMk measurable_id)
    have hnon : 0≤∫ t : CircleX, (u s t)^2 := integral_nonneg fun t ↦ sq_nonneg _
    exact (circle_scaled_integral_bounds (bounded_sq_integrable volume hm' (hb s))
      (fun t ↦ sq_nonneg _) hab hc).2.trans (mul_le_mul_of_nonneg_right hD hnon)
  have h := integral_mono hit.integral_prod_left (hiu.integral_prod_left.const_mul D) hle
  dsimp only [Function.uncurry,u] at h
  rw [integral_const_mul,orientedWeight_sq positive hℓ hℓ1 hα hα2] at h
  exact h

lemma trial_pair_upper {a b c d ℓ α ε : ℝ} (hab : a<b) (hc : 0<c) (hd : 0<d)
    (hℓ : 0<ℓ) (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2)
    (positive : Bool)
    (hdisc : ∀ x y : CircleX, ∀ r s : ℝ,
      |(phasePairLaw a b c d).real (Metric.ball x r ×ˢ Metric.ball y s) -
        volume.real (Metric.ball x r)*volume.real (Metric.ball y s)| ≤ ε) :
    (∫ z : CircleX × ℝ,
      orientedWeight positive ℓ α z.1 ((c*z.2 : ℝ) : CircleX)*
      orientedWeight positive ℓ α z.1 ((d*z.2 : ℝ) : CircleX)
      ∂(volume.prod (intervalLaw a b))) ≤
      1+(2*ℓ/(1-ℓ))^2+2*(1+ℓ)*α+4*(1/(ℓ*α))^2*ε := by
  let := intervalLaw_probability hab
  let u := orientedWeight positive ℓ α
  have hm : Measurable (Function.uncurry u) := measurable_orientedWeight positive ℓ α
  have hb := orientedWeight_bounds positive hℓ hα
  have hB : 0≤1/(ℓ*α) := by positivity
  have htrial (c : ℝ) : Measurable (fun z : CircleX × ℝ ↦ u z.1 ((c*z.2 : ℝ) : CircleX)) :=
    hm.comp (measurable_fst.prodMk ((AddCircle.continuous_mk' 1).measurable.comp (measurable_const.mul measurable_snd)))
  have hit := bounded_pair_integrable (volume.prod (intervalLaw a b)) (htrial c) (htrial d) hB
    (fun z ↦ hb z.1 _) (fun z ↦ hb z.1 _)
  have hiu := bounded_integrable (volume.prod volume) hm (fun z ↦ hb z.1 z.2)
  have hmean : ∀ s : CircleX, 0≤(∫ t : CircleX, u s t) ∧ (∫ t : CircleX, u s t)≤1/(ℓ*α) := by
    intro s
    refine ⟨integral_nonneg (fun t ↦ (hb s t).1),?_⟩
    have h := integral_mono (bounded_integrable volume (hm.comp (measurable_const.prodMk measurable_id)) (hb s))
      (integrable_const (1/(ℓ*α))) (fun t ↦ (hb s t).2)
    simpa using h
  have hig : Integrable (fun s : CircleX ↦ (∫ t : CircleX, u s t)^2) volume := by
    apply Integrable.of_bound (hiu.integral_prod_left.aestronglyMeasurable.pow 2) ((1/(ℓ*α))^2)
    exact ae_of_all _ fun s ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hmean s).1 (hmean s).2 2
  rw [integral_prod _ hit]
  have hle (s : CircleX) : (∫ γ, u s ((c*γ : ℝ) : CircleX)*u s ((d*γ : ℝ) : CircleX) ∂intervalLaw a b) ≤
      (∫ t : CircleX, u s t)^2+4*(1/(ℓ*α))^2*ε := by
    have h := product_weight_discrepancy hab hc hd hB (hm.comp (measurable_const.prodMk measurable_id))
      (fun t ↦ (hb s t).1) (fun t ↦ (hb s t).2)
      (fun r hr ↦ orientedWeight_isTwoArcs positive hℓ hℓ1 hα s hr) hdisc
    have := (abs_le.mp h).2
    dsimp only [Function.comp_apply,Function.uncurry_apply_pair,id_eq] at this
    linarith
  have h := integral_mono hit.integral_prod_left (hig.add (integrable_const _)) hle
  dsimp only [Pi.add_apply] at h
  rw [integral_add hig (integrable_const _)] at h
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at h
  have hg := orientedWeight_mean_sq positive hℓ hℓ1 hα hα2
  dsimp only [u] at h
  linarith

end CircleSampling

open MeasureTheory Set Filter
open scoped BigOperators ENNReal
namespace CircleSampling

section
variable {ι : Type uι} {κ : Type uκ} {Ω : Type uΩ} [Fintype ι] [Fintype κ] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

def productAverage (u : κ → Ω → ℝ) (z : ι → Ω) : ℝ :=
  (Fintype.card κ : ℝ)⁻¹ * ∑ n, ∏ i, u n (z i)

lemma measurable_productTerm (u : Ω → ℝ) (hu : Measurable u) :
    Measurable (fun z : ι → Ω ↦ ∏ i, u (z i)) := by
  exact Finset.measurable_prod _ fun i _ ↦ hu.comp (measurable_pi_apply i)

lemma integrable_productTerm (u : Ω → ℝ) (hu : Measurable u) (B : ℝ)
    (hB : ∀ x, ‖u x‖≤B) :
    Integrable (fun z : ι → Ω ↦ ∏ i, u (z i)) (Measure.pi (fun _ : ι ↦ μ)) := by
  apply Integrable.of_bound (measurable_productTerm u hu).aestronglyMeasurable (B^(Fintype.card ι))
  apply ae_of_all
  intro z
  simpa only [norm_prod,Finset.prod_const,Finset.card_univ] using
    Finset.prod_le_prod₀ (s := (Finset.univ : Finset ι)) (fun i _ ↦ norm_nonneg (u (z i))) (fun i _ ↦ hB (z i))

lemma integral_productAverage (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) :
    ∫ z, productAverage (ι := ι) u z ∂Measure.pi (fun _ : ι ↦ μ) =
      (Fintype.card κ : ℝ)⁻¹ * ∑ n, (∫ x, u n x ∂μ)^(Fintype.card ι) := by
  unfold productAverage
  rw [integral_const_mul,integral_finsetSum]
  · simp_rw [integral_fintype_prod_eq_pow]
  · intro n _
    exact integrable_productTerm μ (u n) (hu n) B (hB n)

omit [MeasurableSpace Ω] in
lemma productAverage_sq (u : κ → Ω → ℝ) (z : ι → Ω) :
    (productAverage (ι := ι) u z)^2 =
      ((Fintype.card κ : ℝ)⁻¹)^2 * ∑ n, ∑ k, ∏ i, (u n (z i)*u k (z i)) := by
  unfold productAverage
  rw [mul_pow,pow_two (∑ n, ∏ i, u n (z i)),Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.prod_mul_distrib]

lemma integral_productAverage_sq (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) :
    ∫ z, (productAverage (ι := ι) u z)^2 ∂Measure.pi (fun _ : ι ↦ μ) =
      ((Fintype.card κ : ℝ)⁻¹)^2 *
        ∑ n, ∑ k, (∫ x, u n x*u k x ∂μ)^(Fintype.card ι) := by
  simp_rw [productAverage_sq]
  rw [integral_const_mul,integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k _
      exact integral_fintype_prod_eq_pow (fun x ↦ u n x*u k x)
    · intro k _
      apply integrable_productTerm μ _ ((hu n).mul (hu k)) (B^2)
      intro x
      simp only [Pi.mul_apply,norm_mul,pow_two]
      exact mul_le_mul (hB n x) (hB k x) (norm_nonneg _) ((norm_nonneg _).trans (hB n x))
  · intro n _
    apply integrable_finsetSum
    intro k _
    apply integrable_productTerm μ _ ((hu n).mul (hu k)) (B^2)
    intro x
    simp only [Pi.mul_apply,norm_mul,pow_two]
    exact mul_le_mul (hB n x) (hB k x) (norm_nonneg _) ((norm_nonneg _).trans (hB n x))

lemma productAverage_integrable (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) :
    Integrable (productAverage (ι := ι) u) (Measure.pi (fun _ : ι ↦ μ)) := by
  apply Integrable.const_mul
  exact integrable_finsetSum _ fun n _ ↦ integrable_productTerm μ (u n) (hu n) B (hB n)

lemma productAverage_sq_integrable (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) :
    Integrable (fun z ↦ (productAverage (ι := ι) u z)^2) (Measure.pi (fun _ : ι ↦ μ)) := by
  simp_rw [productAverage_sq]
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro n _
  apply integrable_finsetSum
  intro k _
  apply integrable_productTerm μ _ ((hu n).mul (hu k)) (B^2)
  intro x
  simp only [Pi.mul_apply,norm_mul,pow_two]
  exact mul_le_mul (hB n x) (hB k x) (norm_nonneg _) ((norm_nonneg _).trans (hB n x))

lemma productAverage_first_bound [Nonempty κ] (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) (a : ℝ) (ha : 0≤a)
    (hmean : ∀ n, a≤∫ x, u n x ∂μ) :
    a^(Fintype.card ι) ≤ ∫ z, productAverage (ι := ι) u z ∂Measure.pi (fun _ : ι ↦ μ) := by
  rw [integral_productAverage μ u hu B hB]
  have hc : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ _ : κ, a^(Fintype.card ι) ≤ ∑ n : κ, (∫ x, u n x ∂μ)^(Fintype.card ι) :=
    Finset.sum_le_sum fun n _ ↦ pow_le_pow_left₀ ha (hmean n) _
  have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card κ)))
  simpa [Finset.sum_const,Finset.card_univ, nsmul_eq_mul,← mul_assoc,hc] using h

lemma productAverage_second_bound [Nonempty κ] (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) (b c : ℝ) (hb : 0≤b) (_hc : 0≤c)
    (hu0 : ∀ n x, 0≤u n x)
    (hpair : ∀ n k, n≠k → (∫ x, u n x*u k x ∂μ)≤b)
    (hdiag : ∀ n, (∫ x, (u n x)^2 ∂μ)≤c) :
    (∫ z, (productAverage (ι := ι) u z)^2 ∂Measure.pi (fun _ : ι ↦ μ)) ≤
      b^(Fintype.card ι) + (Fintype.card κ : ℝ)⁻¹*c^(Fintype.card ι) := by
  classical
  rw [integral_productAverage_sq μ u hu B hB]
  have hp : ∀ n k, (∫ x, u n x*u k x ∂μ)^(Fintype.card ι) ≤
      b^(Fintype.card ι) + if n=k then c^(Fintype.card ι) else 0 := by
    intro n k
    have hnon : 0≤∫ x, u n x*u k x ∂μ := integral_nonneg fun x ↦ mul_nonneg (hu0 n x) (hu0 k x)
    by_cases h : n=k
    · subst k
      simp only [ite_true]
      have hle := pow_le_pow_left₀ hnon (show (∫ x, u n x*u n x ∂μ)≤c by simpa [pow_two] using hdiag n) (Fintype.card ι)
      exact hle.trans (le_add_of_nonneg_left (pow_nonneg hb _))
    · simpa only [ite_eq_right h,add_zero] using pow_le_pow_left₀ hnon (hpair n k h) (Fintype.card ι)
  have hs : (∑ n : κ, ∑ k : κ, (∫ x, u n x*u k x ∂μ)^(Fintype.card ι)) ≤
      ∑ n : κ, ∑ k : κ, (b^(Fintype.card ι) + if n=k then c^(Fintype.card ι) else 0) :=
    Finset.sum_le_sum fun n _ ↦ Finset.sum_le_sum fun k _ ↦ hp n k
  have h := mul_le_mul_of_nonneg_left hs (sq_nonneg (Fintype.card κ : ℝ)⁻¹)
  have hcard : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply h.trans_eq
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  field_simp [hcard]

lemma productAverage_error_bound [Nonempty κ] (u : κ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (B : ℝ) (hB : ∀ n x, ‖u n x‖≤B) (a b c : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (hu0 : ∀ n x, 0≤u n x)
    (hmean : ∀ n, a≤∫ x, u n x ∂μ)
    (hpair : ∀ n k, n≠k → (∫ x, u n x*u k x ∂μ)≤b)
    (hdiag : ∀ n, (∫ x, (u n x)^2 ∂μ)≤c) :
    (∫ z, (productAverage (ι := ι) u z-1)^2 ∂Measure.pi (fun _ : ι ↦ μ)) ≤
      b^(Fintype.card ι)+(Fintype.card κ : ℝ)⁻¹*c^(Fintype.card ι)-2*a^(Fintype.card ι)+1 := by
  have h1 := productAverage_first_bound (ι := ι) μ u hu B hB a ha hmean
  have h2 := productAverage_second_bound (ι := ι) μ u hu B hB b c hb hc hu0 hpair hdiag
  have hi := productAverage_integrable (ι := ι) μ u hu B hB
  have hi2 := productAverage_sq_integrable (ι := ι) μ u hu B hB
  have he : (fun z : ι → Ω ↦ (productAverage u z-1)^2) =
      (fun z ↦ ((productAverage u z)^2-2*productAverage u z)+1) := by funext z; ring
  rw [he]
  have hsub : Integrable (fun z : ι → Ω ↦ (productAverage u z)^2-2*productAverage u z) (Measure.pi (fun _ : ι ↦ μ)) := hi2.sub (hi.const_mul 2)
  rw [integral_add hsub (integrable_const 1)]
  have hmul : Integrable (fun z : ι → Ω ↦ 2*productAverage u z) (Measure.pi (fun _ : ι ↦ μ)) := hi.const_mul 2
  rw [integral_sub hi2 hmul,integral_const_mul]
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul]
  linarith
end
open ContinuousCircleWeight.Sampling
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]

def idealAverage (positive : Bool) (ℓ α : ℝ) (c : κ → ℝ) (s : ι → CircleX) (γ : ι → ℝ) : ℝ :=
  (Fintype.card κ : ℝ)⁻¹ * ∑ n, ∏ i, orientedWeight positive ℓ α (s i) ((c n*γ i : ℝ) : CircleX)

lemma ideal_error_bound {a b ℓ α A D ε : ℝ} (hab : a<b)
    (hℓ : 0<ℓ) (hℓ1 : ℓ<1) (hα : 0<α) (hα2 : α≤1/2)
    (hA : 0≤A) (hD : 0≤D) (hε : 0≤ε) (positive : Bool) (c : κ → ℝ)
    (hc : ∀ n, 0<c n) (hA' : ∀ n, A≤1-1/(c n*(b-a)))
    (hD' : ∀ n, 1+1/(c n*(b-a))≤D)
    (hdisc : ∀ n k, n≠k → ∀ x y : CircleX, ∀ r s : ℝ,
      |(phasePairLaw a b (c n) (c k)).real (Metric.ball x r ×ˢ Metric.ball y s) -
        volume.real (Metric.ball x r)*volume.real (Metric.ball y s)| ≤ ε) :
    (∫ γ : ι → ℝ, ∫ s : ι → CircleX,
      (idealAverage positive ℓ α c s γ-1)^2 ∂Measure.pi (fun _ ↦ volume)
      ∂Measure.pi (fun _ ↦ intervalLaw a b)) ≤
      (1+(2*ℓ/(1-ℓ))^2+2*(1+ℓ)*α+4*(1/(ℓ*α))^2*ε)^(Fintype.card ι) +
      (Fintype.card κ : ℝ)⁻¹*(D*((2/ℓ)*Real.log (1/(2*α))))^(Fintype.card ι) -
      2*(A*(1-2*α))^(Fintype.card ι)+1 := by
  let := intervalLaw_probability hab
  let μ := (volume : Measure CircleX).prod (intervalLaw a b)
  let u := fun n (z : CircleX × ℝ) ↦ orientedWeight positive ℓ α z.1 ((c n*z.2 : ℝ) : CircleX)
  have hu (n : κ) : Measurable (u n) :=
    (measurable_orientedWeight positive ℓ α).comp
      (measurable_fst.prodMk ((AddCircle.continuous_mk' 1).measurable.comp (measurable_const.mul measurable_snd)))
  have hu0 (n : κ) (z) : 0≤u n z := (orientedWeight_bounds positive hℓ hα _ _).1
  have huB (n : κ) (z) : ‖u n z‖≤1/(ℓ*α) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hu0 n z)]
    exact (orientedWeight_bounds positive hℓ hα _ _).2
  have hdiag0 : 0≤D*((2/ℓ)*Real.log (1/(2*α))) := by
    apply mul_nonneg hD
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    exact (le_div_iff₀ (by positivity)).mpr (by linarith)
  have h := productAverage_error_bound (ι := ι) μ u hu (1/(ℓ*α)) huB
    (A*(1-2*α)) (1+(2*ℓ/(1-ℓ))^2+2*(1+ℓ)*α+4*(1/(ℓ*α))^2*ε)
    (D*((2/ℓ)*Real.log (1/(2*α)))) (mul_nonneg hA (by linarith)) (by positivity) hdiag0 hu0
    (fun n ↦ trial_mean_lower hab (hc n) hℓ hℓ1 hα hα2 positive (hA' n))
    (fun n k hnk ↦ trial_pair_upper hab (hc n) (hc k) hℓ hℓ1 hα hα2 positive (hdisc n k hnk))
    (fun n ↦ trial_sq_upper hab (hc n) hℓ hℓ1 hα hα2 positive (hD' n))
  have hi := productAverage_integrable (ι := ι) μ u hu (1/(ℓ*α)) huB
  have hi2 := productAverage_sq_integrable (ι := ι) μ u hu (1/(ℓ*α)) huB
  have herror : Integrable (fun z : ι → CircleX × ℝ ↦ (productAverage u z-1)^2)
      (Measure.pi (fun _ : ι ↦ μ)) := by
    have heq : (fun z : ι → CircleX × ℝ ↦ (productAverage u z-1)^2) =
        (fun z ↦ productAverage u z ^ 2 - 2 * productAverage u z + 1) := by funext z; ring
    rw [heq]
    exact (hi2.sub (hi.const_mul 2)).add (integrable_const 1)
  let e := MeasurableEquiv.arrowProdEquivProdArrow CircleX ℝ ι
  have he := measurePreserving_arrowProdEquivProdArrow CircleX ℝ ι
    (fun _ ↦ volume) (fun _ ↦ intervalLaw a b)
  have he' := MeasurePreserving.symm e he
  have hf : (fun z : (ι → CircleX)×(ι → ℝ) ↦ (idealAverage positive ℓ α c z.1 z.2-1)^2) =
      (fun z ↦ (productAverage u (e.symm z)-1)^2) := rfl
  have hif : Integrable (fun z : (ι → CircleX)×(ι → ℝ) ↦ (idealAverage positive ℓ α c z.1 z.2-1)^2)
      ((Measure.pi (fun _ : ι ↦ (volume : Measure CircleX))).prod (Measure.pi (fun _ : ι ↦ intervalLaw a b))) := by
    rw [hf]
    exact he'.integrable_comp_of_integrable herror
  have hint := he'.integral_comp e.symm.measurableEmbedding (fun z ↦ (productAverage (ι := ι) u z-1)^2)
  rw [← hint] at h
  change (∫ z : (ι → CircleX)×(ι → ℝ), (idealAverage positive ℓ α c z.1 z.2-1)^2
    ∂((Measure.pi (fun _ : ι ↦ (volume : Measure CircleX))).prod (Measure.pi (fun _ : ι ↦ intervalLaw a b)))) ≤ _ at h
  rw [integral_prod_symm _ hif] at h
  exact h

end CircleSampling

end

end OAI
