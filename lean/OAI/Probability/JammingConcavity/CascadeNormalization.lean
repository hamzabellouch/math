import Mathlib
import OAI.Probability.JammingConcavity.GaussianColeHopf

namespace OAI

/-! Cascade Normalization. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def CascadeTree : ℕ → Type
  | 0 => Unit
  | k+1 => PointCloud (CascadeTree k)

instance cascadeTreeMeasurable : (k : ℕ) → MeasurableSpace (CascadeTree k)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | k+1 => by
    letI := cascadeTreeMeasurable k
    exact inferInstanceAs (MeasurableSpace (PointCloud (CascadeTree k)))

def cascadeLaw : (ms : List ℝ) → Measure (CascadeTree ms.length)
  | [] => Measure.dirac ()
  | _::ms => pointCloudLaw (cascadeLaw ms)

def cascadeTotal : (ms : List ℝ) → CascadeTree ms.length → ℝ≥0∞
  | [], _ => 1
  | m::ms, ω => pointCloudFunctional
      (fun z => ENNReal.ofReal (z.1 ^ (-1/m)) * cascadeTotal ms z.2) ω

def CascadeNormalizationStatement : Prop :=
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
    (∀ᵐ ω ∂cascadeLaw ms, 0 < cascadeTotal ms ω ∧ cascadeTotal ms ω < ∞) ∧
    Integrable (fun ω => |Real.log (cascadeTotal ms ω).toReal|^2) (cascadeLaw ms)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def mapPoissonBin {X Y : Type*} (f : X → Y) (z : PoissonBin X) : PoissonBin Y :=
  (z.1, fun j => f (z.2 j))

lemma measurable_mapPoissonBin {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : Measurable f) : Measurable (mapPoissonBin f) := by
  apply measurable_fst.prodMk
  exact Measurable.of_eval fun index => hf.comp ((measurable_pi_apply index).comp measurable_snd)

lemma poissonBinLaw_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν] {f : X → Y} (hf : Measurable f) :
    (poissonBinLaw ν).map (mapPoissonBin f) = poissonBinLaw (ν.map f) := by
  unfold poissonBinLaw mapPoissonBin
  change Measure.map (Prod.map id (fun (z : ℕ → X) (j : ℕ) => f (z j))) _ = _
  rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
    Measure.infinitePi_map_pi (fun _ : ℕ => ν) (fun _ => hf)]

lemma poissonSeriesLaw_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν] {f : X → Y} (hf : Measurable f) :
    (poissonSeriesLaw ν).map (fun ω n => mapPoissonBin f (ω n)) =
      poissonSeriesLaw (ν.map f) := by
  unfold poissonSeriesLaw
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => poissonBinLaw ν) (fun _ => measurable_mapPoissonBin hf)]
  simp_rw [poissonBinLaw_map ν hf]

def mapPointCloud {A B : Type*} (f : A → B) (ω : PointCloud A) : PointCloud B :=
  fun n => mapPoissonBin (Prod.map id f) (ω n)

lemma measurable_mapPointCloud {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {f : A → B} (hf : Measurable f) : Measurable (mapPointCloud f) := by
  apply Measurable.of_eval
  intro n
  exact (measurable_mapPoissonBin (measurable_id.prodMap hf)).comp (measurable_pi_apply n)

lemma pointCloudLaw_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure A) [IsProbabilityMeasure ν] {f : A → B} (hf : Measurable f) :
    (pointCloudLaw ν).map (mapPointCloud f) = pointCloudLaw (ν.map f) := by
  unfold pointCloudLaw mapPointCloud
  rw [poissonSeriesLaw_map _ (measurable_id.prodMap hf),
    ← Measure.map_prod_map _ _ measurable_id hf, Measure.map_id]
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma integrable_one_sub_expNeg {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {F : X → ℝ≥0∞} (hF : Measurable F) :
    Integrable (fun x => 1-expNeg (F x)) μ :=
  (integrable_const 1).sub (integrable_expNeg μ hF)

lemma poisson_series_laplace_general {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (F : ℕ → X → ℝ≥0∞) (hF : ∀ n, Measurable (F n)) :
    (∫ ω, expNeg (∑' n : ℕ, poissonBinSum (F n) (ω n)) ∂poissonSeriesLaw μ) =
      expNeg (∑' n : ℕ, ∫⁻ x, ENNReal.ofReal (1-expNeg (F n x)) ∂μ) := by
  have hnonneg : ∀ n : ℕ, 0 ≤ ∫ x, 1-expNeg (F n x) ∂μ := fun n =>
    integral_nonneg (fun x => sub_nonneg.mpr (expNeg_le_one _))
  have hfinite : ∀ k : ℕ,
      (∫ ω, expNeg (∑ n ∈ Finset.range k, poissonBinSum (F n) (ω n)) ∂poissonSeriesLaw μ) =
      expNeg (∑ n ∈ Finset.range k, ∫⁻ x, ENNReal.ofReal (1-expNeg (F n x)) ∂μ) := by
    intro k
    simp only [expNeg_sum, poissonSeriesLaw]
    rw [iid_prefix_product_varying (poissonBinLaw μ)
      (fun n z => expNeg (poissonBinSum (F n) z))
      (fun n => continuous_expNeg.measurable.comp (measurable_poissonBinSum (hF n)))]
    apply Finset.prod_congr rfl
    intro n hn
    rw [poissonBin_laplace μ (hF n)]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_one_sub_expNeg μ (hF n))
      (Filter.Eventually.of_forall fun x => sub_nonneg.mpr (expNeg_le_one _)),
      expNeg_ofReal (hnonneg n)]
  have h₁ := integral_expNeg_tsum (poissonSeriesLaw μ)
    (fun n ω => poissonBinSum (F n) (ω n))
    (fun n => (measurable_poissonBinSum (hF n)).comp (measurable_pi_apply n))
  have h₂ := continuous_expNeg.continuousAt.tendsto.comp
    (ENNReal.tendsto_nat_tsum (fun n => ∫⁻ x, ENNReal.ofReal (1-expNeg (F n x)) ∂μ))
  exact tendsto_nhds_unique h₁ (h₂.congr (fun k => (hfinite k).symm))
end MicroscopicJamming

 
 
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming
lemma lintegral_unit_shift {f : ℝ → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    (∫⁻ u in Ico (0:ℝ) 1, f ((n:ℝ)+u)) = ∫⁻ x in Ioc (n:ℝ) ((n:ℝ)+1), f x := by
  rw [restrict_Ico_eq_restrict_Ioc]
  have he : (fun u : ℝ => (n:ℝ)+u) ⁻¹' Ioc (n:ℝ) ((n:ℝ)+1) = Ioc 0 1 := by
    ext u; simp only [mem_preimage, mem_Ioc]; constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [← he, ← setLIntegral_map measurableSet_Ioc hf (by fun_prop),
    MeasureTheory.Measure.IsAddLeftInvariant.map_add_left_eq_self]

lemma tsum_lintegral_unit_shifts {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∑' n : ℕ, ∫⁻ u in Ico (0:ℝ) 1, f ((n:ℝ)+u)) = ∫⁻ x in Ioi 0, f x := by
  simp_rw [lintegral_unit_shift hf]
  rw [← lintegral_iUnion (fun n : ℕ => measurableSet_Ioc) unit_bins_disjoint,
    unit_bins_union]

lemma lintegral_Ioi_div {f : ℝ → ℝ≥0∞} (hf : Measurable f) {c : ℝ} (hc : 0 < c) :
    (∫⁻ x in Ioi (0:ℝ), f (x/c)) = ENNReal.ofReal c * ∫⁻ x in Ioi 0, f x := by
  have he : (fun x : ℝ => x/c) ⁻¹' Ioi (0:ℝ) = Ioi 0 := by
    ext x; simp [div_pos_iff_of_pos_right hc]
  have hm : Measure.map (fun x : ℝ => x/c) volume = ENNReal.ofReal c • volume := by
    simp only [div_eq_mul_inv]
    rw [Real.map_volume_mul_right (inv_ne_zero hc.ne'), inv_inv, abs_of_pos hc]
  conv_lhs => rw [← he, ← setLIntegral_map measurableSet_Ioi hf (by fun_prop), hm,
    Measure.restrict_smul, lintegral_smul_measure]
  rfl
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming
instance pointCloudLaw_probability {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] : IsProbabilityMeasure (pointCloudLaw ν) := by
  unfold pointCloudLaw; infer_instance

lemma measurable_pointCloudFunctional {A : Type*} [MeasurableSpace A]
    {f : ℝ × A → ℝ≥0∞} (hf : Measurable f) : Measurable (pointCloudFunctional f) := by
  unfold pointCloudFunctional
  apply Measurable.tsum
  intro n
  exact (measurable_poissonBinSum (hf.comp (by fun_prop))).comp (measurable_pi_apply n)

lemma pointCloud_laplace {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [IsProbabilityMeasure ν] {f : ℝ × A → ℝ≥0∞} (hf : Measurable f) :
    (∫ ω, expNeg (pointCloudFunctional f ω) ∂pointCloudLaw ν) =
      expNeg (∫⁻ z, ENNReal.ofReal (1-expNeg (f z)) ∂(volume.restrict (Ioi 0)).prod ν) := by
  change (∫ ω, expNeg (∑' n : ℕ, poissonBinSum
    (fun z : ℝ × A => f ((n:ℝ)+z.1,z.2)) (ω n)) ∂poissonSeriesLaw (cloudUniform.prod ν)) = _
  rw [poisson_series_laplace_general]
  · congr 1
    have hg : Measurable (fun z : ℝ × A => ENNReal.ofReal (1-expNeg (f z))) := by
      exact (measurable_const.sub (continuous_expNeg.measurable.comp hf)).ennreal_ofReal
    have hn (n : ℕ) :
        (∫⁻ z, ENNReal.ofReal (1-expNeg (f ((n:ℝ)+z.1,z.2))) ∂cloudUniform.prod ν) =
        ∫⁻ u in Ico (0:ℝ) 1, ∫⁻ a, ENNReal.ofReal (1-expNeg (f ((n:ℝ)+u,a))) ∂ν :=
      lintegral_prod _ ((hg.comp (measurable_fst.const_add (n:ℝ) |>.prodMk measurable_snd)).aemeasurable)
    simp_rw [hn]
    rw [lintegral_prod _ hg.aemeasurable]
    exact tsum_lintegral_unit_shifts hg.lintegral_prod_right'
  · intro n; exact hf.comp (by fun_prop)
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma laplace_ae_ne_top {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {S : Ω → ℝ≥0∞} (hS : Measurable S)
    {c m : ℝ} (hm : 0 < m)
    (hL : ∀ t : ℝ, 0 ≤ t → (∫ ω, expNeg (ENNReal.ofReal t*S ω) ∂μ) =
      Real.exp (-c*t^m)) : ∀ᵐ ω ∂μ, S ω ≠ ∞ := by
  let f : Ω → ℝ := fun ω => if S ω = ∞ then 0 else 1
  have hf : Measurable f := Measurable.ite (hS (measurableSet_singleton ∞)) measurable_const measurable_const
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by unfold f; split_ifs <;> norm_num)
  have hconv : Tendsto (fun n : ℕ => ∫ ω,
      expNeg (ENNReal.ofReal (1/((n:ℝ)+1))*S ω) ∂μ) atTop (𝓝 (∫ ω, f ω ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    · intro n; exact (continuous_expNeg.measurable.comp (by fun_prop)).aestronglyMeasurable
    · exact integrable_const 1
    · intro n; exact Filter.Eventually.of_forall fun _ => expNeg_norm_le _
    · apply Filter.Eventually.of_forall
      intro ω
      have ht : ∀ n : ℕ, 0 < 1/((n:ℝ)+1) := fun _ => by positivity
      by_cases hs : S ω = ∞
      · have he : ∀ n : ℕ, expNeg (ENNReal.ofReal (1/((n:ℝ)+1))*S ω) = 0 := by
          intro n
          rw [hs, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (ht n)).ne', expNeg_top]
        have hfω : f ω = 0 := by simp [f, hs]
        simpa only [he, hfω] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
      · have he : ∀ n : ℕ,
            expNeg (ENNReal.ofReal (1/((n:ℝ)+1))*S ω) =
            Real.exp (-(1/((n:ℝ)+1))*(S ω).toReal) := by
          intro n
          rw [expNeg_eq_of_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs),
            ENNReal.toReal_mul, ENNReal.toReal_ofReal (ht n).le]
          congr 1; ring
        simp_rw [he]
        simpa [f, hs, Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp
          (tendsto_one_div_add_atTop_nhds_zero_nat.neg.mul_const (S ω).toReal)
  have hval : Tendsto (fun n : ℕ => ∫ ω,
      expNeg (ENNReal.ofReal (1/((n:ℝ)+1))*S ω) ∂μ) atTop (𝓝 (1:ℝ)) := by
    have he : ∀ n : ℕ, (∫ ω, expNeg (ENNReal.ofReal (1/((n:ℝ)+1))*S ω) ∂μ) =
        Real.exp (-c*(1/((n:ℝ)+1))^m) := fun n => hL _ (by positivity)
    simp_rw [he]
    have hpow := (Real.continuous_rpow_const hm.le).continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [Real.zero_rpow hm.ne', Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp (hpow.const_mul (-c))
  have heq : (∫ ω, f ω ∂μ) = 1 := tendsto_nhds_unique hconv hval
  have hz : (∫ ω, 1-f ω ∂μ) = 0 := by rw [integral_sub (integrable_const 1) hfi, heq]; simp
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun ω => by change 0 ≤ 1-f ω; unfold f; split_ifs <;> norm_num))
    ((integrable_const 1).sub hfi)).mp hz
  filter_upwards [hae] with ω hω
  by_contra hs
  simp [f, hs] at hω

lemma laplace_real_ae_pos {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (h0 : ∀ ω, 0 ≤ X ω)
    {c m : ℝ} (hc : 0 < c) (hm : 0 < m)
    (hL : ∀ t : ℝ, 0 ≤ t → (∫ ω, Real.exp (-t*X ω) ∂μ) =
      Real.exp (-c*t^m)) : ∀ᵐ ω ∂μ, 0 < X ω := by
  let f : Ω → ℝ := fun ω => if X ω = 0 then 1 else 0
  have hf : Measurable f := Measurable.ite (hX (measurableSet_singleton 0)) measurable_const measurable_const
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by unfold f; split_ifs <;> norm_num)
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hconv : Tendsto (fun n : ℕ => ∫ ω,
      Real.exp (-((n:ℝ)+1)*X ω) ∂μ) atTop (𝓝 (∫ ω, f ω ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    · intro n; fun_prop
    · exact integrable_const 1
    · intro n; apply Filter.Eventually.of_forall
      intro ω
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (h0 ω))
    · apply Filter.Eventually.of_forall
      intro ω
      by_cases hx : X ω = 0
      · simp only [hx, mul_zero, Real.exp_zero, f]
        exact tendsto_const_nhds
      · have hp : 0 < X ω := lt_of_le_of_ne (h0 ω) (Ne.symm hx)
        have hh := Real.tendsto_exp_atBot.comp (hn.const_mul_atTop_of_neg (neg_lt_zero.mpr hp))
        rw [show f ω = 0 by simp [f, hx]]
        convert hh using 1
        funext n; congr 1; ring
  have hval : Tendsto (fun n : ℕ => ∫ ω,
      Real.exp (-((n:ℝ)+1)*X ω) ∂μ) atTop (𝓝 (0:ℝ)) := by
    have he : ∀ n : ℕ, (∫ ω, Real.exp (-((n:ℝ)+1)*X ω) ∂μ) =
        Real.exp (-c*((n:ℝ)+1)^m) := fun n => hL _ (by positivity)
    simp_rw [he]
    exact Real.tendsto_exp_atBot.comp ((tendsto_rpow_atTop hm).comp hn |>.const_mul_atTop_of_neg
      (neg_lt_zero.mpr hc))
  have heq : (∫ ω, f ω ∂μ) = 0 := tendsto_nhds_unique hconv hval
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun ω => by change 0 ≤ f ω; unfold f; split_ifs <;> norm_num)) hfi).mp heq
  filter_upwards [hae] with ω hω
  have hne : X ω ≠ 0 := by intro he; simp [f, he] at hω
  exact lt_of_le_of_ne (h0 ω) (Ne.symm hne)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma integrable_exp_neg_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (h0 : ∀ ω, 0 ≤ X ω)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun ω => Real.exp (-t*X ω)) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (h0 ω))

lemma stable_positive_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (h0 : ∀ ω, 0 ≤ X ω)
    {c m : ℝ} (hc : 0 ≤ c) (hm : 0 < m) (hm1 : m < 1)
    (hL : ∀ t : ℝ, 0 ≤ t → (∫ ω, Real.exp (-t*X ω) ∂μ) = Real.exp (-c*t^m))
    {a : ℝ} (ha : 0 < a) (ham : a < m) : Integrable (fun ω => (X ω)^a) μ := by
  let K : ℝ × Ω → ℝ := fun z => 1-Real.exp (-(z.1^(-1/a))*X z.2)
  have hK : Measurable K := by unfold K; fun_prop
  have hK0 : ∀ x : ℝ, 0 < x → ∀ ω, 0 ≤ K (x,ω) := by
    intro x hx ω
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.rpow_nonneg hx.le _)) (h0 ω)))
  have hKi : ∀ x : ℝ, 0 < x → Integrable (fun ω => K (x,ω)) μ := by
    intro x hx
    exact (integrable_const 1).sub (integrable_exp_neg_mul μ hX h0 (Real.rpow_nonneg hx.le _))
  have hKval : ∀ x : ℝ, 0 < x → (∫ ω, K (x,ω) ∂μ) =
      1-Real.exp (-c*x^(-1/(a/m))) := by
    intro x hx
    unfold K
    rw [integral_sub (integrable_const 1)
      (integrable_exp_neg_mul μ hX h0 (Real.rpow_nonneg hx.le _)), hL _ (Real.rpow_nonneg hx.le _)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [← Real.rpow_mul hx.le]
    congr 3
    field_simp
  have hip : Integrable K ((volume.restrict (Ioi 0)).prod μ) := by
    apply (integrable_prod_iff hK.aestronglyMeasurable).mpr
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hKi x hx
    · apply (stable_integrable (div_pos ha hm) ((div_lt_one hm).mpr ham) hc).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [← hKval x hx]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => (Real.norm_of_nonneg (hK0 x hx ω)).symm
  have hinner : ∀ ω, (∫ x in Ioi (0:ℝ), K (x,ω)) = Real.Gamma (1-a)*(X ω)^a := by
    intro ω
    have he : (fun x : ℝ => K (x,ω)) =
        (fun x : ℝ => 1-Real.exp (-(X ω)*x^(-1/a))) := by
      funext x; unfold K; congr 2; ring
    rw [he, stable_integral ha (ham.trans hm1) (h0 ω)]
  have hi := hip.integral_prod_right
  simp_rw [hinner] at hi
  have hγ : Real.Gamma (1-a) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0 < 1-a)).ne'
  convert hi.const_mul (Real.Gamma (1-a))⁻¹ using 1
  funext ω
  simp [hγ]

lemma stable_negative_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (h0 : ∀ ω, 0 ≤ X ω)
    (hpos : ∀ᵐ ω ∂μ, 0 < X ω) {c m : ℝ} (hc : 0 < c) (hm : 0 < m)
    (hL : ∀ t : ℝ, 0 ≤ t → (∫ ω, Real.exp (-t*X ω) ∂μ) = Real.exp (-c*t^m))
    {a : ℝ} (ha : 0 < a) : Integrable (fun ω => (X ω)^(-a)) μ := by
  let K : ℝ × Ω → ℝ := fun z => Real.exp (-(z.1^(1/a))*X z.2)
  have hK : Measurable K := by unfold K; fun_prop
  have hKi : ∀ x : ℝ, 0 < x → Integrable (fun ω => K (x,ω)) μ := by
    intro x hx
    exact integrable_exp_neg_mul μ hX h0 (Real.rpow_nonneg hx.le _)
  have hKval : ∀ x : ℝ, 0 < x → (∫ ω, K (x,ω) ∂μ) =
      Real.exp (-c*x^(m/a)) := by
    intro x hx
    unfold K
    rw [hL _ (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
    congr 2; ring_nf
  have hiouter : IntegrableOn (fun x : ℝ => Real.exp (-c*x^(m/a))) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (0:ℝ)) (by norm_num) (div_pos hm ha) hc)
  have hip : Integrable K ((volume.restrict (Ioi 0)).prod μ) := by
    apply (integrable_prod_iff hK.aestronglyMeasurable).mpr
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hKi x hx
    · apply hiouter.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [← hKval x hx]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => (Real.norm_of_nonneg (Real.exp_pos _).le).symm
  have hinner : ∀ᵐ ω ∂μ, (∫ x in Ioi (0:ℝ), K (x,ω)) =
      (X ω)^(-a)*Real.Gamma (a+1) := by
    filter_upwards [hpos] with ω hω
    have he : (fun x : ℝ => K (x,ω)) =
        (fun x : ℝ => Real.exp (-(X ω)*x^(1/a))) := by
      funext x; unfold K; congr 1; ring
    rw [he, integral_exp_neg_mul_rpow (div_pos (by norm_num) ha) hω]
    congr 2 <;> field_simp
  have hi := hip.integral_prod_right.congr hinner
  have hγ : Real.Gamma (a+1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0 < a+1)).ne'
  convert hi.mul_const (Real.Gamma (a+1))⁻¹ using 1
  funext ω
  simp [hγ]
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma log_square_le_powers {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    |Real.log x|^2 ≤ ((a/2)^2)⁻¹*(x^a+x^(-a)) := by
  let ε : ℝ := a/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have h₁ : ε*Real.log x ≤ x^ε := by
    have h := Real.log_le_rpow_div hx.le hε
    simpa only [mul_comm] using (le_div_iff₀ hε).mp h
  have h₂ : -(ε*Real.log x) ≤ x^(-ε) := by
    have h := (le_div_iff₀ hε).mp (Real.log_le_rpow_div (inv_nonneg.mpr hx.le) hε)
    rw [Real.log_inv, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le] at h
    nlinarith
  have hp₁ : (x^ε)^2 = x^a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1; dsimp [ε]; ring
  have hp₂ : (x^(-ε))^2 = x^(-a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1; dsimp [ε]; ring
  have hb : (ε*Real.log x)^2 ≤ x^a+x^(-a) := by
    by_cases h : 0 ≤ ε*Real.log x
    · have hh := pow_le_pow_left₀ h h₁ 2
      rw [hp₁] at hh
      exact hh.trans (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
    · have hh := pow_le_pow_left₀ (neg_nonneg.mpr (le_of_not_ge h)) h₂ 2
      rw [neg_sq, hp₂] at hh
      exact hh.trans (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))
  rw [sq_abs, mul_comm ((a/2)^2)⁻¹, ← div_eq_mul_inv]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  change (Real.log x)^2 * ε^2 ≤ _
  nlinarith

lemma integrable_log_square {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (hX : Measurable X) (hpos : ∀ᵐ ω ∂μ, 0 < X ω)
    {a : ℝ} (ha : 0 < a) (hplus : Integrable (fun ω => (X ω)^a) μ)
    (hminus : Integrable (fun ω => (X ω)^(-a)) μ) :
    Integrable (fun ω => |Real.log (X ω)|^2) μ := by
  apply ((hplus.add hminus).const_mul ((a/2)^2)⁻¹).mono' (hX.log.abs.pow_const 2).aestronglyMeasurable
  filter_upwards [hpos] with ω hω
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact log_square_le_powers hω ha
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

theorem stableCloud : StableCloudStatement := by
  intro m hm hm1 ν hprob hν hmean
  let : IsProbabilityMeasure ν := hprob
  let c : ℝ := Real.Gamma (1-m)*(∫ y : ℝ≥0, (y:ℝ)^m ∂ν)
  have hc : 0 < c := mul_pos (Real.Gamma_pos_of_pos (by linarith)) hmean
  have hExt : ∀ t : ℝ, 0 ≤ t → (∫ ω, expNeg (ENNReal.ofReal t*stableCloudSum m ω)
      ∂markedCloudLaw ν) = Real.exp (-c*t^m) := by
    intro t ht
    rw [cloud_laplace_extended hm hm1 ν hν ht]
    congr 1; dsimp [c]; ring
  have hfin := laplace_ae_ne_top (markedCloudLaw ν) (measurable_stableCloudSum m) hm hExt
  have hX : Measurable (fun ω => (stableCloudSum m ω).toReal) :=
    (measurable_stableCloudSum m).ennreal_toReal
  have hL : ∀ t : ℝ, 0 ≤ t → (∫ ω, Real.exp (-t*(stableCloudSum m ω).toReal)
      ∂markedCloudLaw ν) = Real.exp (-c*t^m) := by
    intro t ht
    rw [← hExt t ht]
    apply integral_congr_ae
    filter_upwards [hfin] with ω hω
    rw [expNeg_eq_of_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
    congr 1; ring
  have hpos := laplace_real_ae_pos (markedCloudLaw ν) hX
    (fun _ => ENNReal.toReal_nonneg) hc hm hL
  have hplus : ∀ a : ℝ, 0 < a → a < m →
      Integrable (fun ω => (stableCloudSum m ω).toReal^a) (markedCloudLaw ν) := by
    intro a ha ham
    exact stable_positive_moment (markedCloudLaw ν) hX (fun _ => ENNReal.toReal_nonneg)
      hc.le hm hm1 hL ha ham
  have hminus : ∀ a : ℝ, 0 < a →
      Integrable (fun ω => (stableCloudSum m ω).toReal^(-a)) (markedCloudLaw ν) := by
    intro a ha
    exact stable_negative_moment (markedCloudLaw ν) hX (fun _ => ENNReal.toReal_nonneg)
      hpos hc hm hL ha
  refine ⟨?_, ?_, hplus, hminus, ?_⟩
  · filter_upwards [hpos] with ω hω
    exact ENNReal.toReal_pos_iff.mp hω
  · intro t ht
    rw [hL t ht]
    congr 1; dsimp [c]; ring
  · exact integrable_log_square (markedCloudLaw ν) hX hpos (div_pos hm (by norm_num))
      (hplus (m/2) (by positivity) (by linarith)) (hminus (m/2) (by positivity))

end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma pointCloud_mark_preserving {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [IsProbabilityMeasure ν] (n j : ℕ) :
    MeasurePreserving (fun ω : PointCloud A => ((ω n).2 j).2) (pointCloudLaw ν) ν := by
  have h₁ := measurePreserving_eval_infinitePi (fun _ : ℕ => poissonBinLaw (cloudUniform.prod ν)) n
  have h₂ : MeasurePreserving Prod.snd (poissonBinLaw (cloudUniform.prod ν))
      (Measure.infinitePi (fun _ : ℕ => cloudUniform.prod ν)) := measurePreserving_snd
  have h₃ := measurePreserving_eval_infinitePi (fun _ : ℕ => cloudUniform.prod ν) j
  have h₄ : MeasurePreserving Prod.snd (cloudUniform.prod ν) ν := measurePreserving_snd
  exact h₄.comp (h₃.comp (h₂.comp h₁))

lemma ae_pointCloud_marks {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [IsProbabilityMeasure ν] {p : A → Prop} (hp : ∀ᵐ a ∂ν, p a) :
    ∀ᵐ ω ∂pointCloudLaw ν, ∀ n j, p ((ω n).2 j).2 := by
  rw [ae_all_iff]
  intro n
  rw [ae_all_iff]
  intro j
  exact (pointCloud_mark_preserving ν n j).quasiMeasurePreserving.ae hp

def coloredStableSum {A : Type*} (m : ℝ) (Y : A → ℝ≥0) (ω : PointCloud A) : ℝ≥0∞ :=
  pointCloudFunctional (fun z => ENNReal.ofReal (z.1^(-1/m)*(Y z.2:ℝ))) ω

lemma stableCloudSum_mapPointCloud {A : Type*} (m : ℝ) (Y : A → ℝ≥0) (ω : PointCloud A) :
    stableCloudSum m (mapPointCloud Y ω) = coloredStableSum m Y ω := by
  rw [stableCloudSum_bins]
  rfl

lemma coloredStable_properties {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {Y : A → ℝ≥0} (hY : Measurable Y)
    (hi : Integrable (fun a => (Y a:ℝ)^m) ν) (hp : 0 < ∫ a, (Y a:ℝ)^m ∂ν) :
    (∀ᵐ ω ∂pointCloudLaw ν, 0 < coloredStableSum m Y ω ∧ coloredStableSum m Y ω < ∞) ∧
    (∀ a : ℝ, 0 < a → a < m → Integrable (fun ω => (coloredStableSum m Y ω).toReal^a) (pointCloudLaw ν)) ∧
    Integrable (fun ω => |Real.log (coloredStableSum m Y ω).toReal|^2) (pointCloudLaw ν) := by
  let η := ν.map Y
  have : IsProbabilityMeasure η := inferInstance
  have hpow : Measurable (fun y : ℝ≥0 => (y:ℝ)^m) := by fun_prop
  have hiη : Integrable (fun y : ℝ≥0 => (y:ℝ)^m) η :=
    (integrable_map_measure hpow.aestronglyMeasurable hY.aemeasurable).mpr hi
  have hpη : 0 < ∫ y : ℝ≥0, (y:ℝ)^m ∂η := by
    rwa [integral_map hY.aemeasurable hpow.aestronglyMeasurable]
  have hs := stableCloud m hm hm1 η inferInstance hiη hpη
  have hmap : MeasurePreserving (mapPointCloud Y) (pointCloudLaw ν) (markedCloudLaw η) :=
    ⟨measurable_mapPointCloud hY, pointCloudLaw_map ν hY⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [stableCloudSum_mapPointCloud] using hmap.quasiMeasurePreserving.ae hs.1
  · intro a ha ham
    simpa only [Function.comp_def, stableCloudSum_mapPointCloud] using
      hmap.integrable_comp_of_integrable (hs.2.2.1 a ha ham)
  · simpa only [Function.comp_def, stableCloudSum_mapPointCloud] using
      hmap.integrable_comp_of_integrable hs.2.2.2.2
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

instance cascadeLaw_probability (ms : List ℝ) : IsProbabilityMeasure (cascadeLaw ms) := by
  induction ms with
  | nil => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | cons m ms ih =>
    have := ih
    exact inferInstanceAs (IsProbabilityMeasure (pointCloudLaw (cascadeLaw ms)))

lemma measurable_cascadeTotal (ms : List ℝ) : Measurable (cascadeTotal ms) := by
  induction ms with
  | nil => exact measurable_const
  | cons m ms ih =>
    exact measurable_pointCloudFunctional ((by fun_prop : Measurable
      (fun z : ℝ × CascadeTree ms.length => ENNReal.ofReal (z.1^(-1/m)))).mul
      (ih.comp measurable_snd))

lemma pointCloudFunctional_mark_congr {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {f g : ℝ × A → ℝ≥0∞}
    (h : ∀ᵐ a ∂ν, ∀ x, f (x,a) = g (x,a)) :
    pointCloudFunctional f =ᵐ[pointCloudLaw ν] pointCloudFunctional g := by
  filter_upwards [ae_pointCloud_marks ν h] with ω hω
  unfold pointCloudFunctional
  apply tsum_congr
  intro n
  unfold poissonBinSum
  apply Finset.sum_congr rfl
  intro j hj
  exact hω n j _

lemma cascadeTotal_colored {ms : List ℝ} {m : ℝ}
    (hf : ∀ᵐ ω ∂cascadeLaw ms, cascadeTotal ms ω < ∞) :
    cascadeTotal (m::ms) =ᵐ[cascadeLaw (m::ms)]
      coloredStableSum m (fun ω => (cascadeTotal ms ω).toNNReal) := by
  apply pointCloudFunctional_mark_congr (cascadeLaw ms)
  filter_upwards [hf] with ω hω
  intro x
  rw [ENNReal.ofReal_mul' (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
    ENNReal.coe_toNNReal hω.ne]

lemma cascadeTotal_properties (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) :
    (∀ᵐ ω ∂cascadeLaw ms, 0 < cascadeTotal ms ω ∧ cascadeTotal ms ω < ∞) ∧
    (∀ a : ℝ, 0 < a → (∀ m ∈ ms, a < m) →
      Integrable (fun ω => (cascadeTotal ms ω).toReal^a) (cascadeLaw ms)) ∧
    Integrable (fun ω => |Real.log (cascadeTotal ms ω).toReal|^2) (cascadeLaw ms) := by
  induction ms with
  | nil =>
    refine ⟨Filter.Eventually.of_forall (by intro ω; simp [cascadeTotal]), ?_, ?_⟩
    · intro a ha ham
      simpa [cascadeTotal] using integrable_const (μ := cascadeLaw ([] : List ℝ)) (1:ℝ)
    · simp [cascadeTotal]
  | cons m ms ih =>
    have hm := (h01 m (List.mem_cons_self)).1
    have hm1 := (h01 m (List.mem_cons_self)).2
    have hs := List.pairwise_cons.mp hms
    have ht := ih hs.2 (fun x hx => h01 x (List.mem_cons_of_mem _ hx))
    let Y : CascadeTree ms.length → ℝ≥0 := fun ω => (cascadeTotal ms ω).toNNReal
    have hY : Measurable Y := (measurable_cascadeTotal ms).ennreal_toNNReal
    have hi : Integrable (fun ω => (Y ω:ℝ)^m) (cascadeLaw ms) := ht.2.1 m hm hs.1
    have hpos : ∀ᵐ ω ∂cascadeLaw ms, 0 < (Y ω:ℝ)^m := by
      filter_upwards [ht.1] with ω hω
      exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hω.1.ne' hω.2.ne) _
    have hp : 0 < ∫ ω, (Y ω:ℝ)^m ∂cascadeLaw ms := by
      have hn : 0 ≤ ∫ ω, (Y ω:ℝ)^m ∂cascadeLaw ms :=
        integral_nonneg (fun ω => Real.rpow_nonneg (NNReal.coe_nonneg _) _)
      apply lt_of_le_of_ne hn
      intro heq
      have hz := (integral_eq_zero_iff_of_nonneg
        (fun ω => Real.rpow_nonneg (NNReal.coe_nonneg _) _) hi).mp heq.symm
      have hc := hpos.and hz
      obtain ⟨ω, hω⟩ := hc.exists
      exact (ne_of_gt hω.1) hω.2
    have hc := coloredStable_properties (cascadeLaw ms) hm hm1 hY hi hp
    have heq := cascadeTotal_colored (m := m) (ht.1.mono (fun _ h => h.2))
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [heq, hc.1] with ω he hω
      rwa [he]
    · intro a ha ham
      exact (hc.2.1 a ha (ham m (List.mem_cons_self))).congr
        (heq.symm.mono (fun _ h => congrArg (fun x : ℝ≥0∞ => x.toReal^a) h))
    · exact hc.2.2.congr
        (heq.symm.mono (fun _ h => congrArg (fun x : ℝ≥0∞ => |Real.log x.toReal|^2) h))

theorem cascadeNormalization : CascadeNormalizationStatement := by
  intro ms hms h01
  have h := cascadeTotal_properties ms hms h01
  exact ⟨h.1, h.2.2⟩

end MicroscopicJamming

end

end OAI
