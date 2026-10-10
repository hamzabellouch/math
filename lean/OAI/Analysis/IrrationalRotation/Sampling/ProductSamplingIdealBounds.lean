import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingWeightTests
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingEstimates
import OAI.Analysis.IrrationalRotation.Couplings.ProductDensity
import OAI.Analysis.IrrationalRotation.Analysis.ScalarKernelMomentRates
import OAI.Analysis.IrrationalRotation.Rotation.CircleRepresentative
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductSampling

theorem partial_product_sq_le_exp {ι : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] (D : Finset ι) (f : (i : ι) → Ω i → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) {m c : ℝ}
    (hm : 1 ≤ m) (hc : 0 ≤ c)
    (hd : (D.card : ℝ) ≤ (101 / 100 : ℝ) * m)
    (hb : ∀ i ∈ D, (∫ x, (f i x)^2 ∂μ i) ≤ 1 + c * m^(-6 / 5 : ℝ)) :
    (∫ x, (∏ i ∈ D, f i (x i))^2 ∂Measure.infinitePi μ) ≤
      Real.exp ((101 / 100 : ℝ) * c) := by
  simp_rw [← Finset.prod_pow]
  rw [ProductDensity.integral_partial_product D (fun i => (hf i).integrable_sq)]
  have hδ : 0 ≤ c * m^(-6 / 5 : ℝ) := mul_nonneg hc (Real.rpow_nonneg (by linarith) _)
  calc
    (∏ i ∈ D, ∫ x, (f i x)^2 ∂μ i) ≤ ∏ _i ∈ D, (1 + c * m^(-6 / 5 : ℝ)) :=
      Finset.prod_le_prod₀ (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) hb
    _ = (1 + c * m^(-6 / 5 : ℝ))^D.card := by simp
    _ ≤ (Real.exp (c * m^(-6 / 5 : ℝ)))^D.card :=
      pow_le_pow_left₀ (by linarith) (by simpa [add_comm] using Real.add_one_le_exp (c * m^(-6 / 5 : ℝ))) _
    _ = Real.exp ((D.card : ℝ) * (c * m^(-6 / 5 : ℝ))) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((101 / 100 : ℝ) * c) := by
      apply Real.exp_le_exp.mpr
      calc
        (D.card : ℝ) * (c * m^(-6 / 5 : ℝ)) ≤
            ((101 / 100 : ℝ) * m) * (c * m^(-6 / 5 : ℝ)) := mul_le_mul_of_nonneg_right hd hδ
        _ = ((101 / 100 : ℝ) * c) * (m * m^(-6 / 5 : ℝ)) := by ring
        _ ≤ ((101 / 100 : ℝ) * c) * 1 :=
          mul_le_mul_of_nonneg_left (mul_rpow_le_one hm (by norm_num)) (by positivity)
        _ = _ := mul_one _

theorem partial_product_eLpNorm_le_exp {ι : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] (D : Finset ι) (f : (i : ι) → Ω i → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) {m c : ℝ}
    (hm : 1 ≤ m) (hc : 0 ≤ c)
    (hd : (D.card : ℝ) ≤ (101 / 100 : ℝ) * m)
    (hb : ∀ i ∈ D, (∫ x, (f i x)^2 ∂μ i) ≤ 1 + c * m^(-6 / 5 : ℝ)) :
    eLpNorm (fun x => ∏ i ∈ D, f i (x i)) 2 (Measure.infinitePi μ) ≤
      ENNReal.ofReal (Real.exp ((101 / 200 : ℝ) * c)) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    (ProductDensity.memLp_partial_product D hf)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Real.exp ((101 / 100 : ℝ) * c))^(1 / 2 : ℝ) :=
      Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _)
        (partial_product_sq_le_exp D f hf hm hc hd hb) (by positivity)
    _ = Real.exp ((101 / 200 : ℝ) * c) := by
      rw [← Real.exp_mul]; congr 1; ring

end Invariant233.ProductSampling

namespace Invariant233.ProductModel.SamplingWeights

def idealCoordinate (endpoint : Bool) (I : Finset ℕ) (h α : ℝ) (i : ℕ)
    (E F : Set ℝ) (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, testedCoordinateWeight endpoint I h α i E F s t

 theorem measurable_idealCoordinate (endpoint : Bool) (I : Finset ℕ) (h α : ℝ)
    (i : ℕ) {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Measurable (idealCoordinate endpoint I h α i E F) :=
  ScalarSampling.measurable_interval_average (measurable_testedCoordinateWeight endpoint I h α i hE hF)

 theorem idealCoordinate_nonneg (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) (E F : Set ℝ) (s : ℝ) :
    0 ≤ idealCoordinate endpoint I h α i E F s :=
  intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun t => (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).1)

 theorem norm_idealCoordinate_le (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) (E F : Set ℝ) (s : ℝ) :
    ‖idealCoordinate endpoint I h α i E F s‖ ≤ height h α := by
  have hb (t : ℝ) (_ht : t ∈ uIoc (0 : ℝ) 1) :
      ‖testedCoordinateWeight endpoint I h α i E F s t‖ ≤ height h α := by
    rw [Real.norm_eq_abs, abs_of_nonneg (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).1]
    exact (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).2
  simpa [idealCoordinate] using intervalIntegral.norm_integral_le_of_norm_le_const hb

 theorem memLp_idealCoordinate (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    MemLp (fun x : Circle => idealCoordinate endpoint I h α i E F (circleRepresentative x))
      2 circleMeasure := by
  apply MemLp.of_bound ((measurable_idealCoordinate endpoint I h α i hE hF).comp
    ProductCocycle.measurable_representative).aestronglyMeasurable (height h α)
  exact Filter.Eventually.of_forall fun x => norm_idealCoordinate_le endpoint I hh hα i E F _

 theorem intervalIntegrable_idealCoordinate (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    IntervalIntegrable (fun s => (idealCoordinate endpoint I h α i E F s)^2) volume 0 1 := by
  apply ScalarSampling.intervalIntegrable_unit_of_measurable_bound
    ((measurable_idealCoordinate endpoint I h α i hE hF).pow_const 2)
  intro s
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_idealCoordinate_le endpoint I hh hα i E F s) 2

theorem testedCoordinateWeight_le_univ (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) (E F : Set ℝ) (s t : ℝ) :
    testedCoordinateWeight endpoint I h α i E F s t ≤
      testedCoordinateWeight endpoint I h α i univ univ s t := by
  unfold testedCoordinateWeight
  simp only [Set.indicator_univ, mul_one]
  by_cases he : (if endpoint = true then Int.fract (s - t) else s) ∈ E <;>
    by_cases hf : (if endpoint = true then s else Int.fract (s + t)) ∈ F
  · simp only [Set.indicator_of_mem he, Set.indicator_of_mem hf, mul_one]
    exact le_rfl
  · simp only [Set.indicator_of_notMem hf, mul_zero]
    exact (coordinateWeight_bounds I hh hα i _ _).1
  · simp only [Set.indicator_of_notMem he, mul_zero, zero_mul]
    exact (coordinateWeight_bounds I hh hα i _ _).1
  · simp only [Set.indicator_of_notMem he, mul_zero, zero_mul]
    exact (coordinateWeight_bounds I hh hα i _ _).1

 theorem intervalIntegrable_testedCoordinateWeight (endpoint : Bool) (I : Finset ℕ)
    {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (i : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (s : ℝ) :
    IntervalIntegrable (testedCoordinateWeight endpoint I h α i E F s) volume 0 1 := by
  apply ScalarSampling.intervalIntegrable_unit_of_measurable_bound
    ((measurable_testedCoordinateWeight endpoint I h α i hE hF).comp
      (measurable_const.prodMk measurable_id))
  intro t
  change ‖testedCoordinateWeight endpoint I h α i E F s t‖ ≤ height h α
  rw [Real.norm_eq_abs, abs_of_nonneg (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).1]
  exact (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).2

 theorem idealCoordinate_le_univ (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (s : ℝ) :
    idealCoordinate endpoint I h α i E F s ≤ idealCoordinate endpoint I h α i univ univ s := by
  exact intervalIntegral.integral_mono (by norm_num)
    (intervalIntegrable_testedCoordinateWeight endpoint I hh hα i hE hF s)
    (intervalIntegrable_testedCoordinateWeight endpoint I hh hα i MeasurableSet.univ MeasurableSet.univ s)
    (testedCoordinateWeight_le_univ endpoint I hh hα i E F s)

theorem idealCoordinate_univ_eq_scalar (endpoint : Bool) {I : Finset ℕ} {i m : ℕ}
    (hi : i ∉ I) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i univ univ s =
      ∫ t in (0 : ℝ)..1, if endpoint then ScalarSampling.manuscriptEndpointKernel m s t
        else ScalarSampling.manuscriptKernel m s t := by
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro t ht
  have ht' := Int.fract_eq_self.mpr (show t ∈ Ico (0 : ℝ) 1 from ⟨ht.1.le, ht.2⟩)
  cases endpoint <;>
    simp [testedCoordinateWeight, coordinateWeight, hi, ScalarSampling.manuscriptEndpointKernel,
      ScalarSampling.manuscriptKernel, ScalarSampling.circleKernel, ht', Int.fract_eq_self.mpr hs]

theorem idealCoordinate_univ_le_one_of_mem (endpoint : Bool) {I : Finset ℕ}
    {i : ℕ} (hi : i ∈ I) (h α s : ℝ) :
    idealCoordinate endpoint I h α i univ univ s ≤ 1 := by
  have hb (t : ℝ) (_ht : t ∈ uIoc (0 : ℝ) 1) :
      ‖testedCoordinateWeight endpoint I h α i univ univ s t‖ ≤ (1 : ℝ) := by
    simp only [testedCoordinateWeight, coordinateWeight, ite_eq_left hi,
      ScalarSampling.triangularKernel, Set.indicator_apply]
    split_ifs <;> norm_num
  have hn : ‖idealCoordinate endpoint I h α i univ univ s‖ ≤ 1 := by
    simpa [idealCoordinate] using intervalIntegral.norm_integral_le_of_norm_le_const hb
  exact (le_abs_self _).trans hn

theorem idealCoordinate_square_integral_le (endpoint : Bool) (I : Finset ℕ)
    {m : ℕ} (hm : 200 ≤ m) (i : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    (∫ s in (0 : ℝ)..1,
      (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i E F s)^2) ≤
        1 + 4 * (m : ℝ)^(-(6 / 5 : ℝ)) := by
  obtain ⟨hh, _, hα, _⟩ := ScalarSampling.manuscript_parameters hm
  have htest : (∫ s in (0 : ℝ)..1,
      (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i E F s)^2) ≤
      ∫ s in (0 : ℝ)..1,
      (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i univ univ s)^2 := by
    apply intervalIntegral.integral_mono (by norm_num)
      (intervalIntegrable_idealCoordinate endpoint I hh hα i hE hF)
      (intervalIntegrable_idealCoordinate endpoint I hh hα i MeasurableSet.univ MeasurableSet.univ)
    intro s
    exact pow_le_pow_left₀ (idealCoordinate_nonneg endpoint I hh hα i E F s)
      (idealCoordinate_le_univ endpoint I hh hα i hE hF s) 2
  apply htest.trans
  by_cases hi : i ∈ I
  · have hu : (∫ s in (0 : ℝ)..1,
        (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i univ univ s)^2) ≤ 1 := by
      have he := intervalIntegral.integral_mono (by norm_num : (0 : ℝ) ≤ 1)
        (intervalIntegrable_idealCoordinate endpoint I hh hα i MeasurableSet.univ MeasurableSet.univ)
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1)
        (fun s => pow_le_one₀ (idealCoordinate_nonneg endpoint I hh hα i univ univ s)
          (idealCoordinate_univ_le_one_of_mem endpoint hi _ _ s))
      simpa using he
    exact hu.trans (le_add_of_nonneg_right (by positivity))
  · have he : (∫ s in (0 : ℝ)..1,
        (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i univ univ s)^2) =
        ∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1,
          if endpoint then ScalarSampling.manuscriptEndpointKernel m s t else ScalarSampling.manuscriptKernel m s t)^2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro s hs
      dsimp only
      rw [idealCoordinate_univ_eq_scalar endpoint (m := m) hi ⟨hs.1.le, hs.2⟩]
    rw [he]
    cases endpoint
    · exact (ScalarSampling.manuscript_average_square_rates hm).1
    · exact (ScalarSampling.manuscript_average_square_rates hm).2

theorem integral_circleRepresentative_eq_interval (f : ℝ → ℝ) :
    (∫ x : Circle, f (circleRepresentative x) ∂circleMeasure) =
      ∫ s in (0 : ℝ)..1, f s := by
  have hr : MeasurableEmbedding (circleRepresentative : Circle → ℝ) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ico).comp
      (AddCircle.measurableEquivIco (1 : ℝ) 0).measurableEmbedding
  calc
    _ = ∫ s in Ico (0 : ℝ) 1, f s :=
      CocycleSupport.measurePreserving_circleRepresentative.integral_comp hr f
    _ = ∫ s in Ioc (0 : ℝ) 1, f s := integral_Ico_eq_integral_Ioc
    _ = _ := (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm

 theorem idealCoordinate_circle_square_integral_le (endpoint : Bool) (I : Finset ℕ)
    {m : ℕ} (hm : 200 ≤ m) (i : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    (∫ x : Circle,
      (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i E F
        (circleRepresentative x))^2 ∂circleMeasure) ≤
        1 + 4 * (m : ℝ)^(-(6 / 5 : ℝ)) := by
  rw [integral_circleRepresentative_eq_interval (fun s =>
    (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i E F s)^2)]
  exact idealCoordinate_square_integral_le endpoint I hm i hE hF

def idealProduct (endpoint : Bool) (D I : Finset ℕ) (h α : ℝ)
    (E F : ℕ → Set ℝ) (x : Base) : ℝ :=
  ∏ i ∈ D, idealCoordinate endpoint I h α i (E i) (F i) (circleRepresentative (x i))

theorem memLp_idealProduct (endpoint : Bool) (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i)) :
    MemLp (idealProduct endpoint D I h α E F) 2 baseMeasure :=
  ProductDensity.memLp_partial_product D
    (fun i => memLp_idealCoordinate endpoint I hh hα i (hE i) (hF i))

theorem manuscript_idealProduct_eLpNorm_le (endpoint : Bool) (D I : Finset ℕ)
    {m : ℕ} (hm : 200 ≤ m) (hd : (D.card : ℝ) ≤ (101 / 100 : ℝ) * m)
    (E F : ℕ → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i)) :
    eLpNorm (idealProduct endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ)))
        (1 / (m : ℝ)^2) E F) 2 baseMeasure ≤
      ENNReal.ofReal (Real.exp (101 / 50 : ℝ)) := by
  obtain ⟨hh, _, hα, _⟩ := ScalarSampling.manuscript_parameters hm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have he := ProductSampling.partial_product_eLpNorm_le_exp
    (μ := fun _ : ℕ => circleMeasure) D
    (fun i x => idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ)))
      (1 / (m : ℝ)^2) i (E i) (F i) (circleRepresentative x))
    (fun i => memLp_idealCoordinate endpoint I hh hα i (hE i) (hF i))
    (c := 4) hm' (by norm_num) hd
    (fun i _ => by simpa only [neg_div] using
      idealCoordinate_circle_square_integral_le endpoint I hm i (hE i) (hF i))
  norm_num only [show (101 / 200 : ℝ) * 4 = 101 / 50 by norm_num] at he
  exact he

theorem idealProduct_eLpNorm_le_height (endpoint : Bool) (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ) :
    eLpNorm' (idealProduct endpoint D I h α E F) 2 baseMeasure ≤
      ENNReal.ofReal ((height h α)^D.card) := by
  have hb : ∀ᵐ x ∂baseMeasure, ‖idealProduct endpoint D I h α E F x‖ ≤ (height h α)^D.card := by
    filter_upwards [] with x
    unfold idealProduct
    rw [norm_prod]
    calc
      (∏ i ∈ D, ‖idealCoordinate endpoint I h α i (E i) (F i) (circleRepresentative (x i))‖) ≤
          ∏ _i ∈ D, height h α :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i _ => norm_idealCoordinate_le endpoint I hh hα i (E i) (F i) _)
      _ = _ := by simp
  have hheight : 0 ≤ (height h α)^D.card := by unfold height; positivity
  calc
    _ ≤ eLpNorm' (fun _ : Base => (height h α)^D.card) 2 baseMeasure :=
      eLpNorm'_mono_ae (by norm_num)
        (hb.mono fun _ hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg hheight] using hx)
    _ = _ := by
      rw [eLpNorm'_const_of_isProbabilityMeasure _ (by norm_num), Real.enorm_of_nonneg hheight]

theorem source_idealProduct_uniform_bound {p : ProductScaleData} (hp : ProductScaleLaws p) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ j : ℕ, ∀ endpoint : Bool, ∀ I : Finset ℕ,
      ∀ E F : ℕ → Set ℝ, (∀ i, MeasurableSet (E i)) → (∀ i, MeasurableSet (F i)) →
      eLpNorm (idealProduct endpoint (Finset.range (p.prefixCount (j + 1))) I
        ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2) E F) 2 baseMeasure ≤
          ENNReal.ofReal H := by
  let B : ℝ := (height ((p.m 0 : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m 0 : ℝ)^2)) ^ p.prefixCount 1
  refine ⟨max (Real.exp (101 / 50 : ℝ)) B,
    (Real.exp_pos _).le.trans (le_max_left _ _), ?_⟩
  intro j endpoint I E F hE hF
  cases j with
  | zero =>
      have hm0 : (0 : ℝ) < p.m 0 := by exact_mod_cast hp.m_pos 0
      have he := idealProduct_eLpNorm_le_height endpoint (Finset.range (p.prefixCount 1)) I
        (Real.rpow_pos_of_pos hm0 (-(3 / 5 : ℝ))) (by positivity : 0 < 1 / (p.m 0 : ℝ)^2) E F
      have hmem := memLp_idealProduct endpoint (Finset.range (p.prefixCount 1)) I
        (Real.rpow_pos_of_pos hm0 (-(3 / 5 : ℝ))) (by positivity : 0 < 1 / (p.m 0 : ℝ)^2)
        E F hE hF
      rw [eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num) hmem.aestronglyMeasurable]
      norm_num only [ENNReal.toReal_ofNat]
      simp only [Finset.card_range] at he
      exact he.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  | succ j =>
      have hm : 200 ≤ p.m (j + 1) := by
        have hK := hp.K_ge_100 j
        have hd := hp.K_double j
        have hKm := hp.m_ge_K (j + 1)
        omega
      have hd : ((Finset.range (p.prefixCount ((j + 1) + 1))).card : ℝ) ≤
          (101 / 100 : ℝ) * p.m (j + 1) := by
        simpa only [Finset.card_range] using hp.prefix_count_succ_le (j + 1)
      exact (manuscript_idealProduct_eLpNorm_le endpoint _ I hm hd E F hE hF).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _))

end Invariant233.ProductModel.SamplingWeights

end

end OAI
