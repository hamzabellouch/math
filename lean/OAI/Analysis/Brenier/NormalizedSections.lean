import OAI.Analysis.Brenier.TriangularSampling

namespace OAI

noncomputable section

open MeasureTheory Classical
open scoped ENNReal

namespace Problem358.NormalizedSections

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

def sectionMass (ν : Measure B) (q : A → B → ℝ≥0∞) (a : A) : ℝ≥0∞ :=
  ∫⁻ b, q a b ∂ν

def sectionDensity (ν : Measure B) (q : A → B → ℝ≥0∞) (a : A) (b : B) : ℝ≥0∞ :=
  q a b / sectionMass ν q a

def sectionLaw (ν : Measure B) (q : A → B → ℝ≥0∞) (a : A) : Measure B :=
  ν.withDensity (sectionDensity ν q a)

/-- A constant normalization of the joint density scales each marginal mass. -/
theorem sectionMass_const_mul (ν : Measure B)
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (c : ℝ≥0∞) (a : A) :
    sectionMass ν (fun a b => c * q a b) a = c * sectionMass ν q a := by
  exact lintegral_const_mul c hq.of_uncurry_left

/-- The conditional density is unaffected by any positive finite normalization
of the whole joint density, including on zero or infinite sections. -/
theorem sectionDensity_const_mul (ν : Measure B)
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    sectionDensity ν (fun a b => c * q a b) = sectionDensity ν q := by
  funext a b
  simp only [sectionDensity, sectionMass_const_mul ν hq c]
  exact ENNReal.mul_div_mul_left _ _ hc0 hctop

/-- Uniform-region sampling can use the unscaled conditional laws while its
joint density and section-mass marginal carry the total-volume normalization. -/
theorem sectionLaw_const_mul (ν : Measure B)
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞) (a : A) :
    sectionLaw ν (fun a b => c * q a b) a = sectionLaw ν q a := by
  simp only [sectionLaw, sectionDensity_const_mul ν hq c hc0 hctop]

theorem measurable_sectionMass (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) :
    Measurable (sectionMass ν q) := hq.lintegral_prod_right

theorem measurable_sectionDensity (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) :
    Measurable (Function.uncurry (sectionDensity ν q)) := by
  exact hq.div ((measurable_sectionMass ν hq).comp measurable_fst)

/-- Every nonzero finite section has a normalized probability density. -/
theorem lintegral_sectionDensity_eq_one (ν : Measure B)
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (a : A) (h0 : sectionMass ν q a ≠ 0) (hfin : sectionMass ν q a ≠ ∞) :
    (∫⁻ b, sectionDensity ν q a b ∂ν) = 1 := by
  simp only [sectionDensity, div_eq_mul_inv]
  rw [lintegral_mul_const _ hq.of_uncurry_left]
  exact ENNReal.mul_inv_cancel h0 hfin

theorem isProbabilityMeasure_sectionLaw (ν : Measure B)
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (a : A) (h0 : sectionMass ν q a ≠ 0) (hfin : sectionMass ν q a ≠ ∞) :
    IsProbabilityMeasure (sectionLaw ν q a) := by
  constructor
  rw [sectionLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lintegral_sectionDensity_eq_one ν hq a h0 hfin

/-- Multiplication by the section mass cancels conditional normalization, including
zero-mass sections; only infinite-mass sections have to be excluded. -/
theorem sectionMass_mul_lintegral_sectionLaw (ν : Measure B)
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (a : A) (hfin : sectionMass ν q a ≠ ∞)
    {f : B → ℝ≥0∞} (hf : Measurable f) :
    sectionMass ν q a * (∫⁻ b, f b ∂sectionLaw ν q a) =
      ∫⁻ b, q a b * f b ∂ν := by
  by_cases h0 : sectionMass ν q a = 0
  · rw [h0, zero_mul]
    have hz : q a =ᵐ[ν] 0 := (lintegral_eq_zero_iff hq.of_uncurry_left).mp h0
    symm
    apply lintegral_eq_zero_iff (hq.of_uncurry_left.mul hf) |>.mpr
    filter_upwards [hz] with b hb
    simp [hb]
  · have hd : Measurable (sectionDensity ν q a) :=
      hq.of_uncurry_left.div measurable_const
    rw [sectionLaw, lintegral_withDensity_eq_lintegral_mul ν hd hf]
    have he : (fun b => sectionDensity ν q a b * f b) =
        (fun b => (sectionMass ν q a)⁻¹ * (q a b * f b)) := by
      funext b
      simp only [sectionDensity, div_eq_mul_inv]
      ac_rfl
    change sectionMass ν q a * (∫⁻ b, sectionDensity ν q a b * f b ∂ν) = _
    have hj : Measurable (fun b => q a b * f b) := hq.of_uncurry_left.mul hf
    rw [he, lintegral_const_mul _ hj,
      ← mul_assoc, ENNReal.mul_inv_cancel h0 hfin, one_mul]

/-- Conditional integration preserves measurability in the parameter. -/
theorem measurable_lintegral_sectionLaw (ν : Measure B) [SFinite ν]
    {q f : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (hf : Measurable (Function.uncurry f)) :
    Measurable (fun a => ∫⁻ b, f a b ∂sectionLaw ν q a) := by
  have he : (fun a => ∫⁻ b, f a b ∂sectionLaw ν q a) =
      (fun a => ∫⁻ b, sectionDensity ν q a b * f a b ∂ν) := by
    funext a
    exact lintegral_withDensity_eq_lintegral_mul ν
      ((measurable_sectionDensity ν hq).of_uncurry_left) hf.of_uncurry_left
  rw [he]
  exact ((measurable_sectionDensity ν hq).mul hf).lintegral_prod_right

/-- Exact disintegration of a product density into its section mass and normalized
section laws. The finite-mass hypothesis is only almost everywhere. -/
theorem lintegral_reassemble_sections (μ : Measure A) (ν : Measure B) [SFinite ν]
    {q f : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (hf : Measurable (Function.uncurry f))
    (hfin : ∀ᵐ a ∂μ, sectionMass ν q a ≠ ∞) :
    (∫⁻ a, ∫⁻ b, f a b ∂sectionLaw ν q a ∂μ.withDensity (sectionMass ν q)) =
      ∫⁻ p, f p.1 p.2 ∂(μ.prod ν).withDensity (Function.uncurry q) := by
  rw [lintegral_withDensity_eq_lintegral_mul μ (measurable_sectionMass ν hq)
    (measurable_lintegral_sectionLaw ν hq hf)]
  have hfp : Measurable (fun p : A × B => f p.1 p.2) := hf
  rw [lintegral_withDensity_eq_lintegral_mul (μ.prod ν) hq hfp]
  rw [lintegral_prod _ (hq.mul hfp).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hfin] with a ha
  exact sectionMass_mul_lintegral_sectionLaw ν hq a ha hf.of_uncurry_left

/-- The normalized section laws form a genuine measurable kernel. -/
def sectionKernel (ν : Measure B) [SFinite ν] (q : A → B → ℝ≥0∞) :
    ProbabilityTheory.Kernel A B :=
  (ProbabilityTheory.Kernel.const A ν).withDensity (sectionDensity ν q)

theorem sectionKernel_apply (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (a : A) :
    sectionKernel ν q a = sectionLaw ν q a := by
  rw [sectionKernel, ProbabilityTheory.Kernel.withDensity_apply _
    (measurable_sectionDensity ν hq)]
  rfl

theorem isMarkovKernel_sectionKernel (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (h0 : ∀ a, sectionMass ν q a ≠ 0) (hfin : ∀ a, sectionMass ν q a ≠ ∞) :
    ProbabilityTheory.IsMarkovKernel (sectionKernel ν q) := by
  constructor
  intro a
  rw [sectionKernel_apply ν hq]
  exact isProbabilityMeasure_sectionLaw ν hq a (h0 a) (hfin a)

/-- The conditional kernel is uniformly finite, including its zero/infinite section defaults. -/
theorem isFiniteKernel_sectionKernel (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) :
    ProbabilityTheory.IsFiniteKernel (sectionKernel ν q) := by
  constructor
  refine ⟨1, by simp, fun a => ?_⟩
  rw [sectionKernel_apply ν hq, sectionLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  simp only [sectionDensity, div_eq_mul_inv]
  rw [lintegral_mul_const _ hq.of_uncurry_left]
  exact ENNReal.mul_inv_le_one _

/-- Measure-level disintegration, ready to compose with conditional quantile laws.
Zero-mass fibers require no arbitrary probability choice because their marginal weight vanishes. -/
theorem compProd_sectionKernel (μ : Measure A) [SFinite μ]
    (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (hfin : ∀ᵐ a ∂μ, sectionMass ν q a ≠ ∞) :
    (μ.withDensity (sectionMass ν q)).compProd (sectionKernel ν q) =
      (μ.prod ν).withDensity (Function.uncurry q) := by
  let := isFiniteKernel_sectionKernel ν hq
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_compProd hf]
  simp_rw [sectionKernel_apply ν hq]
  have hf' : Measurable (Function.uncurry (fun a b => f (a, b))) :=
    hf.comp (measurable_fst.prodMk measurable_snd)
  exact lintegral_reassemble_sections μ ν hq hf' hfin

/-- Indicator density of a measurable region in a product space. -/
def setDensity (U : Set (A × B)) (a : A) (b : B) : ℝ≥0∞ :=
  U.indicator (fun _ => 1) (a, b)

theorem measurable_setDensity {U : Set (A × B)} (hU : MeasurableSet U) :
    Measurable (Function.uncurry (setDensity U)) :=
  (measurable_const.indicator hU).comp (measurable_fst.prodMk measurable_snd)

/-- The marginal density of a uniform region is exactly its section volume. -/
theorem sectionMass_setDensity (ν : Measure B) {U : Set (A × B)}
    (hU : MeasurableSet U) (a : A) :
    sectionMass ν (setDensity U) a = ν (Prod.mk a ⁻¹' U) := by
  have he : (setDensity U a) = (Prod.mk a ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext b
    rfl
  rw [sectionMass, he]
  exact lintegral_indicator_one (hU.preimage measurable_prodMk_left)

/-- The conditional law of a region is the normalized restricted volume of its fiber. -/
theorem sectionLaw_setDensity (ν : Measure B) {U : Set (A × B)}
    (hU : MeasurableSet U) (a : A) :
    sectionLaw ν (setDensity U) a =
      (ν (Prod.mk a ⁻¹' U))⁻¹ • ν.restrict (Prod.mk a ⁻¹' U) := by
  classical
  have he : sectionDensity ν (setDensity U) a =
      (Prod.mk a ⁻¹' U).indicator (fun _ => (ν (Prod.mk a ⁻¹' U))⁻¹) := by
    funext b
    rw [sectionDensity, sectionMass_setDensity ν hU]
    by_cases hb : (a, b) ∈ U <;> simp [setDensity, Set.indicator, hb]
  rw [sectionLaw, he, withDensity_indicator (hU.preimage measurable_prodMk_left),
    withDensity_const]

/-- Disintegrating the restriction to a region gives its volume marginal and uniform fibers. -/
theorem compProd_setSections (μ : Measure A) [SFinite μ]
    (ν : Measure B) [SFinite ν] {U : Set (A × B)} (hU : MeasurableSet U)
    (hfin : ∀ᵐ a ∂μ, ν (Prod.mk a ⁻¹' U) ≠ ∞) :
    (μ.withDensity (sectionMass ν (setDensity U))).compProd
      (sectionKernel ν (setDensity U)) = (μ.prod ν).restrict U := by
  have hfin' : ∀ᵐ a ∂μ, sectionMass ν (setDensity U) a ≠ ∞ := by
    simpa only [sectionMass_setDensity ν hU] using hfin
  rw [compProd_sectionKernel μ ν (measurable_setDensity hU) hfin']
  have he : Function.uncurry (setDensity U) = U.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext p
    rcases p with ⟨a, b⟩
    rfl
  rw [he, withDensity_indicator hU, withDensity_const, one_smul]

/-- Finite mass of the whole region discharges the only section-finiteness premise. -/
theorem compProd_setSections_of_finite (μ : Measure A) [SFinite μ]
    (ν : Measure B) [SFinite ν] {U : Set (A × B)} (hU : MeasurableSet U)
    (hfin : (μ.prod ν) U ≠ ∞) :
    (μ.withDensity (sectionMass ν (setDensity U))).compProd
      (sectionKernel ν (setDensity U)) = (μ.prod ν).restrict U := by
  apply compProd_setSections μ ν hU
  have hm := measurable_sectionMass ν (measurable_setDensity hU)
  have hi : (∫⁻ a, sectionMass ν (setDensity U) a ∂μ) ≠ ∞ := by
    simpa only [sectionMass_setDensity ν hU, ← Measure.prod_apply hU] using hfin
  filter_upwards [ae_lt_top hm hi] with a ha
  simpa only [sectionMass_setDensity ν hU] using ha.ne

/-- Positive, finite fibers form a measurable parameter set. -/
def goodSections (ν : Measure B) (q : A → B → ℝ≥0∞) : Set A :=
  {a | sectionMass ν q a ≠ 0 ∧ sectionMass ν q a ≠ ∞}

theorem measurableSet_goodSections (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) :
    MeasurableSet (goodSections ν q) := by
  exact (measurableSet_eq_fun (measurable_sectionMass ν hq) measurable_const).compl.inter
    (measurableSet_eq_fun (measurable_sectionMass ν hq) measurable_const).compl

/-- Complete the conditional kernel by any fixed point on exceptional fibers. -/
def completedSectionKernel (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (b₀ : B) :
    ProbabilityTheory.Kernel A B :=
  ProbabilityTheory.Kernel.piecewise (measurableSet_goodSections ν hq)
    (sectionKernel ν q) (ProbabilityTheory.Kernel.const A (Measure.dirac b₀))

theorem isMarkovKernel_completedSectionKernel (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (b₀ : B) :
    ProbabilityTheory.IsMarkovKernel (completedSectionKernel ν hq b₀) := by
  constructor
  intro a
  classical
  by_cases ha : a ∈ goodSections ν q
  · rw [completedSectionKernel, ProbabilityTheory.Kernel.piecewise_apply, ite_eq_left ha,
      sectionKernel_apply ν hq]
    exact isProbabilityMeasure_sectionLaw ν hq a ha.1 ha.2
  · rw [completedSectionKernel, ProbabilityTheory.Kernel.piecewise_apply, ite_eq_right ha]
    change IsProbabilityMeasure (Measure.dirac b₀)
    infer_instance

/-- Exceptional-fiber completion does not change the conditional law marginal-a.e. -/
theorem completedSectionKernel_ae_eq (μ : Measure A) (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (b₀ : B)
    (hfin : ∀ᵐ a ∂μ, sectionMass ν q a ≠ ∞) :
    completedSectionKernel ν hq b₀ =ᵐ[μ.withDensity (sectionMass ν q)] sectionKernel ν q := by
  apply (ae_withDensity_iff (measurable_sectionMass ν hq)).mpr
  filter_upwards [hfin] with a ha h0
  rw [completedSectionKernel, ProbabilityTheory.Kernel.piecewise_apply, ite_eq_left]
  exact ⟨h0, ha⟩

/-- Exact disintegration with a total Markov kernel, hence ready for measurable sampling. -/
theorem compProd_completedSectionKernel (μ : Measure A) [SFinite μ]
    (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (b₀ : B)
    (hfin : ∀ᵐ a ∂μ, sectionMass ν q a ≠ ∞) :
    (μ.withDensity (sectionMass ν q)).compProd (completedSectionKernel ν hq b₀) =
      (μ.prod ν).withDensity (Function.uncurry q) := by
  let := isMarkovKernel_completedSectionKernel ν hq b₀
  let := isFiniteKernel_sectionKernel ν hq
  rw [Measure.compProd_congr (completedSectionKernel_ae_eq μ ν hq b₀ hfin)]
  exact compProd_sectionKernel μ ν hq hfin

/-- The section-mass marginal of a finite positive region, after normalization,
is a probability measure. -/
theorem isProbabilityMeasure_normalizedSetMarginal (μ : Measure A) [SFinite μ]
    (ν : Measure B) [SFinite ν] {U : Set (A × B)} (hU : MeasurableSet U)
    (h0 : (μ.prod ν) U ≠ 0) (hfin : (μ.prod ν) U ≠ ∞) :
    IsProbabilityMeasure
      (((μ.prod ν) U)⁻¹ • μ.withDensity (sectionMass ν (setDensity U))) := by
  constructor
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  simp only [sectionMass_setDensity ν hU, ← Measure.prod_apply hU, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 hfin

/-- Exact probability-level disintegration of a uniform region. The total
Markov kernel still uses the unnormalized fiber density, so all normalization
of the whole region is confined to the prefix marginal. -/
theorem compProd_uniformSetSections (μ : Measure A) [SFinite μ]
    (ν : Measure B) [SFinite ν] {U : Set (A × B)} (hU : MeasurableSet U)
    (b₀ : B) (hfin : (μ.prod ν) U ≠ ∞) :
    (((μ.prod ν) U)⁻¹ • μ.withDensity (sectionMass ν (setDensity U))).compProd
      (completedSectionKernel ν (measurable_setDensity hU) b₀) =
      ((μ.prod ν) U)⁻¹ • (μ.prod ν).restrict U := by
  let := isMarkovKernel_completedSectionKernel ν (measurable_setDensity hU) b₀
  let := isFiniteKernel_sectionKernel ν (measurable_setDensity hU)
  have hm := measurable_sectionMass ν (measurable_setDensity hU)
  have hi : (∫⁻ a, sectionMass ν (setDensity U) a ∂μ) ≠ ∞ := by
    simpa only [sectionMass_setDensity ν hU, ← Measure.prod_apply hU] using hfin
  have hf : ∀ᵐ a ∂μ, sectionMass ν (setDensity U) a ≠ ∞ := by
    filter_upwards [ae_lt_top hm hi] with a ha
    exact ha.ne
  rw [Measure.compProd_smul_left,
    Measure.compProd_congr
      (completedSectionKernel_ae_eq μ ν (measurable_setDensity hU) b₀ hf),
    compProd_setSections_of_finite μ ν hU hfin]

end Problem358.NormalizedSections

end

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem358

/-- A density section normalized to have total mass one. -/
def normalizedDensityMeasure {A : Type*} (f : A × ℝ → ℝ≥0∞) (a : A) : Measure ℝ :=
  (∫⁻ t, f (a, t))⁻¹ • volume.withDensity (fun t => f (a, t))

lemma normalizedDensityMeasure_isProbability {A : Type*}
    (f : A × ℝ → ℝ≥0∞) (a : A)
    (hzero : (∫⁻ t, f (a, t)) ≠ 0) (htop : (∫⁻ t, f (a, t)) ≠ ∞) :
    IsProbabilityMeasure (normalizedDensityMeasure f a) := by
  constructor
  simp only [normalizedDensityMeasure, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel hzero htop

lemma measurable_normalizedDensityMeasure_apply {A : Type*} [MeasurableSpace A]
    {f : A × ℝ → ℝ≥0∞} (hf : Measurable f) {s : Set ℝ} (hs : MeasurableSet s) :
    Measurable (fun a => normalizedDensityMeasure f a s) := by
  simp only [normalizedDensityMeasure, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ hs]
  exact hf.lintegral_prod_right'.inv.mul hf.lintegral_prod_right'

lemma measurable_cdf_normalizedDensityMeasure {A : Type*} [MeasurableSpace A]
    {f : A × ℝ → ℝ≥0∞} (hf : Measurable f)
    (hzero : ∀ a, (∫⁻ t, f (a, t)) ≠ 0)
    (htop : ∀ a, (∫⁻ t, f (a, t)) ≠ ∞) (t : ℝ) :
    Measurable (fun a => cdf (normalizedDensityMeasure f a) t) := by
  have hprob : ∀ a, IsProbabilityMeasure (normalizedDensityMeasure f a) :=
    fun a => normalizedDensityMeasure_isProbability f a (hzero a) (htop a)
  have heq : (fun a => cdf (normalizedDensityMeasure f a) t) =
      fun a => (normalizedDensityMeasure f a (Set.Iic t)).toReal := by
    funext a
    let := hprob a
    exact cdf_eq_real (normalizedDensityMeasure f a) t
  rw [heq]
  exact (measurable_normalizedDensityMeasure_apply hf measurableSet_Iic).ennreal_toReal

/-- The normalized sections form a measurable kernel, even before probability
assumptions are imposed on their total masses. -/
def normalizedDensityKernel {A : Type*} [MeasurableSpace A]
    (f : A × ℝ → ℝ≥0∞) (hf : Measurable f) : Kernel A ℝ where
  toFun := normalizedDensityMeasure f
  measurable' := Measure.measurable_of_measurable_coe _
    (fun _ hs => measurable_normalizedDensityMeasure_apply hf hs)

@[simp] lemma normalizedDensityKernel_apply {A : Type*} [MeasurableSpace A]
    (f : A × ℝ → ℝ≥0∞) (hf : Measurable f) (a : A) :
    normalizedDensityKernel f hf a = normalizedDensityMeasure f a := rfl

lemma normalizedDensityKernel_isMarkov {A : Type*} [MeasurableSpace A]
    (f : A × ℝ → ℝ≥0∞) (hf : Measurable f)
    (hzero : ∀ a, (∫⁻ t, f (a, t)) ≠ 0)
    (htop : ∀ a, (∫⁻ t, f (a, t)) ≠ ∞) :
    IsMarkovKernel (normalizedDensityKernel f hf) := by
  constructor
  intro a
  exact normalizedDensityMeasure_isProbability f a (hzero a) (htop a)

lemma normalizedDensityMeasure_eq_withDensity {A : Type*} [MeasurableSpace A]
    {f : A × ℝ → ℝ≥0∞} (hf : Measurable f) (a : A) :
    normalizedDensityMeasure f a = volume.withDensity
      (fun t => (∫⁻ s, f (a, s))⁻¹ * f (a, t)) := by
  exact (withDensity_smul _ (hf.comp measurable_prodMk_left)).symm

lemma cdf_normalizedDensityMeasure_eq {A : Type*}
    (f : A × ℝ → ℝ≥0∞) (a : A)
    (hzero : (∫⁻ s, f (a, s)) ≠ 0) (htop : (∫⁻ s, f (a, s)) ≠ ∞) (t : ℝ) :
    cdf (normalizedDensityMeasure f a) t =
      (∫⁻ s, f (a, s)).toReal⁻¹ * (∫⁻ s in Set.Iic t, f (a, s)).toReal := by
  let := normalizedDensityMeasure_isProbability f a hzero htop
  rw [cdf_eq_real, measureReal_def, normalizedDensityMeasure,
    Measure.smul_apply, smul_eq_mul, withDensity_apply _ measurableSet_Iic,
    ENNReal.toReal_mul, ENNReal.toReal_inv]

lemma cdf_normalizedDensityMeasure_ofReal {A : Type*}
    (g : A × ℝ → ℝ) (a : A) (hg : Integrable (fun s => g (a, s)))
    (hnonneg : ∀ s, 0 ≤ g (a, s)) (hpos : 0 < ∫ s, g (a, s)) (t : ℝ) :
    cdf (normalizedDensityMeasure (fun p => ENNReal.ofReal (g p)) a) t =
      (∫ s in Set.Iic t, g (a, s)) / (∫ s, g (a, s)) := by
  have htotal : ENNReal.ofReal (∫ s, g (a, s)) = ∫⁻ s, ENNReal.ofReal (g (a, s)) :=
    ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall hnonneg)
  have hzero : (∫⁻ s, ENNReal.ofReal (g (a, s))) ≠ 0 := by
    rw [← htotal]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
  have htop : (∫⁻ s, ENNReal.ofReal (g (a, s))) ≠ ∞ := by
    rw [← htotal]
    exact ENNReal.ofReal_ne_top
  rw [cdf_normalizedDensityMeasure_eq _ _ hzero htop]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hnonneg) hg.aestronglyMeasurable]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hnonneg) hg.restrict.aestronglyMeasurable]
  ring

lemma measurableSet_validDensityParameters {A : Type*} [MeasurableSpace A]
    {f : A × ℝ → ℝ≥0∞} (hf : Measurable f) :
    MeasurableSet {a | (∫⁻ t, f (a, t)) ≠ 0 ∧ (∫⁻ t, f (a, t)) ≠ ∞} := by
  exact (measurableSet_eq_fun hf.lintegral_prod_right' measurable_const).compl.inter
    (measurableSet_eq_fun hf.lintegral_prod_right' measurable_const).compl

/-- A globally Markov version, using a fixed point mass at invalid density sections. -/
def probabilityDensityKernel {A : Type*} [MeasurableSpace A]
    (f : A × ℝ → ℝ≥0∞) (hf : Measurable f) (x₀ : ℝ) : Kernel A ℝ :=
  Kernel.piecewise (measurableSet_validDensityParameters hf)
    (normalizedDensityKernel f hf) (Kernel.const A (Measure.dirac x₀))

lemma probabilityDensityKernel_apply {A : Type*} [MeasurableSpace A]
    (f : A × ℝ → ℝ≥0∞) (hf : Measurable f) (x₀ : ℝ) (a : A) :
    probabilityDensityKernel f hf x₀ a =
      if (∫⁻ t, f (a, t)) ≠ 0 ∧ (∫⁻ t, f (a, t)) ≠ ∞
      then normalizedDensityMeasure f a else Measure.dirac x₀ := by
  classical
  rfl

instance probabilityDensityKernel_isMarkov {A : Type*} [MeasurableSpace A]
    (f : A × ℝ → ℝ≥0∞) (hf : Measurable f) (x₀ : ℝ) :
    IsMarkovKernel (probabilityDensityKernel f hf x₀) := by
  constructor
  intro a
  rw [probabilityDensityKernel_apply]
  split_ifs with h
  · exact normalizedDensityMeasure_isProbability f a h.1 h.2
  · infer_instance

lemma probabilityDensityKernel_apply_of_valid {A : Type*} [MeasurableSpace A]
    (f : A × ℝ → ℝ≥0∞) (hf : Measurable f) (x₀ : ℝ) (a : A)
    (hzero : (∫⁻ t, f (a, t)) ≠ 0) (htop : (∫⁻ t, f (a, t)) ≠ ∞) :
    probabilityDensityKernel f hf x₀ a = normalizedDensityMeasure f a := by
  rw [probabilityDensityKernel_apply, ite_eq_left ⟨hzero, htop⟩]

lemma measurable_cdf_probabilityDensityKernel {A : Type*} [MeasurableSpace A]
    (f : A × ℝ → ℝ≥0∞) (hf : Measurable f) (x₀ t : ℝ) :
    Measurable (fun a => cdf (probabilityDensityKernel f hf x₀ a) t) := by
  simp_rw [cdf_eq_real, measureReal_def]
  exact ((probabilityDensityKernel f hf x₀).measurable_coe measurableSet_Iic).ennreal_toReal

/-- The CDF of a real-valued Markov kernel is jointly measurable in the
parameter and the evaluation point. -/
lemma measurable_cdf_kernel_joint {A : Type*} [MeasurableSpace A]
    (κ : Kernel A ℝ) [IsMarkovKernel κ] :
    Measurable (fun p : A × ℝ => cdf (κ p.1) p.2) := by
  simp_rw [cdf_eq_real, measureReal_def]
  let κ' : Kernel (A × ℝ) ℝ := κ.comap Prod.fst measurable_fst
  have hset : MeasurableSet {p : (A × ℝ) × ℝ | p.2 ≤ p.1.2} :=
    measurableSet_le measurable_snd measurable_fst.snd
  exact (Kernel.measurable_kernel_prodMk_left (κ := κ') hset).ennreal_toReal

end Problem358

end

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Problem358.NormalizedSections

variable {A B S T : Type*}
  [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace S] [MeasurableSpace T]

/-- Under the section-mass marginal, zero and infinite fibers are negligible
as soon as the whole region has finite mass. This remains true after the
total-volume normalization. -/
theorem ae_goodSections_normalizedSetMarginal
    (μ : Measure A) [SFinite μ] (ν : Measure B) [SFinite ν]
    {U : Set (A × B)} (hU : MeasurableSet U)
    (hfin : (μ.prod ν) U ≠ ∞) :
    ∀ᵐ a ∂(((μ.prod ν) U)⁻¹ •
      μ.withDensity (sectionMass ν (setDensity U))),
      a ∈ goodSections ν (setDensity U) := by
  apply Measure.ae_smul_measure
  apply (ae_withDensity_iff
    (measurable_sectionMass ν (measurable_setDensity hU))).mpr
  have hi : (∫⁻ a, sectionMass ν (setDensity U) a ∂μ) ≠ ∞ := by
    simpa only [sectionMass_setDensity ν hU, ← Measure.prod_apply hU] using hfin
  filter_upwards [ae_lt_top
    (measurable_sectionMass ν (measurable_setDensity hU)) hi] with a ha h0
  exact ⟨h0, ha.ne⟩

/-- Sampling the normalized prefix marginal and then the uniform conditional
fiber gives exactly the uniform law on the whole region. Conditional laws are
required only on positive finite fibers; no choice on exceptional fibers is
part of the interface. -/
theorem map_prod_uniformSet_of_sectionLaws
    (μ : Measure A) [SFinite μ] (ν : Measure B) [SFinite ν]
    (σ : Measure S) [SFinite σ] (η : Measure T) [SFinite η]
    {U : Set (A × B)} (hU : MeasurableSet U)
    (hfin : (μ.prod ν) U ≠ ∞)
    (b₀ : B) (F : S → A) (Q : A → T → B)
    (hF : Measurable F) (hQ : Measurable (Function.uncurry Q))
    (hbase : Measure.map F σ =
      ((μ.prod ν) U)⁻¹ • μ.withDensity (sectionMass ν (setDensity U)))
    (hfiber : ∀ a ∈ goodSections ν (setDensity U),
      Measure.map (Q a) η = sectionLaw ν (setDensity U) a) :
    Measure.map (fun p : S × T => (F p.1, Q (F p.1) p.2)) (σ.prod η) =
      ((μ.prod ν) U)⁻¹ • (μ.prod ν).restrict U := by
  classical
  let ρ := ((μ.prod ν) U)⁻¹ • μ.withDensity (sectionMass ν (setDensity U))
  let κ := completedSectionKernel ν (measurable_setDensity hU) b₀
  let : IsMarkovKernel κ :=
    isMarkovKernel_completedSectionKernel ν (measurable_setDensity hU) b₀
  have hgood : ∀ᵐ s ∂σ, F s ∈ goodSections ν (setDensity U) := by
    apply ae_of_ae_map hF.aemeasurable
    rw [hbase]
    exact ae_goodSections_normalizedSetMarginal μ ν hU hfin
  have hlaw : ∀ᵐ s ∂σ,
      Measure.map (fun t => Q (F s) t) η = κ (F s) := by
    filter_upwards [hgood] with s hs
    rw [hfiber (F s) hs]
    dsimp [κ]
    rw [completedSectionKernel, Kernel.piecewise_apply, ite_eq_left hs,
      sectionKernel_apply ν (measurable_setDensity hU)]
  have hG : Measurable (fun p : S × T => Q (F p.1) p.2) :=
    hQ.comp ((hF.comp measurable_fst).prodMk measurable_snd)
  have h := TriangularSampling.map_prod_eq_compProd
    σ η ρ κ F (fun p => Q (F p.1) p.2) hF hG hbase hlaw
  exact h.trans (compProd_uniformSetSections μ ν hU b₀ hfin)

/-- Arbitrary joint densities have good fibers almost everywhere under their
section-mass marginal. Finite section mass is only required base-almost everywhere. -/
theorem ae_goodSections_smul_marginal
    (μ : Measure A) (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (c : ℝ≥0∞) (hfin : ∀ᵐ a ∂μ, sectionMass ν q a ≠ ∞) :
    ∀ᵐ a ∂c • μ.withDensity (sectionMass ν q), a ∈ goodSections ν q := by
  apply Measure.ae_smul_measure
  apply (ae_withDensity_iff (measurable_sectionMass ν hq)).mpr
  filter_upwards [hfin] with a ha h0
  exact ⟨h0, ha⟩

/-- Density version of the sampling bridge, applicable when the joint density
is a residual-tail volume rather than the indicator of a region. All global
normalization is confined to the scalar `c` and the prefix marginal. -/
theorem map_prod_smulDensity_of_sectionLaws
    (μ : Measure A) [SFinite μ] (ν : Measure B) [SFinite ν]
    (σ : Measure S) [SFinite σ] (η : Measure T) [SFinite η]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (c : ℝ≥0∞) (hfin : ∀ᵐ a ∂μ, sectionMass ν q a ≠ ∞)
    (b₀ : B) (F : S → A) (Q : A → T → B)
    (hF : Measurable F) (hQ : Measurable (Function.uncurry Q))
    (hbase : Measure.map F σ = c • μ.withDensity (sectionMass ν q))
    (hfiber : ∀ a ∈ goodSections ν q,
      Measure.map (Q a) η = sectionLaw ν q a) :
    Measure.map (fun p : S × T => (F p.1, Q (F p.1) p.2)) (σ.prod η) =
      c • (μ.prod ν).withDensity (Function.uncurry q) := by
  classical
  let ρ := c • μ.withDensity (sectionMass ν q)
  let κ := completedSectionKernel ν hq b₀
  let : IsMarkovKernel κ := isMarkovKernel_completedSectionKernel ν hq b₀
  have hgood : ∀ᵐ s ∂σ, F s ∈ goodSections ν q := by
    apply ae_of_ae_map hF.aemeasurable
    rw [hbase]
    exact ae_goodSections_smul_marginal μ ν hq c hfin
  have hlaw : ∀ᵐ s ∂σ, Measure.map (Q (F s)) η = κ (F s) := by
    filter_upwards [hgood] with s hs
    rw [hfiber (F s) hs]
    dsimp [κ]
    rw [completedSectionKernel, Kernel.piecewise_apply, ite_eq_left hs,
      sectionKernel_apply ν hq]
  have hG : Measurable (fun p : S × T => Q (F p.1) p.2) :=
    hQ.comp ((hF.comp measurable_fst).prodMk measurable_snd)
  have h := TriangularSampling.map_prod_eq_compProd
    σ η ρ κ F (fun p => Q (F p.1) p.2) hF hG hbase hlaw
  apply h.trans
  change (c • μ.withDensity (sectionMass ν q)).compProd
    (completedSectionKernel ν hq b₀) = _
  rw [Measure.compProd_smul_left, compProd_completedSectionKernel μ ν hq b₀ hfin]

end Problem358.NormalizedSections

end

end OAI
