import OAI.Analysis.RotationWeights.BorelTransport

namespace OAI

noncomputable section

universe uX uκ uP uι

namespace ContinuousCircleWeight
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

open MeasureTheory Set Filter Topology Algebra Submodule
open scoped BigOperators ComplexConjugate

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X]

theorem compactMap_integrable (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ)) :
    Integrable f μ :=
  Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (ae_of_all _ f.norm_coe_le_norm)

theorem probability_integral_lipschitz (μ : ProbabilityMeasure X) :
    LipschitzWith 1 (fun f : C(X, ℂ) => ∫ x, f x ∂(μ : Measure X)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [← integral_sub (compactMap_integrable _ f) (compactMap_integrable _ g)]
  simpa using (norm_integral_le_of_norm_le_const
    (ae_of_all (μ : Measure X) (fun x => (f - g).norm_coe_le_norm x)))

theorem probability_tendsto_of_dense_span {κ : Type uκ} (l : Filter κ)
    (s : Set C(X, ℂ)) (hs : (span ℂ s).topologicalClosure = ⊤)
    (μs : κ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (h : ∀ f ∈ s, Tendsto (fun j => ∫ x, f x ∂(μs j : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X)))) :
    Tendsto μs l (𝓝 μ) := by
  have heq : Equicontinuous
      (fun j (f : C(X, ℂ)) => ∫ x, f x ∂(μs j : Measure X)) :=
    (LipschitzWith.uniformEquicontinuous _ 1
      (fun j => probability_integral_lipschitz (μs j))).equicontinuous
  have hc := heq.isClosed_setOfPred_tendsto (l := l) (probability_integral_lipschitz μ).continuous
  have hspan : (↑(span ℂ s) : Set C(X, ℂ)) ⊆
      {f | Tendsto (fun j => ∫ x, f x ∂(μs j : Measure X)) l
        (𝓝 (∫ x, f x ∂(μ : Measure X)))} := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf => exact h f hf
    | zero => simpa using (tendsto_const_nhds (x := (0 : ℂ)))
    | add f g _ _ hf hg =>
      have hw (ν : ProbabilityMeasure X) :
          (∫ x, (f + g) x ∂(ν : Measure X)) =
            (∫ x, f x ∂(ν : Measure X)) + ∫ x, g x ∂(ν : Measure X) :=
        integral_add (compactMap_integrable _ f) (compactMap_integrable _ g)
      simpa only [Set.mem_ofPred_eq, hw] using hf.add hg
    | smul a f _ hf =>
      have hw (ν : ProbabilityMeasure X) :
          (∫ x, (a • f) x ∂(ν : Measure X)) = a • ∫ x, f x ∂(ν : Measure X) :=
        integral_smul a _
      simpa only [Set.mem_ofPred_eq, hw] using hf.const_smul a
  have hall := closure_minimal hspan hc
  rw [← Submodule.topologicalClosure_coe, hs, Submodule.top_coe] at hall
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr
  intro f
  exact hall (a := f.toContinuousMap) (mem_univ _)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma not_mem_frontier_ge_of_continuousAt {f : X → ℝ} {x : X} {t : ℝ}
    (hc : ContinuousAt f x) (hne : f x ≠ t) :
    x ∉ frontier {z | t ≤ f z} := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have he : ∀ᶠ z in 𝓝 x, f z < t := hc.eventually (gt_mem_nhds hlt)
    intro h
    have hd := h.1
    rw [mem_closure_iff_nhds] at hd
    have := hd {z | f z < t} he
    obtain ⟨z, hz, hzt⟩ := this
    exact (not_le_of_gt (show f z < t from hz)) (show t ≤ f z from hzt)
  · have he : {z | t ≤ f z} ∈ 𝓝 x := mem_of_superset (hc.eventually (lt_mem_nhds hgt))
      (fun z hz => show t ≤ f z from le_of_lt hz)
    exact fun h => h.2 (mem_interior_iff_mem_nhds.mpr he)

omit [BorelSpace X] [CompactSpace X] in
lemma ae_null_frontier_ge (μ : Measure X) [SFinite μ] {f : X → ℝ}
    (hf : Measurable f) (hc : ∀ᵐ x ∂μ, ContinuousAt f x) :
    ∀ᵐ t : ℝ, μ (frontier {x | t ≤ f x}) = 0 := by
  have hcount := Measure.countable_meas_level_set_pos (μ := μ) hf
  have hzero : ∀ᵐ t : ℝ, μ {x | f x = t} = 0 := by
    have h := hcount.measure_zero (volume : Measure ℝ)
    rw [measure_eq_zero_iff_ae_notMem] at h
    simpa only [mem_ofPred_eq, not_lt, nonpos_iff_eq_zero] using h
  filter_upwards [hzero] with t ht
  rw [measure_eq_zero_iff_ae_notMem] at ht ⊢
  filter_upwards [hc, ht] with x hx hxt
  exact not_mem_frontier_ge_of_continuousAt hx hxt

omit [CompactSpace X] in

theorem tendsto_integral_nn_of_weak_of_ae_continuous [HasOuterApproxClosed X]
    {κ : Type uκ} {l : Filter κ} [l.IsCountablyGenerated]
    (μs : κ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (f : X → ℝ)
    (hf : Measurable f) (hc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x)
    (hnn : ∀ x, 0 ≤ f x) (M : ℝ) (hb : ∀ x, f x ≤ M) :
    Tendsto (fun n => ∫ x, f x ∂(μs n : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  have hfi (ν : ProbabilityMeasure X) : Integrable f (ν : Measure X) :=
    Integrable.of_bound hf.aestronglyMeasurable M
      (ae_of_all _ (fun x => by simpa only [Real.norm_of_nonneg (hnn x)] using hb x))
  have heq (ν : ProbabilityMeasure X) : (∫ x, f x ∂(ν : Measure X)) =
      ∫ t in Ioc 0 M, (ν : Measure X).real {x | t ≤ f x} :=
    (hfi ν).integral_eq_integral_Ioc_meas_le (ae_of_all _ hnn) (ae_of_all _ hb)
  simp_rw [heq]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · apply Eventually.of_forall
    intro n
    have hm : Antitone (fun t : ℝ => (μs n : Measure X) {x | t ≤ f x}) := by
      intro s t hst
      exact measure_mono (fun x hx => hst.trans hx)
    exact hm.measurable.ennreal_toReal.aestronglyMeasurable
  · exact Eventually.of_forall (fun n => ae_of_all _ (fun t =>
      by simpa only [Measure.real, Real.norm_of_nonneg ENNReal.toReal_nonneg] using
        (measureReal_le_one (μ := (μs n : Measure X)) (s := {x | t ≤ f x}))))
  · exact integrable_const _
  · filter_upwards [ae_restrict_of_ae (ae_null_frontier_ge (μ : Measure X) hf hc)] with t ht
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ ht)

omit [CompactSpace X] in

theorem tendsto_integral_of_weak_of_ae_continuous [HasOuterApproxClosed X]
    {κ : Type uκ} {l : Filter κ} [l.IsCountablyGenerated]
    (μs : κ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (f : X → ℝ)
    (hf : Measurable f) (hc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x)
    (M : ℝ) (hb : ∀ x, ‖f x‖ ≤ M) :
    Tendsto (fun n => ∫ x, f x ∂(μs n : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  have hb' (x : X) : -M ≤ f x ∧ f x ≤ M := abs_le.mp (hb x)
  have hnn (x : X) : 0 ≤ f x + M := by linarith [(hb' x).1]
  have hupper (x : X) : f x + M ≤ 2 * M := by linarith [(hb' x).2]
  have hc' : ∀ᵐ x ∂(μ : Measure X), ContinuousAt (fun x => f x + M) x :=
    hc.mono (fun _ hx => hx.add continuousAt_const)
  have h := tendsto_integral_nn_of_weak_of_ae_continuous μs μ hμ (fun x => f x + M)
    (hf.add_const M) hc' hnn (2 * M) hupper
  have heq (ν : ProbabilityMeasure X) : (∫ x, f x + M ∂(ν : Measure X)) =
      (∫ x, f x ∂(ν : Measure X)) + M := by
    rw [integral_add (Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hb))
      (integrable_const _)]
    simp
  simp_rw [heq] at h
  simpa only [add_sub_cancel_right] using h.sub_const M

omit [CompactSpace X] in
theorem tendsto_integral_complex_of_weak_of_ae_continuous [HasOuterApproxClosed X]
    {κ : Type uκ} {l : Filter κ} [l.IsCountablyGenerated]
    (μs : κ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (f : X → ℂ)
    (hf : Measurable f) (hc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x)
    (M : ℝ) (hb : ∀ x, ‖f x‖ ≤ M) :
    Tendsto (fun n => ∫ x, f x ∂(μs n : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  have hfi (ν : ProbabilityMeasure X) : Integrable f (ν : Measure X) :=
    Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hb)
  have hre := tendsto_integral_of_weak_of_ae_continuous μs μ hμ (fun x => (f x).re)
    (Complex.measurable_re.comp hf)
    (hc.mono (fun _ hx => Complex.continuous_re.continuousAt.comp hx)) M
    (fun x => (Complex.abs_re_le_norm _).trans (hb x))
  have him := tendsto_integral_of_weak_of_ae_continuous μs μ hμ (fun x => (f x).im)
    (Complex.measurable_im.comp hf)
    (hc.mono (fun _ hx => Complex.continuous_im.continuousAt.comp hx)) M
    (fun x => (Complex.abs_im_le_norm _).trans (hb x))
  simp_rw [show ∀ ν : ProbabilityMeasure X,
    (∫ x, (f x).re ∂(ν : Measure X)) = (∫ x, f x ∂(ν : Measure X)).re from
      fun ν => integral_re (hfi ν)] at hre
  simp_rw [show ∀ ν : ProbabilityMeasure X,
    (∫ x, (f x).im ∂(ν : Measure X)) = (∫ x, f x ∂(ν : Measure X)).im from
      fun ν => integral_im (hfi ν)] at him
  have hrec := Complex.continuous_ofReal.continuousAt.tendsto.comp hre
  have himc := Complex.continuous_ofReal.continuousAt.tendsto.comp him
  simpa only [Function.comp_apply, Complex.re_add_im] using hrec.add (himc.mul_const Complex.I)

def withParameter {P : Type uP} [TopologicalSpace P] [MeasurableSpace P]
    [BorelSpace P] (ν : ProbabilityMeasure X) (b : P) : ProbabilityMeasure (X × P) :=
  ν.map (fun x => (x, b))

omit [CompactSpace X] in
theorem integral_withParameter [SecondCountableTopology X]
    {P : Type uP} [TopologicalSpace P] [SecondCountableTopology P] [MeasurableSpace P]
    [BorelSpace P] (ν : ProbabilityMeasure X) (b : P) (f : C(X × P, ℂ)) :
    (∫ z, f z ∂(withParameter ν b : Measure (X × P))) =
      ∫ x, f (x, b) ∂(ν : Measure X) := by
  exact integral_map (measurable_id.prodMk measurable_const).aemeasurable
    f.continuous.aestronglyMeasurable

theorem probability_tendsto_withParameter [SecondCountableTopology X]
    {P : Type uP} [TopologicalSpace P] [SecondCountableTopology P]
    [MeasurableSpace P] [BorelSpace P]
    {κ : Type uκ} {l : Filter κ} {νs : κ → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hν : Tendsto νs l (𝓝 ν)) {bs : κ → P} {b : P} (hb : Tendsto bs l (𝓝 b)) :
    Tendsto (fun n => withParameter (νs n) (bs n)) l (𝓝 (withParameter ν b)) := by
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr
  intro f
  let g : C(P, C(X, ℂ)) :=
    (f.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry
  have hgb : Tendsto (fun n => g (bs n)) l (𝓝 (g b)) := g.continuous.continuousAt.tendsto.comp hb
  have hfix : Tendsto (fun n => ∫ x, g b x ∂(νs n : Measure X)) l
      (𝓝 (∫ x, g b x ∂(ν : Measure X))) := by
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hν
      (BoundedContinuousFunction.mkOfCompact (g b))
  have hdist : Tendsto (fun n => dist (∫ x, g b x ∂(νs n : Measure X))
      (∫ x, g (bs n) x ∂(νs n : Measure X))) l (𝓝 0) := by
    apply squeeze_zero (g := fun n => dist (g b) (g (bs n))) (fun _ => dist_nonneg)
      (fun n => by simpa only [NNReal.coe_one, one_mul] using
        (probability_integral_lipschitz (νs n)).dist_le_mul (g b) (g (bs n)))
    simpa only [dist_comm] using (tendsto_iff_dist_tendsto_zero.mp hgb)
  have h := tendsto_of_tendsto_of_dist hfix hdist
  change Tendsto (fun n => ∫ z, f.toContinuousMap z ∂(withParameter (νs n) (bs n) : Measure (X × P))) l
    (𝓝 (∫ z, f.toContinuousMap z ∂(withParameter ν b : Measure (X × P))))
  simpa only [integral_withParameter, g, ContinuousMap.curry_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, Prod.swap_prod_mk] using h

namespace Sampling

abbrev CircleX := AddCircle (1 : ℝ)
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {ι : Type uι} [Fintype ι]

def torusFourier (a : ι → ℤ) : C(ι → CircleX, ℂ) where
  toFun x := ∏ i, fourier (a i) (x i)
  continuous_toFun := by fun_prop

@[simp] theorem torusFourier_apply (a : ι → ℤ) (x : ι → CircleX) :
    torusFourier a x = ∏ i, fourier (a i) (x i) := rfl

@[simp] theorem torusFourier_zero : torusFourier (0 : ι → ℤ) = 1 := by
  ext x
  simp

theorem torusFourier_add (a b : ι → ℤ) :
    torusFourier (a + b) = torusFourier a * torusFourier b := by
  ext x
  simp only [torusFourier_apply, Pi.add_apply, fourier_add, ContinuousMap.mul_apply]
  exact Finset.prod_mul_distrib

theorem torusFourier_neg (a : ι → ℤ) :
    torusFourier (-a) = star (torusFourier a) := by
  ext x
  change (∏ i, fourier (-a i) (x i)) = conj (∏ i, fourier (a i) (x i))
  simp only [fourier_neg, map_prod]

def torusFourierSubalgebra : StarSubalgebra ℂ C(ι → CircleX, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range torusFourier)
  star_mem' := by
    change Algebra.adjoin ℂ (range (torusFourier (ι := ι))) ≤
      star (Algebra.adjoin ℂ (range (torusFourier (ι := ι))))
    refine adjoin_le ?_
    rintro - ⟨a, rfl⟩
    exact subset_adjoin ⟨-a, torusFourier_neg a⟩

theorem torusFourierSubalgebra_coe :
    Subalgebra.toSubmodule (torusFourierSubalgebra (ι := ι)).toSubalgebra =
      span ℂ (range (torusFourier (ι := ι))) := by
  apply adjoin_eq_span_of_subset
  refine Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0, torusFourier_zero⟩ ?_ hx
  rintro - - - - ⟨a, rfl⟩ ⟨b, rfl⟩
  exact ⟨a + b, torusFourier_add a b⟩

theorem torusFourier_single [DecidableEq ι] (i : ι) (x : ι → CircleX) :
    torusFourier (Pi.single i (1 : ℤ)) x = fourier 1 (x i) := by
  rw [torusFourier_apply, Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem torusFourierSubalgebra_separatesPoints :
    (torusFourierSubalgebra (ι := ι)).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  refine ⟨_, ⟨torusFourier (Pi.single i 1), subset_adjoin ⟨_, rfl⟩, rfl⟩, ?_⟩
  change torusFourier (Pi.single i 1) x ≠ torusFourier (Pi.single i 1) y
  rw [torusFourier_single, torusFourier_single, fourier_one, fourier_one]
  intro h
  apply hi
  exact AddCircle.injective_toCircle (by norm_num) (Subtype.coe_injective h)

theorem span_torusFourier_closure_eq_top :
    (span ℂ (range (torusFourier (ι := ι)))).topologicalClosure = ⊤ := by
  rw [← torusFourierSubalgebra_coe]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      torusFourierSubalgebra torusFourierSubalgebra_separatesPoints)

theorem integral_fourier (n : ℤ) :
    (∫ x : CircleX, fourier n x ∂AddCircle.haarAddCircle) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

def circleHaar : ProbabilityMeasure CircleX :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

def torusHaar : ProbabilityMeasure (ι → CircleX) :=
  ⟨Measure.pi (fun _ => AddCircle.haarAddCircle), inferInstance⟩

theorem integral_torusFourier (a : ι → ℤ) :
    (∫ x, torusFourier a x ∂(torusHaar (ι := ι) : Measure (ι → CircleX))) =
      if a = 0 then 1 else 0 := by
  classical
  change (∫ x : ι → CircleX, ∏ i, fourier (a i) (x i)
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) = _
  rw [integral_fintype_prod_eq_prod]
  simp_rw [integral_fourier]
  split_ifs with ha
  · subst a
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa using hi

omit [Fintype ι] in
theorem fourier_sum (s : Finset ι) (a : ι → ℤ) (x : CircleX) :
    fourier (∑ i ∈ s, a i) x = ∏ i ∈ s, fourier (a i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, fourier_add, ih]

def characterCurve (q : ι → ℤ) : C(CircleX, ι → CircleX) where
  toFun x i := q i • x
  continuous_toFun := by fun_prop

theorem torusFourier_curve (a q : ι → ℤ) (x : CircleX) :
    torusFourier a (characterCurve q x) = fourier (∑ i, a i * q i) x := by
  rw [fourier_sum]
  apply Finset.prod_congr rfl
  intro i _
  simp only [characterCurve, ContinuousMap.coe_mk, fourier_apply, mul_zsmul]

def curveLaw (q : ι → ℤ) : ProbabilityMeasure (ι → CircleX) :=
  circleHaar.map (characterCurve q)

theorem integral_curveLaw (q : ι → ℤ) (f : C(ι → CircleX, ℂ)) :
    (∫ x, f x ∂(curveLaw q : Measure (ι → CircleX))) =
      ∫ x : CircleX, f (characterCurve q x) ∂AddCircle.haarAddCircle := by
  exact integral_map (characterCurve q).continuous.measurable.aemeasurable
    f.continuous.aestronglyMeasurable

theorem integral_curveLaw_torusFourier (q a : ι → ℤ) :
    (∫ x, torusFourier a x ∂(curveLaw q : Measure (ι → CircleX))) =
      if ∑ i, a i * q i = 0 then 1 else 0 := by
  rw [integral_curveLaw]
  simp_rw [torusFourier_curve]
  exact integral_fourier _

theorem eventually_sum_ne_zero_of_separated [LinearOrder ι]
    {κ : Type uκ} {l : Filter κ} (q : κ → ι → ℝ)
    (hq : ∀ n i, q n i ≠ 0)
    (hsep : ∀ i j, i < j → Tendsto (fun n => q n i / q n j) l (𝓝 0))
    (a : ι → ℝ) (ha : a ≠ 0) :
    ∀ᶠ n in l, ∑ i, a i * q n i ≠ 0 := by
  classical
  let s : Finset ι := Finset.univ.filter (fun i => a i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    exact ⟨i, by simpa [s] using hi⟩
  let j := s.max' hs
  have hj : a j ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have hlim (i : ι) : Tendsto (fun n => a i * q n i / q n j) l
      (𝓝 (if i = j then a j else 0)) := by
    by_cases hi : i = j
    · subst i
      simpa [hq] using (tendsto_const_nhds (x := a j) (f := l))
    · rw [ite_eq_right hi]
      by_cases hai : a i = 0
      · simpa [hai] using (tendsto_const_nhds (x := (0 : ℝ)) (f := l))
      · have his : i ∈ s := by simp [s, hai]
        have hij : i < j := lt_of_le_of_ne (Finset.le_max' s i his) hi
        simpa only [mul_zero, mul_div_assoc] using (hsep i j hij).const_mul (a i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
  filter_upwards [hsum.eventually_ne hj] with n hn
  intro he
  apply hn
  rw [← Finset.sum_div, he, zero_div]

theorem curveLaw_tendsto_of_nonresonance {κ : Type uκ} {l : Filter κ}
    {q : κ → ι → ℤ}
    (h : ∀ a : ι → ℤ, a ≠ 0 → ∀ᶠ n in l, ∑ i, a i * q n i ≠ 0) :
    Tendsto (fun n => curveLaw (q n)) l (𝓝 (torusHaar (ι := ι))) := by
  apply probability_tendsto_of_dense_span l (Set.range torusFourier)
    span_torusFourier_closure_eq_top
  rintro _ ⟨a, rfl⟩
  simp_rw [integral_curveLaw_torusFourier, integral_torusFourier]
  by_cases ha : a = 0
  · subst a
    simpa using (tendsto_const_nhds (x := (1 : ℂ)))
  · rw [ite_eq_right ha]
    apply tendsto_const_nhds.congr'
    filter_upwards [h a ha] with n hn
    simp [hn]

theorem curveLaw_tendsto_of_separated [LinearOrder ι]
    {κ : Type uκ} {l : Filter κ} {q : κ → ι → ℤ}
    (hq : ∀ n i, q n i ≠ 0)
    (hsep : ∀ i j, i < j →
      Tendsto (fun n => (q n i : ℝ) / q n j) l (𝓝 0)) :
    Tendsto (fun n => curveLaw (q n)) l (𝓝 (torusHaar (ι := ι))) := by
  apply curveLaw_tendsto_of_nonresonance
  intro a ha
  have har : (fun i => (a i : ℝ)) ≠ 0 := by
    intro he
    apply ha
    ext i
    have hh : (a i : ℝ) = 0 := congrFun he i
    change a i = 0
    exact_mod_cast hh
  have hqr : ∀ n i, (q n i : ℝ) ≠ 0 := by
    intro n i
    exact_mod_cast hq n i
  filter_upwards [eventually_sum_ne_zero_of_separated
    (fun n i => (q n i : ℝ)) hqr hsep (fun i => (a i : ℝ)) har] with n hn
  exact_mod_cast hn

theorem separated_of_successive {κ : Type uκ} {l : Filter κ} {r : ℕ}
    (q : κ → ℕ → ℝ) (hq : ∀ n i, i < r → q n i ≠ 0)
    (hsep : ∀ i, i + 1 < r → Tendsto (fun n => q n (i + 1) / q n i) l atTop) :
    ∀ i j, i < j → j < r → Tendsto (fun n => q n i / q n j) l (𝓝 0) := by
  intro i j
  induction j with
  | zero => omega
  | succ j ih =>
    intro hij hjr
    have hnext : Tendsto (fun n => q n j / q n (j + 1)) l (𝓝 0) := by
      simpa only [Function.comp_def, inv_div] using
        tendsto_inv_atTop_zero.comp (hsep j hjr)
    by_cases heq : i = j
    · simpa [heq] using hnext
    · have hik : i < j := by omega
      have hlim := (ih hik (by omega)).mul hnext
      simp only [mul_zero] at hlim
      convert hlim using 1
      ext n
      field_simp [hq n j (by omega)]

theorem curveLaw_tendsto_of_successiveRatios {κ : Type uκ} {l : Filter κ} {r : ℕ}
    (q : κ → ℕ → ℤ) (hq : ∀ n i, i < r → 0 < q n i)
    (hsep : ∀ i, i + 1 < r →
      Tendsto (fun n => (q n (i + 1) : ℝ) / q n i) l atTop) :
    Tendsto (fun n => curveLaw (fun i : Fin r => q n i)) l (𝓝 (torusHaar (ι := Fin r))) := by
  apply curveLaw_tendsto_of_separated
  · intro n i
    exact ne_of_gt (hq n i i.isLt)
  · intro i j hij
    apply separated_of_successive (fun n i => (q n i : ℝ)) _ hsep i j hij j.isLt
    intro n i hi
    exact_mod_cast ne_of_gt (hq n i hi)

theorem circle_approximation_with_parameters
    {P : Type uP} [MetricSpace P] [CompactSpace P] [MeasurableSpace P] [BorelSpace P]
    {κ : Type uκ} {l : Filter κ} [l.IsCountablyGenerated] {r : ℕ}
    (q : κ → ℕ → ℤ) (hq : ∀ n i, i < r → 0 < q n i)
    (hsep : ∀ i, i + 1 < r →
      Tendsto (fun n => (q n (i + 1) : ℝ) / q n i) l atTop)
    {bs : κ → P} {b : P} (hb : Tendsto bs l (𝓝 b))
    (Φ : ((Fin r → CircleX) × P) → ℂ) (hΦ : Measurable Φ)
    (hc : ∀ᵐ z ∂(withParameter (torusHaar (ι := Fin r)) b : Measure _), ContinuousAt Φ z)
    (M : ℝ) (hM : ∀ z, ‖Φ z‖ ≤ M) :
    Tendsto (fun n => ∫ x : CircleX, Φ (characterCurve (fun i : Fin r => q n i) x, bs n)
      ∂AddCircle.haarAddCircle) l
      (𝓝 (∫ s, Φ (s, b) ∂(torusHaar (ι := Fin r) : Measure _))) := by
  have hν := probability_tendsto_withParameter (curveLaw_tendsto_of_successiveRatios q hq hsep) hb
  have h := tendsto_integral_complex_of_weak_of_ae_continuous
    (fun n => withParameter (curveLaw (fun i : Fin r => q n i)) (bs n))
    (withParameter (torusHaar (ι := Fin r)) b) hν Φ hΦ hc M hM
  have heq (ν : ProbabilityMeasure (Fin r → CircleX)) (b : P) :
      (∫ z, Φ z ∂(withParameter ν b : Measure _)) = ∫ s, Φ (s, b) ∂(ν : Measure _) :=
    integral_map (measurable_id.prodMk measurable_const).aemeasurable hΦ.aestronglyMeasurable
  simp_rw [heq] at h
  have heq' (n : κ) : (∫ s, Φ (s, bs n) ∂(curveLaw (fun i : Fin r => q n i) : Measure _)) =
      ∫ x : CircleX, Φ (characterCurve (fun i : Fin r => q n i) x, bs n)
        ∂AddCircle.haarAddCircle :=
    integral_map (characterCurve _).continuous.measurable.aemeasurable
      (hΦ.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  simpa only [heq'] using h

end Sampling
end ContinuousCircleWeight

end

end OAI
