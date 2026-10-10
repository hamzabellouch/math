import Mathlib
import OAI.Probability.Perceptron.Interpolation.FiniteOverlap

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma expNegENNReal_finite {u : ℝ≥0∞} (hu : u ≠ ⊤) :
    expNegENNReal u = Real.exp (-u.toReal) := by
  unfold expNegENNReal
  rw [← EReal.coe_ennreal_toReal hu,← EReal.coe_neg,EReal.exp_coe,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

@[simp] lemma expNegENNReal_top : expNegENNReal ⊤ = 0 := by simp [expNegENNReal]

def poissonLaplace {S : Type*} [MeasurableSpace S] (f : S → ℝ) (η : Measure S) : ℝ :=
  expNegENNReal (∫⁻ x, ENNReal.ofReal (f x) ∂η)

lemma poissonLaplace_measurable {S : Type*} [MeasurableSpace S]
    {f : S → ℝ} (hf : Measurable f) : Measurable (poissonLaplace f) :=
  expNegENNReal_continuous.measurable.comp (Measure.measurable_lintegral hf.ennreal_ofReal)

lemma poissonLaplace_bounds {S : Type*} [MeasurableSpace S]
    (f : S → ℝ) (η : Measure S) : 0 ≤ poissonLaplace f η ∧ poissonLaplace f η ≤ 1 :=
  expNegENNReal_bound _

lemma poissonLaplace_finitePointMeasure {S : Type*} [MeasurableSpace S]
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (n : ℕ) (x : Fin n → S) :
    poissonLaplace f (finitePointMeasure n x) = ∏ i : Fin n, Real.exp (-f (x i)) := by
  simp only [poissonLaplace,finitePointMeasure,lintegral_finsetSum_measure]
  simp_rw [lintegral_dirac' _ hf.ennreal_ofReal]
  rw [expNegENNReal_finite (ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)),ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_ofReal (hf0 _)]
  rw [← Finset.sum_neg_distrib,Real.exp_sum]

lemma finitePoissonLaw_laplace {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ η, poissonLaplace f η ∂finitePoissonLaw r ν =
      Real.exp ((r : ℝ) * ((∫ x, Real.exp (-f x) ∂ν) - 1)) := by
  have hi : Integrable (poissonLaplace f) (finitePoissonLaw r ν) := by
    apply Integrable.of_bound (poissonLaplace_measurable hf).aestronglyMeasurable 1
    exact ae_of_all _ fun η => by
      rw [Real.norm_eq_abs,abs_of_nonneg (poissonLaplace_bounds f η).1]
      exact (poissonLaplace_bounds f η).2
  rw [finitePoissonLaw,integral_sum_measure hi]
  simp_rw [integral_smul_measure]
  have hlocal (n : ℕ) :
      ∫ η, poissonLaplace f η ∂((Measure.pi fun _ : Fin n => ν).map (finitePointMeasure n)) =
        (∫ x, Real.exp (-f x) ∂ν)^n := by
    rw [integral_map (finitePointMeasure_measurable n).aemeasurable
      (poissonLaplace_measurable hf).aestronglyMeasurable]
    simp_rw [poissonLaplace_finitePointMeasure hf hf0]
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin n) (x : S) => Real.exp (-f x))]
    simp
  simp_rw [hlocal,smul_eq_mul]
  have hp := poisson_power_integral r (∫ x, Real.exp (-f x) ∂ν)
  rw [integral_poissonMeasure] at hp
  simpa only [measureReal_def,← poissonMeasure_real_singleton,smul_eq_mul] using hp

@[simp] lemma expNegENNReal_zero : expNegENNReal 0 = 1 := by simp [expNegENNReal]

lemma expNegENNReal_add (u v : ℝ≥0∞) :
    expNegENNReal (u+v) = expNegENNReal u * expNegENNReal v := by
  by_cases hu : u = ⊤
  · simp [hu]
  by_cases hv : v = ⊤
  · simp [hv]
  rw [expNegENNReal_finite (ENNReal.add_ne_top.mpr ⟨hu,hv⟩),
    expNegENNReal_finite hu,expNegENNReal_finite hv,ENNReal.toReal_add hu hv,
    neg_add,Real.exp_add]

lemma expNegENNReal_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) :
    expNegENNReal (∑ i ∈ s, a i) = ∏ i ∈ s, expNegENNReal (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,expNegENNReal_add,ih]

lemma measureSum_measurable {S : Type*} [MeasurableSpace S] :
    Measurable (fun η : ℕ → Measure S => Measure.sum η) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.sum_apply _ hs]
  exact Measurable.tsum fun i => (Measure.measurable_coe hs).comp (measurable_pi_apply i)

lemma poissonLaplace_finsetSum {S : Type*} [MeasurableSpace S]
    (f : S → ℝ) (s : Finset ℕ) (η : ℕ → Measure S) :
    poissonLaplace f (∑ i ∈ s, η i) = ∏ i ∈ s, poissonLaplace f (η i) := by
  simp only [poissonLaplace,lintegral_finsetSum_measure,expNegENNReal_sum]

lemma poissonLaplace_sum_tendsto {S : Type*} [MeasurableSpace S]
    (f : S → ℝ) (η : ℕ → Measure S) :
    Tendsto (fun n => poissonLaplace f (∑ i ∈ Finset.range n, η i)) atTop
      (𝓝 (poissonLaplace f (Measure.sum η))) := by
  simp only [poissonLaplace,lintegral_sum_measure,lintegral_finsetSum_measure]
  exact expNegENNReal_continuous.continuousAt.tendsto.comp
    (ENNReal.summable.hasSum.tendsto_sum_nat)

def countablePoissonLaw {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) : Measure (Measure S) :=
  (Measure.infinitePi fun i => finitePoissonLaw (r i) (ν i)).map Measure.sum

instance countablePoissonLaw_probability {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) [∀ i, IsProbabilityMeasure (ν i)] :
    IsProbabilityMeasure (countablePoissonLaw r ν) := by
  unfold countablePoissonLaw
  infer_instance

lemma finitePoissonLaw_laplace_nonneg {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ η, poissonLaplace f η ∂finitePoissonLaw r ν =
      expNegENNReal (ENNReal.ofReal ((r : ℝ) * ∫ x, 1 - Real.exp (-f x) ∂ν)) := by
  have hib : Integrable (fun x => Real.exp (-f x)) ν := by
    apply Integrable.of_bound (hf.neg.exp.aestronglyMeasurable) 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x))
  have hn : 0 ≤ (r : ℝ) * ∫ x, 1 - Real.exp (-f x) ∂ν := by
    apply mul_nonneg r.coe_nonneg
    apply integral_nonneg
    intro x
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x)))
  rw [finitePoissonLaw_laplace r ν hf hf0,expNegENNReal_finite ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hn,integral_sub (integrable_const 1) hib]
  simp only [integral_const,probReal_univ,one_smul]
  congr 1
  ring

lemma countablePoissonLaw_laplace {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) [∀ i, IsProbabilityMeasure (ν i)]
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ η, poissonLaplace f η ∂countablePoissonLaw r ν =
      expNegENNReal (∑' i, ENNReal.ofReal ((r i : ℝ) * ∫ x, 1 - Real.exp (-f x) ∂ν i)) := by
  let Q := Measure.infinitePi fun i => finitePoissonLaw (r i) (ν i)
  let a (i : ℕ) := ENNReal.ofReal ((r i : ℝ) * ∫ x, 1 - Real.exp (-f x) ∂ν i)
  have hm (n : ℕ) : Measurable (fun η : ℕ → Measure S =>
      poissonLaplace f (∑ i ∈ Finset.range n, η i)) := by
    apply (poissonLaplace_measurable hf).comp
    fun_prop
  have he (n : ℕ) :
      ∫ η, poissonLaplace f (∑ i ∈ Finset.range n, η i) ∂Q =
        expNegENNReal (∑ i ∈ Finset.range n, a i) := by
    simp_rw [poissonLaplace_finsetSum]
    have he' : (fun η : ℕ → Measure S => ∏ i ∈ Finset.range n, poissonLaplace f (η i)) =
        (fun η : ℕ → Measure S => ∏ i : (Finset.range n),
          poissonLaplace f ((Finset.range n).restrict η i)) := by
      funext η
      exact (Finset.prod_coe_sort (Finset.range n) (fun i => poissonLaplace f (η i))).symm
    rw [he']
    rw [integral_restrict_infinitePi (μ := fun i => finitePoissonLaw (r i) (ν i))
      (f := fun η : (i : Finset.range n) → Measure S => ∏ i, poissonLaplace f (η i))
      (by exact (Finset.measurable_prod _ (fun i _ => (poissonLaplace_measurable hf).comp
        (measurable_pi_apply i))).aestronglyMeasurable)]
    rw [integral_fintype_prod_eq_prod (fun (i : Finset.range n) (η : Measure S) =>
      poissonLaplace f η)]
    simp_rw [finitePoissonLaw_laplace_nonneg _ _ hf hf0]
    rw [expNegENNReal_sum]
    exact Finset.prod_coe_sort (Finset.range n) (fun i => expNegENNReal (a i))
  have ht : Tendsto (fun n => ∫ η, poissonLaplace f (∑ i ∈ Finset.range n, η i) ∂Q)
      atTop (𝓝 (∫ η, poissonLaplace f (Measure.sum η) ∂Q)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun n => (hm n).aestronglyMeasurable) (integrable_const 1)
    · intro n
      exact ae_of_all _ fun η => by
        rw [Real.norm_eq_abs,abs_of_nonneg (poissonLaplace_bounds _ _).1]
        exact (poissonLaplace_bounds _ _).2
    · exact ae_of_all _ (poissonLaplace_sum_tendsto f)
  simp_rw [he] at ht
  have ht' : Tendsto (fun n => expNegENNReal (∑ i ∈ Finset.range n, a i)) atTop
      (𝓝 (expNegENNReal (∑' i, a i))) :=
    expNegENNReal_continuous.continuousAt.tendsto.comp ENNReal.summable.hasSum.tendsto_sum_nat
  rw [countablePoissonLaw, integral_map measureSum_measurable.aemeasurable
    (poissonLaplace_measurable hf).aestronglyMeasurable]
  exact tendsto_nhds_unique ht ht'

lemma measure_eq_of_additive_test_family {X M : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddMonoid M] (g : M → X →ᵇ ℝ)
    (g0 : g 0 = 1) (gadd : ∀ a b, g (a+b) = g a * g b)
    (gsep : ∀ x y : X, x ≠ y → ∃ a, g a x ≠ g a y)
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (heq : ∀ a, ∫ x, g a x ∂P = ∫ x, g a x ∂Q) : P = Q := by
  let K : Submonoid (X →ᵇ ℝ) :=
    { carrier := Set.range g
      one_mem' := ⟨0,g0⟩
      mul_mem' := by
        rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩
        exact ⟨a+b,gadd a b⟩ }
  let A : StarSubalgebra ℝ (X →ᵇ ℝ) :=
    { toSubalgebra := Algebra.adjoin ℝ (K : Set (X →ᵇ ℝ))
      star_mem' := fun {f} hf => by
        have hstar : star f = f := by ext x; simp
        rwa [hstar] }
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨a,ha⟩ := gsep x y hxy
    use g a
    simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
      SetLike.mem_coe, exists_exists_and_eq_and, ne_eq]
    refine ⟨⟨g a,?_,rfl⟩,ha⟩
    exact Algebra.subset_adjoin (show g a ∈ K from ⟨a,rfl⟩)
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep
  intro f hf
  let V : Submodule ℝ (X →ᵇ ℝ) :=
    { carrier := {f | ∫ x, f x ∂P = ∫ x, f x ∂Q}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change ∫ x, a x + b x ∂P = ∫ x, a x + b x ∂Q
        rw [integral_add (a.integrable P) (b.integrable P),
          integral_add (a.integrable Q) (b.integrable Q),ha,hb]
      smul_mem' := by
        intro c f hf
        change ∫ x, c * f x ∂P = ∫ x, c * f x ∂Q
        rw [integral_const_mul,integral_const_mul,hf] }
  have hspan : Submodule.span ℝ (K : Set (X →ᵇ ℝ)) ≤ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact heq a
  apply hspan
  change f ∈ (Algebra.adjoin ℝ (K : Set (X →ᵇ ℝ))).toSubmodule at hf
  rw [Algebra.adjoin_eq_span,Submonoid.closure_eq] at hf
  exact hf

lemma expNegENNReal_injective : Function.Injective expNegENNReal := by
  intro u v huv
  have hfinite (w : ℝ≥0∞) : EReal.exp (-(w : EReal)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (EReal.exp_le_one_iff.mpr
      (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg w))) ENNReal.one_lt_top)
  have he := (ENNReal.toReal_eq_toReal_iff' (hfinite u) (hfinite v)).mp huv
  have hn := EReal.expOrderIso.injective he
  exact EReal.coe_ennreal_injective (by simpa using congrArg Neg.neg hn)

def laplaceTest {ι : Type*} [Fintype ι] (a : ι → ℝ≥0) : (ι → ℝ≥0∞) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => expNegENNReal (∑ i, (a i : ℝ≥0∞) * x i), by
      apply expNegENNReal_continuous.comp
      exact continuous_finsetSum _ fun i _ =>
        (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp (continuous_apply i)⟩

@[simp] lemma laplaceTest_zero {ι : Type*} [Fintype ι] :
    laplaceTest (0 : ι → ℝ≥0) = 1 := by
  ext x
  simp [laplaceTest]

lemma laplaceTest_add {ι : Type*} [Fintype ι] (a b : ι → ℝ≥0) :
    laplaceTest (a+b) = laplaceTest a * laplaceTest b := by
  ext x
  simp only [laplaceTest,BoundedContinuousFunction.mkOfCompact_apply,
    ContinuousMap.coe_mk,Pi.add_apply,ENNReal.coe_add,add_mul,
    Finset.sum_add_distrib,expNegENNReal_add,BoundedContinuousFunction.mul_apply]

lemma laplaceTest_separates {ι : Type*} [Fintype ι] (x y : ι → ℝ≥0∞) (hxy : x ≠ y) :
    ∃ a : ι → ℝ≥0, laplaceTest a x ≠ laplaceTest a y := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! h
    exact hxy (funext h)
  refine ⟨Pi.single i 1,?_⟩
  simpa [laplaceTest,Pi.single_apply,apply_ite,ite_mul] using expNegENNReal_injective.ne hi

lemma measure_eq_of_laplace_tests {ι : Type*} [Fintype ι]
    (P Q : Measure (ι → ℝ≥0∞)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (heq : ∀ a : ι → ℝ≥0, ∫ x, laplaceTest a x ∂P = ∫ x, laplaceTest a x ∂Q) : P = Q :=
  measure_eq_of_additive_test_family laplaceTest laplaceTest_zero laplaceTest_add
    laplaceTest_separates P Q heq

lemma measure_eq_of_map_eq_comap {X Y : Type*} [mX : MeasurableSpace X]
    [mY : MeasurableSpace Y] (f : X → Y) (h : mX = mY.comap f)
    (P Q : Measure X) (heq : P.map f = Q.map f) : P = Q := by
  have hf : Measurable f := Measurable.of_comap_le h.ge
  ext s hs
  rw [h] at hs
  obtain ⟨t,ht,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  rw [← Measure.map_apply hf ht,← Measure.map_apply hf ht,heq]

lemma measureLaw_eval_comap {S : Type*} [MeasurableSpace S] :
    (inferInstance : MeasurableSpace (Measure S)) = MeasurableSpace.comap
      (fun η : Measure S => fun s : {s : Set S // MeasurableSet s} => η s.val)
      inferInstance := by
  apply le_antisymm
  · change (⨆ (s : Set S) (hs : MeasurableSet s),
      MeasurableSpace.comap (fun η : Measure S => η s) (borel ℝ≥0∞)) ≤ _
    apply iSup₂_le
    intro s hs
    exact MeasurableSpace.comap_le_comap_pi (g := fun t : {s : Set S // MeasurableSet s} =>
      fun η : Measure S => η t.val) ⟨s,hs⟩
  · apply Measurable.comap_le
    apply Measurable.of_eval
    intro s
    exact Measure.measurable_coe s.property

lemma laplaceTest_eval_eq {S ι : Type*} [MeasurableSpace S] [Fintype ι]
    (s : ι → Set S) (hs : ∀ i, MeasurableSet (s i)) (a : ι → ℝ≥0) (η : Measure S) :
    laplaceTest a (fun i => η (s i)) =
      poissonLaplace (fun x => ∑ i, (s i).indicator (fun _ => (a i : ℝ)) x) η := by
  classical
  have h0 (i : ι) (x : S) : 0 ≤ (s i).indicator (fun _ => (a i : ℝ)) x :=
    Set.indicator_nonneg (fun _ _ => (a i).coe_nonneg) x
  have he (x : S) : ENNReal.ofReal (∑ i, (s i).indicator (fun _ => (a i : ℝ)) x) =
      ∑ i, (s i).indicator (fun _ => (a i : ℝ≥0∞)) x := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 i x)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ s i <;> simp [hx]
  change expNegENNReal (∑ i, (a i : ℝ≥0∞) * η (s i)) = _
  simp only [poissonLaplace,he]
  rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hs i))]
  simp_rw [lintegral_indicator (hs _),setLIntegral_const]

lemma measureLaw_eq_of_laplace {S : Type*} [MeasurableSpace S]
    (P Q : Measure (Measure S)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (heq : ∀ f : S → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
      ∫ η, poissonLaplace f η ∂P = ∫ η, poissonLaplace f η ∂Q) : P = Q := by
  classical
  let J := {s : Set S // MeasurableSet s}
  let E (η : Measure S) (s : J) : ℝ≥0∞ := η s.val
  have hE : Measurable E := Measurable.of_eval fun event => Measure.measurable_coe event.property
  apply measure_eq_of_map_eq_comap E measureLaw_eval_comap
  apply IsProjectiveLimit.unique (P := fun I : Finset J => (Q.map E).map I.restrict)
    (hν := fun _ => rfl)
  intro I
  have hI : Measurable (I.restrict (π := fun _ => ℝ≥0∞)) :=
    Measurable.of_eval fun index => measurable_pi_apply index.val
  change (P.map E).map I.restrict = (Q.map E).map I.restrict
  rw [Measure.map_map hI hE,Measure.map_map hI hE]
  apply measure_eq_of_laplace_tests
  intro a
  have hm : Measurable (I.restrict ∘ E) := hI.comp hE
  rw [integral_map hm.aemeasurable (laplaceTest a).continuous.measurable.aestronglyMeasurable,
    integral_map hm.aemeasurable (laplaceTest a).continuous.measurable.aestronglyMeasurable]
  have hid (η : Measure S) : laplaceTest a ((I.restrict ∘ E) η) =
      poissonLaplace (fun x => ∑ i : I, i.val.val.indicator (fun _ => (a i : ℝ)) x) η :=
    laplaceTest_eval_eq (fun i : I => i.val.val) (fun i => i.val.property) a η
  simp_rw [hid]
  apply heq
  · exact Finset.measurable_sum _ fun i _ => measurable_const.indicator i.val.property
  · intro x
    exact Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => (a i).coe_nonneg) x

def countablePoissonIntensity {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) : Measure S :=
  Measure.sum fun i => (r i : ℝ≥0∞) • ν i

lemma countablePoissonLaw_laplace_intensity {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) [∀ i, IsProbabilityMeasure (ν i)]
    {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ η, poissonLaplace f η ∂countablePoissonLaw r ν =
      expNegENNReal (∫⁻ x, ENNReal.ofReal (1 - Real.exp (-f x)) ∂countablePoissonIntensity r ν) := by
  rw [countablePoissonLaw_laplace r ν hf hf0]
  congr 1
  rw [countablePoissonIntensity,lintegral_sum_measure]
  apply tsum_congr
  intro i
  rw [lintegral_smul_measure,ENNReal.ofReal_mul (r i).coe_nonneg,ENNReal.ofReal_coe_nnreal]
  congr 1
  apply ofReal_integral_eq_lintegral_ofReal
  · apply Integrable.of_bound (measurable_const.sub hf.neg.exp).aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      have h0 := Real.exp_pos (-f x)
      have h1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x))
      change |1 - Real.exp (-f x)| ≤ 1
      rw [abs_of_nonneg (sub_nonneg.mpr h1)]
      linarith
  · exact ae_of_all _ fun x => sub_nonneg.mpr
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 x)))

def finiteIntensityMarks {S : Type*} [MeasurableSpace S] [Nonempty S] (κ : Measure S) : Measure S :=
  if κ univ = 0 then Measure.dirac (Classical.choice ‹Nonempty S›) else (κ univ)⁻¹ • κ

instance finiteIntensityMarks_probability {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [IsFiniteMeasure κ] : IsProbabilityMeasure (finiteIntensityMarks κ) := by
  by_cases hκ : κ univ = 0
  · simp only [finiteIntensityMarks,ite_eq_left hκ]
    infer_instance
  · constructor
    simp [finiteIntensityMarks,hκ,ENNReal.inv_mul_cancel hκ (measure_ne_top _ _)]

lemma finiteIntensityMarks_smul {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [IsFiniteMeasure κ] :
    ((κ univ).toNNReal : ℝ≥0∞) • finiteIntensityMarks κ = κ := by
  rw [ENNReal.coe_toNNReal (measure_ne_top _ _)]
  by_cases hκ : κ univ = 0
  · have he : κ = 0 := Measure.measure_univ_eq_zero.mp hκ
    simp [he]
  · rw [finiteIntensityMarks,ite_eq_right hκ,smul_smul,ENNReal.mul_inv_cancel hκ (measure_ne_top _ _),one_smul]

def poissonRandomMeasureLaw {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] : Measure (Measure S) :=
  countablePoissonLaw (fun i => ((sfiniteSeq κ i) univ).toNNReal)
    (fun i => finiteIntensityMarks (sfiniteSeq κ i))

instance poissonRandomMeasureLaw_probability {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] : IsProbabilityMeasure (poissonRandomMeasureLaw κ) := by
  unfold poissonRandomMeasureLaw
  infer_instance

lemma poissonRandomMeasureLaw_laplace {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ η, poissonLaplace f η ∂poissonRandomMeasureLaw κ =
      expNegENNReal (∫⁻ x, ENNReal.ofReal (1 - Real.exp (-f x)) ∂κ) := by
  rw [poissonRandomMeasureLaw,countablePoissonLaw_laplace_intensity _ _ hf hf0]
  congr 2
  simp only [countablePoissonIntensity,finiteIntensityMarks_smul,sum_sfiniteSeq]

end SphericalPerceptronFreeEnergy
end

end OAI
