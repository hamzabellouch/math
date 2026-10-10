import Mathlib
import OAI.Probability.SphericalField.Poisson.Intensity

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
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

end SphericalPerceptron
end
end

end OAI
