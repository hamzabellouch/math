import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkGoodParameters
import OAI.Probability.Perceptron.Variational.CompactScalarGG

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkOverlap_continuous (N : ℕ) : Continuous (Function.uncurry (bulkOverlap (N:=N))) := by
  apply Continuous.subtype_mk
  exact continuous_fst.subtype_val.inner continuous_snd.subtype_val

lemma bulkBlockTest_measurable (N r : ℕ) (F : CompactBlock CompactOverlap r →ᵇ ℝ) :
    Measurable (fun x : Fin r→NormalizedSpin N => F (fun i j => bulkOverlap (x i) (x j))) := by
  apply F.continuous.measurable.comp
  refine Measurable.of_eval fun first => Measurable.of_eval fun second => ?_
  have hm : Measurable (fun x : Fin r → NormalizedSpin N => (x first, x second)) :=
    (measurable_pi_apply first).prodMk (measurable_pi_apply second)
  exact (bulkOverlap_measurable N).comp hm

lemma bulk_compact_gg_defect (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p r : ℕ) (j : Fin r)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) :
    compactGGDefect (bulkGibbsArrayLaw n M f v) r j F (compactScalarMonomial p) =
      -bulkGGDefect n M f v p r j (fun x => F (fun i l => bulkOverlap (x i) (x l))) := by
  have hh := compactGGDefect_gibbsOverlapArray (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x)
    (bulkHamiltonian_continuous _ _ _ _).measurable bulkOverlap (bulkOverlap_measurable (n+1))
    (ae_of_all _ (bulkHamiltonian_exp_integrable n M f v)) r j F (compactScalarMonomial p) 1
    (fun x => by simp only [compactScalarMonomial_apply,bulkOverlap,spinOverlap_self,one_pow])
    (fun x y => by simp only [compactScalarMonomial_apply,bulkOverlap,spinOverlap,real_inner_comm])
  simpa only [bulkGibbsArrayLaw,kernelGGDefect,bulkGGDefect,bulkMoment,bulkSpinKernel,
    Kernel.const_apply,compactScalarMonomial_apply,bulkOverlap,one_mul] using hh

lemma bulk_compact_gg_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (r : ℕ) (j : Fin r)
    (F : CompactBlock CompactOverlap r →ᵇ ℝ) (hv : 1≤v (p.val+1)) :
    |compactGGDefect (bulkGibbsArrayLaw n M f v) r j F (compactScalarMonomial (p.val+1))| ≤
      ‖F‖/(2:ℝ)^(-((p.val+1:ℕ):ℤ))*bulkNormalizedDeviation n M f p v := by
  rw [bulk_compact_gg_defect,abs_neg]
  exact bulkGG_bound n M f v p r j (bulkBlockTest_measurable (n+1) r F) (norm_nonneg _)
    (fun x => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (fun i l => bulkOverlap (x i) (x l))) hv

lemma omitted_bulk_monomial_tendsto (α : ℝ) (f : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ)
    (hv : ∀ᶠ n in atTop, ∀ p, 1≤v n p)
    (hd : ∀ p, Tendsto (fun n => omittedBulkDeviation α f n p (v n)) atTop (𝓝 0))
    (p r : ℕ) (j : Fin r) (F : CompactBlock CompactOverlap r →ᵇ ℝ) :
    Tendsto (fun n => compactGGDefect (bulkGibbsArrayLaw n (patternCount α (n+1)-2) f (v n))
      r j F (compactScalarMonomial (p+1))) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun n => ‖F‖/(2:ℝ)^(-((p+1:ℕ):ℤ))*omittedBulkDeviation α f n p (v n))
  · filter_upwards [hv,eventually_ge_atTop p] with n hn hp
    have hpn : p<n+1 := Nat.lt_succ_of_le hp
    simpa only [Real.norm_eq_abs,omittedBulkDeviation,bulkDeviationAt,dite_eq_left hpn] using
      bulk_compact_gg_bound n (patternCount α (n+1)-2) f (v n) ⟨p,hpn⟩ r j F (hn (p+1))
  · simpa using (hd p).const_mul (‖F‖/(2:ℝ)^(-((p+1:ℕ):ℤ)))

lemma compactScalarGG_zero (μ : ProbabilityMeasure (CompactArray CompactOverlap))
    (r : ℕ) (j : Fin r) (F : CompactBlock CompactOverlap r →ᵇ ℝ) :
    compactGGDefect μ r j F (compactScalarMonomial 0)=0 := by
  have hr : 1≤r := by have := j.isLt; omega
  simp only [compactGGDefect,compactScalarMonomial_apply,pow_zero,mul_one,
    integral_const,probReal_univ,smul_eq_mul,Finset.sum_const,Finset.card_erase_of_mem
    (Finset.mem_univ j),Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_sub hr,Nat.cast_one]
  ring

lemma omitted_bulk_limit_gg (α : ℝ) (f : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ)
    (hv : ∀ᶠ n in atTop, ∀ p, 1≤v n p)
    (hd : ∀ p, Tendsto (fun n => omittedBulkDeviation α f n p (v n)) atTop (𝓝 0))
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (patternCount α (s n+1)-2) f (v (s n))) atTop (𝓝 ν))
    (r : ℕ) (j : Fin r) (F : CompactBlock CompactOverlap r →ᵇ ℝ) (g : CompactOverlap →ᵇ ℝ) :
    compactGGDefect ν r j F g=0 := by
  apply compactGG_of_scalar_monomials
  intro p
  cases p with
  | zero => exact compactScalarGG_zero ν r j F
  | succ p =>
    apply compactGGDefect_limit hlim
    exact (omitted_bulk_monomial_tendsto α f v hv hd p r j F).comp hs.tendsto_atTop


lemma bulk_monomial_tendsto (M : ℕ→ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ)
    (hv : ∀ᶠ n in atTop, ∀ p, 1≤v n p)
    (hd : ∀ p, Tendsto (fun n => bulkDeviationAt n (M n) f p (v n)) atTop (𝓝 0))
    (p r : ℕ) (j : Fin r) (F : CompactBlock CompactOverlap r →ᵇ ℝ) :
    Tendsto (fun n => compactGGDefect (bulkGibbsArrayLaw n (M n) f (v n))
      r j F (compactScalarMonomial (p+1))) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun n => ‖F‖/(2:ℝ)^(-((p+1:ℕ):ℤ))*bulkDeviationAt n (M n) f p (v n))
  · filter_upwards [hv,eventually_ge_atTop p] with n hn hp
    have hpn : p<n+1 := Nat.lt_succ_of_le hp
    simpa only [Real.norm_eq_abs,bulkDeviationAt,dite_eq_left hpn] using
      bulk_compact_gg_bound n (M n) f (v n) ⟨p,hpn⟩ r j F (hn (p+1))
  · simpa using (hd p).const_mul (‖F‖/(2:ℝ)^(-((p+1:ℕ):ℤ)))

lemma bulk_limit_gg (M : ℕ→ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ)
    (hv : ∀ᶠ n in atTop, ∀ p, 1≤v n p)
    (hd : ∀ p, Tendsto (fun n => bulkDeviationAt n (M n) f p (v n)) atTop (𝓝 0))
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) f (v (s n))) atTop (𝓝 ν))
    (r : ℕ) (j : Fin r) (F : CompactBlock CompactOverlap r →ᵇ ℝ) (g : CompactOverlap →ᵇ ℝ) :
    compactGGDefect ν r j F g=0 := by
  apply compactGG_of_scalar_monomials
  intro p
  cases p with
  | zero => exact compactScalarGG_zero ν r j F
  | succ p =>
    apply compactGGDefect_limit hlim
    exact (bulk_monomial_tendsto M f v hv hd p r j F).comp hs.tendsto_atTop

def bulkJointDeviation (α : ℝ) (f : ℝ→ᵇℝ) (n p : ℕ) (v : ℕ→ℝ) : ℝ :=
  bulkDeviationAt n (patternCount α (n+1)) f p v + omittedBulkDeviation α f n p v

lemma bulkJointDeviation_nonneg (α : ℝ) (f : ℝ→ᵇℝ) (n p : ℕ) (v : ℕ→ℝ) :
    0≤bulkJointDeviation α f n p v :=
  add_nonneg (bulkDeviationAt_nonneg _ _ _ _ _) (bulkDeviationAt_nonneg _ _ _ _ _)
lemma bulkJointDeviation_measurable (α : ℝ) (f : ℝ→ᵇℝ) (n p : ℕ) :
    Measurable (bulkJointDeviation α f n p) :=
  (bulkDeviationAt_measurable _ _ _ _).add (bulkDeviationAt_measurable _ _ _ _)
lemma bulkJointDeviation_integrable (α : ℝ) (f : ℝ→ᵇℝ) (n p : ℕ) :
    Integrable (bulkJointDeviation α f n p) bulkParameterLaw :=
  (bulkDeviationAt_integrable _ _ _ _).add (bulkDeviationAt_integrable _ _ _ _)

lemma bulkJointDeviation_integral_tendsto {α : ℝ} (hα : 0≤α) (f : ℝ→ᵇℝ) (p : ℕ) :
    Tendsto (fun n => ∫ v, bulkJointDeviation α f n p v ∂bulkParameterLaw) atTop (𝓝 0) := by
  have h₁ := bulkDeviationAt_integral_tendsto (fun n => patternCount α (n+1)) f hα
    (fun n => Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg _))) p
  have h₂ := omittedBulkDeviation_integral_tendsto hα f p
  have he (n : ℕ) : (∫ v, bulkJointDeviation α f n p v ∂bulkParameterLaw) =
      (∫ v, bulkDeviationAt n (patternCount α (n+1)) f p v ∂bulkParameterLaw) +
        ∫ v, omittedBulkDeviation α f n p v ∂bulkParameterLaw :=
    integral_add (bulkDeviationAt_integrable _ _ _ _) (bulkDeviationAt_integrable _ _ _ _)
  simp_rw [he]
  simpa only [add_zero] using h₁.add h₂

def bulkJointGoodSet (α : ℝ) (f : ℝ→ᵇℝ) (J : ℕ→ℕ) (n : ℕ) : Set (ℕ→ℝ) :=
  diagonalGoodSet bulkParameterLaw (bulkJointDeviation α f) J n ∩ {v | ∀ p, v p∈Icc (1:ℝ) 2}

lemma bulkJointGoodSet_measurable (α : ℝ) (f : ℝ→ᵇℝ) (J : ℕ→ℕ) (n : ℕ) :
    MeasurableSet (bulkJointGoodSet α f J n) := by
  refine (diagonalGoodSet_measurable _ _ (bulkJointDeviation_measurable α f) J n).inter ?_
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun p => (measurable_pi_apply p) measurableSet_Icc

lemma bulkJointGoodSet_compl_measure (α : ℝ) (f : ℝ→ᵇℝ) (J : ℕ→ℕ) (n : ℕ) :
    bulkParameterLaw.real (bulkJointGoodSet α f J n)ᶜ =
      bulkParameterLaw.real (diagonalGoodSet bulkParameterLaw (bulkJointDeviation α f) J n)ᶜ := by
  simp only [measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [bulkParameterLaw_ae] with v hv
  apply propext
  change ¬(v∈diagonalGoodSet bulkParameterLaw (bulkJointDeviation α f) J n ∧ ∀ p, v p∈Icc (1:ℝ) 2) ↔ _
  exact not_congr ⟨fun h => h.1, fun h => ⟨h,hv⟩⟩

theorem exists_bulkJointGoodParameters {α : ℝ} (hα : 0≤α) (f : ℝ→ᵇℝ) :
    ∃ J : ℕ→ℕ, Monotone J ∧ (∀ n, J n≤n) ∧ Tendsto J atTop atTop ∧
      (∀ n, MeasurableSet (bulkJointGoodSet α f J n)) ∧
      Tendsto (fun n => bulkParameterLaw.real (bulkJointGoodSet α f J n)ᶜ) atTop (𝓝 0) ∧
      (∀ v : ℕ→(ℕ→ℝ), (∀ᶠ n in atTop, v n∈bulkJointGoodSet α f J n) →
        ∀ p, Tendsto (fun n => bulkDeviationAt n (patternCount α (n+1)) f p (v n)) atTop (𝓝 0) ∧
          Tendsto (fun n => omittedBulkDeviation α f n p (v n)) atTop (𝓝 0)) := by
  have hn := bulkJointDeviation_nonneg α f
  have hi := bulkJointDeviation_integrable α f
  obtain ⟨J,hmon,hbound,hlim,hmass⟩ := exists_slow_diagonal
    (fun n p => integral_nonneg (hn n p)) (bulkJointDeviation_integral_tendsto hα f)
  refine ⟨J,hmon,hbound,hlim,bulkJointGoodSet_measurable α f J,?_,?_⟩
  · simpa only [bulkJointGoodSet_compl_measure] using
      diagonalGoodSet_compl_tendsto bulkParameterLaw (bulkJointDeviation α f) hn hi J hmass
  · intro v hv p
    have hd := diagonalGoodSet_deviation_tendsto bulkParameterLaw (bulkJointDeviation α f) hn J hlim hmass v
      (hv.mono fun n h => h.1) p
    constructor
    · exact squeeze_zero (fun n => bulkDeviationAt_nonneg _ _ _ _ _)
        (fun n => le_add_of_nonneg_right (bulkDeviationAt_nonneg _ _ _ _ _)) hd
    · exact squeeze_zero (fun n => bulkDeviationAt_nonneg _ _ _ _ _)
        (fun n => le_add_of_nonneg_left (bulkDeviationAt_nonneg _ _ _ _ _)) hd

end SphericalPerceptronFreeEnergy
end

end OAI
