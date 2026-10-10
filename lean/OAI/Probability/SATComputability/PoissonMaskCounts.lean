import OAI.Probability.SATComputability.FinitePushforward
import OAI.Probability.SATComputability.ClauseRestoration
import OAI.Probability.DilutedSpin.RootProductLaw

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

noncomputable def zeroMask {X : Type*} [Fintype X] (z : X → ℝ) : Finset X :=
  Finset.univ.filter (fun x => z x = 0)

theorem zeroMask_measurable {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] : Measurable (zeroMask (X := X)) := by
  apply measurable_finset_iff.mpr
  intro x
  simp only [zeroMask, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (measurable_pi_apply x).eq_const 0

noncomputable def maskDefect {A X : Type*} [Fintype X]
    (mask : A → Finset X) (a : A) : X → ℝ :=
  fun x => if x ∈ mask a then 0 else 1

noncomputable def countsMask {A X : Type*} [Fintype A] [Fintype X]
    (mask : A → Finset X) (counts : A → ℕ) : Finset X :=
  Finset.univ.filter (fun x => ∀ a, counts a = 0 ∨ x ∈ mask a)

theorem zeroMask_sum_defect {A X : Type*} [Fintype A] [Fintype X]
    (mask : A → Finset X) (counts : A → ℕ) :
    zeroMask (∑ a, counts a • maskDefect mask a) = countsMask mask counts := by
  ext x
  simp only [zeroMask, countsMask, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.sum_apply, nsmul_eq_mul]
  change (∑ a, (counts a : ℝ)*(if x ∈ mask a then 0 else 1)) = 0 ↔
    ∀ a, counts a = 0 ∨ x ∈ mask a
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by split_ifs <;> positivity)]
  simp only [Finset.mem_univ, true_implies]
  apply forall_congr'
  intro a
  by_cases hx : x ∈ mask a <;> simp [hx]

theorem zeroMask_sum_marks {A X : Type*} [Fintype X] (mask : A → Finset X)
    {d : ℕ} (as : Fin d → A) :
    zeroMask (∑ j, maskDefect mask (as j)) =
      Finset.univ.filter (fun x => ∀ j, x ∈ mask (as j)) := by
  ext x
  simp only [zeroMask, Finset.mem_filter, Finset.mem_univ, true_and, Finset.sum_apply,
    maskDefect]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)]
  simp

theorem compoundPoisson_uniform_integral {A E : Type} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    (r : ℝ≥0) (V : A → E) (f : E → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ z, |f z| ≤ B) :
    (∫ z, f z ∂compoundPoisson r (Measure.map V (finiteUniform A))) =
      ∫ d : ℕ, (FiniteLaw.uniform : FiniteLaw (Fin d → A)).expect
        (fun as => f (∑ j, V (as j))) ∂poissonMeasure r := by
  have hV : Measurable V := measurable_of_countable V
  let ν := Measure.map V (finiteUniform A)
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr inferInstance
  have hi : Integrable f (compoundPoisson r ν) :=
    Integrable.of_bound hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hb z))
  rw [compoundPoisson, integral_sum_measure hi, integral_poissonMeasure]
  apply tsum_congr
  intro d
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    integral_map (by fun_prop) hf.aestronglyMeasurable]
  change _ • (∫ z : Fin d → E, f (∑ j, z j)
    ∂Measure.pi (fun _ => Measure.map V (finiteUniform A))) = _
  rw [← Measure.pi_map_pi (μ := fun _ : Fin d => finiteUniform A)
    (f := fun _ a => V a) (fun _ => hV.aemeasurable),
    integral_map (φ := fun x : Fin d → A => fun i => V (x i))
      (f := fun z : Fin d → E => f (∑ j, z j))
      (Measurable.of_eval (fun i => hV.comp (measurable_pi_apply i))).aemeasurable
      (hf.comp (by fun_prop)).aestronglyMeasurable,
    finiteUniform_pi, integral_finiteUniform]
  simp only [FiniteLaw.expect, FiniteLaw.uniform, smul_eq_mul, ← Finset.mul_sum]

noncomputable def markedMaskLaw {A X : Type*} [Fintype A] [Nonempty A] [Fintype X]
    (r : ℝ≥0) (mask : A → Finset X) : FiniteLaw (Finset X) :=
  poissonMixture r (fun d => finiteMap (FiniteLaw.uniform : FiniteLaw (Fin d → A))
    (fun as => Finset.univ.filter (fun x => ∀ j, x ∈ mask (as j))))

theorem markedMaskLaw_counts {A X : Type} [Fintype A] [Nonempty A] [Fintype X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (r : ℝ≥0) (mask : A → Finset X) (f : Finset X → ℝ) :
    (markedMaskLaw r mask).expect f =
      ∫ counts : A → ℕ, f (countsMask mask counts)
        ∂Measure.pi (fun _ : A => poissonMeasure (r / Fintype.card A)) := by
  have hg : Measurable (fun z : X → ℝ => f (zeroMask z)) :=
    (measurable_of_countable f).comp zeroMask_measurable
  have hb (z : X → ℝ) : |f (zeroMask z)| ≤ ∑ U : Finset X, |f U| :=
    Finset.single_le_sum (fun U _ => abs_nonneg (f U)) (Finset.mem_univ _)
  have he := compoundPoisson_uniform_integral r (maskDefect mask)
    (fun z => f (zeroMask z)) hg _ hb
  simp only [zeroMask_sum_marks] at he
  rw [uniform_poisson_weighted_counts, integral_map
    (measurable_of_countable (fun counts : A → ℕ => ∑ a, counts a • maskDefect mask a)).aemeasurable
    hg.aestronglyMeasurable] at he
  simp only [zeroMask_sum_defect] at he
  rw [markedMaskLaw, poissonMixture_expect]
  simp only [finiteMap_expect]
  exact he.symm

theorem candidateBlock_counts {n : ℕ} [NeZero n] (r : ℝ≥0) (k : ℕ)
    (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock r k (Finset.univ : Finset (DeletionCandidate n))).expect f =
      ∫ counts : (Fin k → SignedLiteral n) → ℕ,
        f (countsMask clauseMask counts)
        ∂Measure.pi (fun _ : Fin k → SignedLiteral n =>
          poissonMeasure (r / Fintype.card (Fin k → SignedLiteral n))) := by
  classical
  let : MeasurableSpace (DeletionCandidate n) := ⊤
  let : MeasurableSingletonClass (DeletionCandidate n) := ⟨fun _ => trivial⟩
  rw [← markedMaskLaw_counts r (clauseMask (n := n) (k := k)) f,
    markedMaskLaw, poissonMixture_expect, candidateBlock_expect]
  apply integral_congr_ae
  filter_upwards [] with d
  rw [candidateStep_iterate]
  simp only [finiteMap, FiniteLaw.expect, Finset.sum_mul, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cs _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 2
  ext x
  simp only [candidateResidual, clauseMask, Finset.mem_filter, Finset.mem_univ, true_and]

end FixedClauseThreshold.Computability

end OAI
