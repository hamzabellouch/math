import OAI.Probability.InvariantIsing.Cavity.CavitySelectedRestrictedSpin
import OAI.Probability.InvariantIsing.Cavity.CavitySelectedCappedAverage

namespace OAI

/-! Elementary boundedness and product identities for the restricted
finite-spin factor used in the actual cavity Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def cavityRestrictedFactor {d k : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (T B : ℝ) (y : EuclideanSpace ℝ (Fin d)) (ε : Spin k) : ℝ :=
  if 1+‖y‖^2 ≤ 1+B^2 then Real.exp (min (cavityLogFactor K L C y ε) T) else 0

lemma cavityRestrictedFactor_mem {d k : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (T B : ℝ) (y : EuclideanSpace ℝ (Fin d)) (ε : Spin k) :
    cavityRestrictedFactor K L C T B y ε ∈ Icc 0 (Real.exp T) := by
  unfold cavityRestrictedFactor
  split_ifs
  · exact ⟨(Real.exp_pos _).le,Real.exp_le_exp.mpr (min_le_right _ _)⟩
  · exact ⟨le_rfl,(Real.exp_pos _).le⟩

lemma measurable_cavityRestrictedFactor {d k : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (T B : ℝ) : Measurable (fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
      cavityRestrictedFactor K L C T B p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro ε
  apply Measurable.ite _ _ measurable_const
  · apply measurableSet_le _ measurable_const
    fun_prop
  · exact (((continuous_cavityLogFactor K L C ε).measurable).min measurable_const).exp

lemma measurable_cavityRestrictedFactor_comp {d k : ℕ} {E : Type*} [MeasurableSpace E]
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (Y : E → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
    (ε : E → Spin k) (hε : Measurable ε) :
    Measurable (fun x => cavityRestrictedFactor K L C T B (Y x) (ε x)) := by
  have hp : Measurable (fun x => (Y x,ε x)) := hY.prodMk hε
  change Measurable ((fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
    cavityRestrictedFactor K L C T B p.1 p.2) ∘ (fun x => (Y x,ε x)))
  exact Measurable.comp (g := fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
    cavityRestrictedFactor K L C T B p.1 p.2) (f := fun x => (Y x,ε x))
      (measurable_cavityRestrictedFactor K L C T B) hp

lemma cavityRestrictedFlatSpinValue_bound {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : (Fin r → Spin k) → ℝ) {M : ℝ} (hF : ∀ ε, ‖F ε‖ ≤ M)
    (y : EuclideanSpace ℝ (Fin r × Fin d)) :
    ‖cavityRestrictedFlatSpinValue K L C T B π F y‖ ≤ (Real.exp T)^r * M := by
  unfold cavityRestrictedFlatSpinValue
  split_ifs
  · exact cavityCappedFlatSpinValue_bound K L C T π F hF y
  · rw [norm_zero]
    exact mul_nonneg (by positivity) ((norm_nonneg (F default)).trans (hF default))

lemma cavityRestrictedFlatSpinValue_eq {r d k : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ) (π : Measure (Spin k))
    (F : (Fin r → Spin k) → ℝ) (y : EuclideanSpace ℝ (Fin r × Fin d)) :
    cavityRestrictedFlatSpinValue K L C T B π F y =
      ∫ ε : Fin r → Spin k, (∏ i, cavityRestrictedFactor K L C T B
        (WithLp.toLp 2 (fun a => y (i,a))) (ε i)) * F ε ∂Measure.pi (fun _ => π) := by
  classical
  by_cases hy : ∀ i, 1+‖(WithLp.toLp 2 (fun a => y (i,a)) : EuclideanSpace ℝ (Fin d))‖^2 ≤ 1+B^2
  · simp only [cavityRestrictedFlatSpinValue,hy,ite_true,cavityRestrictedFactor,
      cavityCappedFlatSpinValue]
    simp
  · obtain ⟨i,hi⟩ := not_forall.mp hy
    have hp (ε : Fin r → Spin k) : (∏ j, cavityRestrictedFactor K L C T B
        (WithLp.toLp 2 (fun a => y (j,a))) (ε j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [cavityRestrictedFactor,hi,ite_false])
    simp only [cavityRestrictedFlatSpinValue,hy,ite_false,hp,zero_mul,integral_zero]

end InvariantIsing

end

end OAI
