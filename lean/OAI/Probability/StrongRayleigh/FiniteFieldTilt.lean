import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem336AdditiveD139

def finiteFieldWeight {I : Type u_1} (S : Finset I) (h : I → ℝ)
    (x : I → Bool) : ℝ :=
  Real.exp (∑ j ∈ S, h j * boolReal (x j))

def finiteFieldMean {I : Type u_2} (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (h : I → ℝ) (i : I) : ℝ :=
  (∫ x, boolReal (x i) * finiteFieldWeight S h x ∂(μ : Measure (I → Bool))) /
    (∫ x, finiteFieldWeight S h x ∂(μ : Measure (I → Bool)))

private theorem measurable_boolReal : Measurable boolReal := by
  exact measurable_of_countable _

theorem measurable_finiteFieldWeight {I : Type u_3} (S : Finset I) (h : I → ℝ) :
    Measurable (finiteFieldWeight S h) := by
  unfold finiteFieldWeight
  apply Measurable.exp
  exact Finset.measurable_sum S (fun j _ => measurable_const.mul
    (measurable_boolReal.comp (measurable_pi_apply j)))

theorem measurable_finiteFieldWeight_joint {I : Type u_4} (S : Finset I) :
    Measurable (fun p : (I → ℝ) × (I → Bool) => finiteFieldWeight S p.1 p.2) := by
  unfold finiteFieldWeight
  apply Measurable.exp
  exact Finset.measurable_sum S (fun j _ =>
    ((measurable_pi_apply j).comp measurable_fst).mul
      (measurable_boolReal.comp ((measurable_pi_apply j).comp measurable_snd)))

theorem finiteFieldWeight_pos {I : Type u_5} (S : Finset I) (h : I → ℝ)
    (x : I → Bool) : 0 < finiteFieldWeight S h x := Real.exp_pos _

theorem integrable_finiteFieldWeight {I : Type u_6}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (h : I → ℝ) :
    Integrable (finiteFieldWeight S h) (μ : Measure (I → Bool)) := by
  apply (integrable_const (Real.exp (∑ j ∈ S, |h j|))).mono'
    (measurable_finiteFieldWeight S h).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (finiteFieldWeight_pos S h x)]
  apply Real.exp_le_exp.mpr
  apply Finset.sum_le_sum
  intro j _
  cases x j <;> simp [boolReal, le_abs_self]

theorem finiteFieldWeight_integral_pos {I : Type u_7}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (h : I → ℝ) :
    0 < ∫ x, finiteFieldWeight S h x ∂(μ : Measure (I → Bool)) := by
  apply (integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (finiteFieldWeight_pos S h x).le)
    (integrable_finiteFieldWeight μ S h)).mpr
  have hs : Function.support (finiteFieldWeight S h) = Set.univ := by
    ext x
    simp [Function.mem_support, ne_of_gt (finiteFieldWeight_pos S h x)]
  rw [hs]
  simp

private theorem finiteField_boolReal_bounds (b : Bool) :
    0 ≤ boolReal b ∧ boolReal b ≤ 1 := by
  cases b <;> simp [boolReal]

theorem integrable_finiteFieldMean_numerator {I : Type u_8}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (h : I → ℝ) (i : I) :
    Integrable (fun x => boolReal (x i) * finiteFieldWeight S h x)
      (μ : Measure (I → Bool)) := by
  apply (integrable_finiteFieldWeight μ S h).mono'
    (((measurable_boolReal.comp (measurable_pi_apply i)).mul
      (measurable_finiteFieldWeight S h)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  have hb := finiteField_boolReal_bounds (x i)
  have hw := (finiteFieldWeight_pos S h x).le
  change ‖boolReal (x i) * finiteFieldWeight S h x‖ ≤ finiteFieldWeight S h x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 hw)]
  exact mul_le_of_le_one_left hw hb.2

theorem finiteFieldMean_mem_unitInterval {I : Type u_9}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (h : I → ℝ) (i : I) :
    finiteFieldMean μ S h i ∈ Set.Icc (0 : ℝ) 1 := by
  have hden := finiteFieldWeight_integral_pos μ S h
  have hnum : 0 ≤ ∫ x, boolReal (x i) * finiteFieldWeight S h x
      ∂(μ : Measure (I → Bool)) :=
    integral_nonneg fun x => mul_nonneg (finiteField_boolReal_bounds (x i)).1
      (finiteFieldWeight_pos S h x).le
  constructor
  · exact div_nonneg hnum hden.le
  · apply (div_le_one hden).mpr
    apply integral_mono (integrable_finiteFieldMean_numerator μ S h i)
      (integrable_finiteFieldWeight μ S h)
    intro x
    exact mul_le_of_le_one_left (finiteFieldWeight_pos S h x).le
      (finiteField_boolReal_bounds (x i)).2

theorem measurable_finiteFieldMean {I : Type u_10}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (i : I) :
    Measurable (fun h : I → ℝ => finiteFieldMean μ S h i) := by
  have hw := measurable_finiteFieldWeight_joint S
  have hn : Measurable (fun p : (I → ℝ) × (I → Bool) =>
      boolReal (p.2 i) * finiteFieldWeight S p.1 p.2) :=
    (measurable_boolReal.comp ((measurable_pi_apply i).comp measurable_snd)).mul hw
  exact hn.stronglyMeasurable.integral_prod_right.measurable.div
    hw.stronglyMeasurable.integral_prod_right.measurable

theorem finiteFieldWeight_translate {Γ : Type u_11} [Group Γ] [DecidableEq Γ]
    (g : Γ) (S : Finset Γ) (h : Γ → ℝ) (x : Γ → Bool) :
    finiteFieldWeight (S.image (fun j => g * j)) (leftTranslate g h)
      (leftTranslate g x) = finiteFieldWeight S h x := by
  classical
  unfold finiteFieldWeight
  congr 1
  rw [Finset.sum_image]
  · simp only [leftTranslate, inv_mul_cancel_left]
  · intro a _ b _ hab
    exact mul_left_cancel hab

theorem integral_leftTranslate_of_invariant {Γ : Type u_12} [Group Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (hμ : InvariantBinaryLaw μ)
    (g : Γ) (f : (Γ → Bool) → ℝ) (hf : Measurable f) :
    (∫ x, f (leftTranslate g x) ∂(μ : Measure (Γ → Bool))) =
      ∫ x, f x ∂(μ : Measure (Γ → Bool)) := by
  have hg : Measurable (leftTranslate g : (Γ → Bool) → (Γ → Bool)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (g⁻¹ * i))
  rw [← integral_map hg.aemeasurable hf.aestronglyMeasurable, hμ g]

theorem finiteFieldMean_translate {Γ : Type u_13} [Group Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (hμ : InvariantBinaryLaw μ)
    (g i : Γ) (S : Finset Γ) (h : Γ → ℝ) :
    finiteFieldMean μ (S.image (fun j => g * j)) (leftTranslate g h) (g * i) =
      finiteFieldMean μ S h i := by
  classical
  unfold finiteFieldMean
  congr 1
  · let f : (Γ → Bool) → ℝ := fun x =>
      boolReal (x (g * i)) * finiteFieldWeight (S.image (fun j => g * j))
        (leftTranslate g h) x
    have hf : Measurable f :=
      (measurable_boolReal.comp (measurable_pi_apply (g * i))).mul
        (measurable_finiteFieldWeight _ _)
    have heq := integral_leftTranslate_of_invariant μ hμ g f hf
    simpa only [f, leftTranslate, inv_mul_cancel_left,
      finiteFieldWeight_translate] using heq.symm
  · have heq := integral_leftTranslate_of_invariant μ hμ g
      (finiteFieldWeight (S.image (fun j => g * j)) (leftTranslate g h))
      (measurable_finiteFieldWeight _ _)
    simpa only [finiteFieldWeight_translate] using heq.symm

end Problem336AdditiveD139

end

end OAI
