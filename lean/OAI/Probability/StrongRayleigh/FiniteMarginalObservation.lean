import OAI.Probability.StrongRayleigh.MarginalBase
import OAI.Probability.StrongRayleigh.FiniteFieldTilt

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336AdditiveD139

lemma finite_field_sum_restrict {I : Type u_1} [DecidableEq I]
    (S J : Finset I) (hSJ : S ⊆ J) (h : I → ℝ) (x : I → Bool) :
    (∑ j : J, (if j.1 ∈ S then h j.1 else 0) * boolReal (x j.1)) =
      ∑ j ∈ S, h j * boolReal (x j) := by
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_subtype J (fun _ => Iff.rfl)
    (fun j => if j ∈ S then h j * boolReal (x j) else 0), Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hSJ]

lemma integral_finiteMarginal {I : Type u_2} (μ : ProbabilityMeasure (I → Bool))
    (J : Finset I) (f : (J → Bool) → ℝ) :
    (∫ x, f x ∂(finiteMarginal μ J : Measure (J → Bool))) =
      ∫ x, f (fun j : J => x j.1) ∂(μ : Measure (I → Bool)) := by
  rw [finiteMarginal, ProbabilityMeasure.toMeasure_map]
  apply integral_map
  · exact (Measurable.of_eval (fun j => measurable_pi_apply j.1)).aemeasurable
  · exact (measurable_of_countable f).aestronglyMeasurable

theorem finiteFieldMean_eq_tiltMean_finiteMarginal {I : Type u_3} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (S J : Finset I) (hSJ : S ⊆ J)
    (h : I → ℝ) (i : J) :
    finiteFieldMean μ S h i.1 =
      tiltMean (finiteMarginal μ J) (fun j : J => if j.1 ∈ S then h j.1 else 0) i := by
  classical
  let h' : J → ℝ := fun j => if j.1 ∈ S then h j.1 else 0
  let w : (J → Bool) → ℝ := fun x => Real.exp (∑ j : J, h' j * boolReal (x j))
  have hw (x : I → Bool) : w (fun j : J => x j.1) = finiteFieldWeight S h x := by
    unfold w finiteFieldWeight h'
    rw [finite_field_sum_restrict S J hSJ]
  have hden : (∫ x, finiteFieldWeight S h x ∂(μ : Measure (I → Bool))) =
      tiltPartition (finiteMarginal μ J) h' := by
    rw [← show (fun x => w (fun j : J => x j.1)) = finiteFieldWeight S h from funext hw,
      ← integral_finiteMarginal μ J w, integral_fintype Integrable.of_finite]
    unfold tiltPartition
    apply Finset.sum_congr (by ext; simp)
    intro x _
    simp only [smul_eq_mul, w, Measure.real]
    ring
  have hnum : (∫ x, boolReal (x i.1) * finiteFieldWeight S h x
      ∂(μ : Measure (I → Bool))) =
      ∑ x : J → Bool, w x * ((finiteMarginal μ J : Measure (J → Bool)) {x}).toReal *
        boolReal (x i) := by
    have heq : (fun x : I → Bool => boolReal (x i.1) * finiteFieldWeight S h x) =
        fun x => (fun z : J → Bool => boolReal (z i) * w z) (fun j : J => x j.1) := by
      funext x
      change boolReal (x i.1) * finiteFieldWeight S h x =
        boolReal (x i.1) * w (fun j : J => x j.1)
      rw [hw]
    rw [heq, ← integral_finiteMarginal μ J (fun z => boolReal (z i) * w z),
      integral_fintype Integrable.of_finite]
    apply Finset.sum_congr (by ext; simp)
    intro x _
    simp only [smul_eq_mul, Measure.real]
    ring
  unfold finiteFieldMean tiltMean
  rw [hnum, hden]
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro x _
  rfl

def finiteObservationField {I : Type u_4} [DecidableEq I]
    (i : I) (S : Finset I) (t : ℝ) (y : I → ℝ) : {j // j ∈ insert i S} → ℝ :=
  fun j => if j.1 ∈ S then y j.1 - t / 2 else 0

def finiteObservationDrift {I : Type u_5} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I)
    (t : ℝ) (y : I → ℝ) : ℝ :=
  tiltMean (finiteMarginal μ (insert i S)) (finiteObservationField i S t y)
    ⟨i, Finset.mem_insert_self i S⟩

theorem finiteObservationDrift_eq_finiteFieldMean {I : Type u_6} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I)
    (t : ℝ) (y : I → ℝ) :
    finiteObservationDrift μ i S t y =
      finiteFieldMean μ S (fun j => y j - t / 2) i := by
  exact (finiteFieldMean_eq_tiltMean_finiteMarginal μ S (insert i S)
    (Finset.subset_insert i S) (fun j => y j - t / 2)
    ⟨i, Finset.mem_insert_self i S⟩).symm

theorem finiteObservationDrift_mem_Icc {I : Type u_7} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I)
    (t : ℝ) (y : I → ℝ) : finiteObservationDrift μ i S t y ∈ Set.Icc (0 : ℝ) 1 := by
  rw [finiteObservationDrift_eq_finiteFieldMean]
  exact finiteFieldMean_mem_unitInterval μ S _ i

theorem measurable_finiteObservationDrift {I : Type u_8} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I) :
    Measurable (fun p : ℝ × (I → ℝ) => finiteObservationDrift μ i S p.1 p.2) := by
  simp_rw [finiteObservationDrift_eq_finiteFieldMean]
  apply (measurable_finiteFieldMean μ S i).comp
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply j).comp measurable_snd).sub (measurable_fst.div_const 2)

theorem finiteObservationDrift_translate {Γ : Type u_9} [Group Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) (hμ : InvariantBinaryLaw μ)
    (g i : Γ) (S : Finset Γ) (t : ℝ) (y : Γ → ℝ) :
    finiteObservationDrift μ (g * i) (S.image (fun j => g * j)) t (leftTranslate g y) =
      finiteObservationDrift μ i S t y := by
  simp_rw [finiteObservationDrift_eq_finiteFieldMean]
  exact finiteFieldMean_translate μ hμ g i S (fun j => y j - t / 2)

theorem finiteObservationField_abs_sub_le {I : Type u_10} [DecidableEq I]
    (i : I) (S : Finset I) (t : ℝ) (y y' : I → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hy : ∀ j : I, |y j - y' j| ≤ D) :
    ∀ j : {j // j ∈ insert i S},
      |finiteObservationField i S t y j - finiteObservationField i S t y' j| ≤ D := by
  intro j
  by_cases hj : j.1 ∈ S
  · simpa only [finiteObservationField, hj, ite_true, sub_sub_sub_cancel_right] using hy j.1
  · simpa only [finiteObservationField, hj, ite_false, sub_self, abs_zero] using hD

theorem finiteObservationDrift_response_of_finite_response
    {I : Type u_11} [DecidableEq I] (μ : ProbabilityMeasure (I → Bool))
    (i : I) (S : Finset I)
    (hresponse : ∀ (h h' : {j // j ∈ insert i S} → ℝ) (D : ℝ), 0 ≤ D →
      (∀ j : {j // j ∈ insert i S}, |h j - h' j| ≤ D) →
      |tiltMean (finiteMarginal μ (insert i S)) h ⟨i, Finset.mem_insert_self i S⟩ -
       tiltMean (finiteMarginal μ (insert i S)) h' ⟨i, Finset.mem_insert_self i S⟩| ≤ D / 2)
    (t : ℝ) (y y' : I → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hy : ∀ j : I, |y j - y' j| ≤ D) :
    |finiteObservationDrift μ i S t y - finiteObservationDrift μ i S t y'| ≤ D / 2 := by
  exact hresponse _ _ D hD (finiteObservationField_abs_sub_le i S t y y' D hD hy)

theorem finiteObservationDrift_eq_tiltMean_of_mem {I : Type u_12} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I) (hi : i ∈ S)
    (t : ℝ) (y : I → ℝ) :
    finiteObservationDrift μ i S t y =
      tiltMean (finiteMarginal μ S) (fun j : S => y j.1 - t / 2) ⟨i, hi⟩ := by
  rw [finiteObservationDrift_eq_finiteFieldMean,
    finiteFieldMean_eq_tiltMean_finiteMarginal μ S S (Finset.Subset.refl S)
      (fun j => y j - t / 2) ⟨i, hi⟩]
  congr 1
  funext j
  exact ite_eq_left j.property

@[simp] theorem finiteFieldMean_zero_field {I : Type u_13}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (i : I) :
    finiteFieldMean μ S (fun _ => 0) i =
      ∫ x, boolReal (x i) ∂(μ : Measure (I → Bool)) := by
  simp [finiteFieldMean, finiteFieldWeight]

@[simp] theorem finiteObservationDrift_zero_zero {I : Type u_14} [DecidableEq I]
    (μ : ProbabilityMeasure (I → Bool)) (i : I) (S : Finset I) :
    finiteObservationDrift μ i S 0 (fun _ => 0) =
      ∫ x, boolReal (x i) ∂(μ : Measure (I → Bool)) := by
  simp [finiteObservationDrift_eq_finiteFieldMean]

end Problem336AdditiveD139

end

end OAI
