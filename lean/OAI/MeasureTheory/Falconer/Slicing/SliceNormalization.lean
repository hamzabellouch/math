import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Normalizing the retained original-label slice laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def normalizedSliceLaw (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) : ProbabilityMeasure X :=
  ⟨(μ univ)⁻¹ • μ, ⟨by
    rw [Measure.smul_apply,smul_eq_mul,ENNReal.inv_mul_cancel hμ (measure_ne_top μ univ)]⟩⟩

theorem normalizedSliceLaw_apply (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) (S : Set X) :
    (normalizedSliceLaw μ hμ : Measure X) S = (μ univ)⁻¹*μ S := rfl

theorem normalizedSliceLaw_bound (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) (S : Set X) {L B : ℝ≥0∞}
    (hL : L ≤ μ univ) (hS : μ S ≤ B) :
    (normalizedSliceLaw μ hμ : Measure X) S ≤ L⁻¹*B := by
  rw [normalizedSliceLaw_apply]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr hL) hS

theorem normalizedSliceLaw_ae (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂(normalizedSliceLaw μ hμ : Measure X), P x :=
  Measure.ae_smul_measure hP _

theorem positive_incidence_marginals (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (E : Set (X × Y)) (hE : 0 < (μ.prod ν) E) :
    μ univ ≠ 0 ∧ ν univ ≠ 0 := by
  have hu : 0 < μ univ*ν univ := hE.trans_le (by
    calc
      _ ≤ (μ.prod ν) univ := measure_mono (subset_univ _)
      _ = _ := by rw [← univ_prod_univ,Measure.prod_prod])
  exact ⟨fun h => by simp only [h,zero_mul,lt_self_iff_false] at hu,
    fun h => by simp only [h,mul_zero,lt_self_iff_false] at hu⟩

theorem incidence_marginal_lower_bounds (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (E : Set (X × Y))
    {P M I : ℝ≥0∞} (hP : μ univ ≤ P) (hM : ν univ ≤ M)
    (hP0 : P ≠ 0) (hPtop : P ≠ ∞) (hM0 : M ≠ 0) (hMtop : M ≠ ∞)
    (hI : I ≤ (μ.prod ν) E) : I/M ≤ μ univ ∧ I/P ≤ ν univ := by
  have hi : I ≤ μ univ*ν univ := hI.trans (by
    calc
      _ ≤ (μ.prod ν) univ := measure_mono (subset_univ _)
      _ = _ := by rw [← univ_prod_univ,Measure.prod_prod])
  constructor
  · calc
      I/M ≤ (μ univ*M)*M⁻¹ := mul_le_mul_left (hi.trans (mul_le_mul_right hM _)) _
      _ = μ univ := by rw [mul_assoc,ENNReal.mul_inv_cancel hM0 hMtop,mul_one]
  · calc
      I/P ≤ (ν univ*P)*P⁻¹ := mul_le_mul_left
        (hi.trans ((mul_le_mul_left hP _).trans_eq (mul_comm _ _))) _
      _ = ν univ := by rw [mul_assoc,ENNReal.mul_inv_cancel hP0 hPtop,mul_one]

theorem normalizedSliceLaw_incidence (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ univ ≠ 0) (hν : ν univ ≠ 0) (E : Set (X × Y)) :
    ((normalizedSliceLaw μ hμ : Measure X).prod (normalizedSliceLaw ν hν : Measure Y)) E =
      (μ univ*ν univ)⁻¹*(μ.prod ν) E := by
  change (((μ univ)⁻¹ • μ).prod ((ν univ)⁻¹ • ν)) E = _
  rw [Measure.prod_smul_left,Measure.prod_smul_right,Measure.smul_apply,Measure.smul_apply,
    smul_eq_mul,smul_eq_mul,← mul_assoc,← ENNReal.mul_inv (Or.inl hμ) (Or.inr hν)]

theorem normalizedSliceLaw_incidence_lower (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ univ ≠ 0) (hν : ν univ ≠ 0) (E : Set (X × Y))
    {P M I : ℝ≥0∞} (hP : μ univ ≤ P) (hM : ν univ ≤ M) (hI : I ≤ (μ.prod ν) E) :
    (P*M)⁻¹*I ≤
      ((normalizedSliceLaw μ hμ : Measure X).prod (normalizedSliceLaw ν hν : Measure Y)) E := by
  rw [normalizedSliceLaw_incidence]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr (mul_le_mul' hP hM)) hI

end Falconer

end OAI
