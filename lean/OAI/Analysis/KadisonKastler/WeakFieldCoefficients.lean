import OAI.Analysis.KadisonKastler.WeakFieldNorm
import OAI.Analysis.KadisonKastler.WeakOperatorCoefficients

namespace OAI

/-! # Intrinsic scalar coefficients of weak operator fields -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorField

/-- A representative with exactly the quotient norm bound. -/
def representative (T : WeakOperatorField (H := H) μ) : WeakOperatorRepresentative (H := H) μ :=
  Classical.choose (exists_operatorFieldRepresentative T)

theorem quotient_representative (T : WeakOperatorField (H := H) μ) :
    operatorFieldQuotient μ (representative T) = T :=
  (Classical.choose_spec (exists_operatorFieldRepresentative T)).1

theorem norm_representative_le (T : WeakOperatorField (H := H) μ) :
    ‖representative T‖ ≤ ‖T‖ :=
  (Classical.choose_spec (exists_operatorFieldRepresentative T)).2

/-- Matrix coefficients depend only on the almost-everywhere operator class. -/
def coefficient (T : WeakOperatorField (H := H) μ) (ξ η : H) : ScalarLInfinity μ :=
  WeakOperatorRepresentative.coefficient (representative T) ξ η

theorem coefficient_quotient (F : WeakOperatorRepresentative (H := H) μ) (ξ η : H) :
    coefficient (operatorFieldQuotient μ F) ξ η = WeakOperatorRepresentative.coefficient F ξ η := by
  apply WeakOperatorRepresentative.coefficient_eq_of_ae
  exact (operatorFieldQuotient_eq_iff μ _ _).mp (quotient_representative _)

variable [IsFiniteMeasure μ]

theorem norm_coefficient_le (T : WeakOperatorField (H := H) μ) (ξ η : H) :
    ‖coefficient T ξ η‖ ≤ ‖T‖ * ‖ξ‖ * ‖η‖ :=
  ((WeakOperatorRepresentative.scalarKernel (representative T)).norm_le ξ η).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (norm_representative_le T) (norm_nonneg ξ)) (norm_nonneg η))

variable [TopologicalSpace.SeparableSpace H]

omit [IsFiniteMeasure μ] in
/-- Intrinsic scalar coefficients separate the quotient. -/
theorem ext_coeff {T S : WeakOperatorField (H := H) μ}
    (h : ∀ ξ η, coefficient T ξ η = coefficient S ξ η) : T = S := by
  rw [← quotient_representative T, ← quotient_representative S]
  apply (WeakOperatorRepresentative.quotient_eq_iff_coefficient_eq _ _).mpr
  exact h

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
theorem coefficient_add (T S : WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficient (T + S) ξ η = coefficient T ξ η + coefficient S ξ η := by
  rw [← quotient_representative T, ← quotient_representative S, ← map_add,
    coefficient_quotient, coefficient_quotient, coefficient_quotient]
  apply Lp.ext
  filter_upwards [WeakOperatorRepresentative.coefficient_ae (representative T + representative S) ξ η,
    WeakOperatorRepresentative.coefficient_ae (representative T) ξ η,
    WeakOperatorRepresentative.coefficient_ae (representative S) ξ η,
    Lp.coeFn_add (WeakOperatorRepresentative.coefficient (representative T) ξ η)
      (WeakOperatorRepresentative.coefficient (representative S) ξ η)] with x ha hb hc hd
  simp only [Pi.add_apply] at hd
  rw [ha, hd, hb, hc, WeakOperatorRepresentative.eval_add,
    add_apply, inner_add_right]

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
theorem coefficient_smul (c : ℂ) (T : WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficient (c • T) ξ η = c • coefficient T ξ η := by
  rw [← quotient_representative T, ← map_smul, coefficient_quotient, coefficient_quotient]
  apply Lp.ext
  filter_upwards [WeakOperatorRepresentative.coefficient_ae (c • representative T) ξ η,
    WeakOperatorRepresentative.coefficient_ae (representative T) ξ η,
    Lp.coeFn_smul c (WeakOperatorRepresentative.coefficient (representative T) ξ η)] with x ha hb hc
  simp only [Pi.smul_apply] at hc
  rw [ha, hc, hb, WeakOperatorRepresentative.eval_smul,
    smul_apply, inner_smul_right]
  rfl

end WeakOperatorField

end

end KadisonKastler

end OAI
