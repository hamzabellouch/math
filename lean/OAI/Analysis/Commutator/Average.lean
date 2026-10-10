import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open MeasureTheory Filter

namespace Kadison.WeakOperatorIntegral

variable {ι H : Type*} [MeasurableSpace ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (μ : Measure ι) [IsProbabilityMeasure μ] (T : ι → H →L[ℂ] H)
  (hI : ∀ x y, Integrable (fun i => inner ℂ (T i x) y) μ)
  (V : H →L[ℂ] H)
  (hV : ∀ x y, inner ℂ (V x) y = ∫ i, inner ℂ (T i x) y ∂μ)

omit [CompleteSpace H] in
include hV in
lemma norm_le_of_integral {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) : ‖V‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound V hC
  intro x
  have hi : ‖inner ℂ (V x) (V x)‖ ≤ C*‖x‖*‖V x‖ := by
    rw [hV]
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun i => inner ℂ (T i x) (V x)) (C := C*‖x‖*‖V x‖)
      (Eventually.of_forall (fun i => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (((T i).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg x))) (norm_nonneg _))))
    simpa only [probReal_univ,mul_one] using h
  rw [← inner_self_re_eq_norm,inner_self_eq_norm_mul_norm] at hi
  by_cases hv : ‖V x‖=0
  · rw [hv]; positivity
  · have hp : 0 < ‖V x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa [mul_comm,mul_left_comm,mul_assoc] using hi)

omit [IsProbabilityMeasure μ] in
include hI hV in
lemma commutator_coeff (a : H →L[ℂ] H) (x y : H) :
    inner ℂ ((V*a-a*V) x) y = ∫ i, inner ℂ ((T i*a-a*T i) x) y ∂μ := by
  simp only [sub_apply,mul_apply_eq_comp,inner_sub_left]
  simp only [← ContinuousLinearMap.adjoint_inner_right a]
  rw [hV,hV,integral_sub (hI (a x) y) (hI x (a.adjoint y))]

include hI hV in
lemma commutator_norm (a : H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i, ‖T i*a-a*T i‖ ≤ C) : ‖V*a-a*V‖ ≤ C := by
  exact norm_le_of_integral μ (fun i => T i*a-a*T i) (V*a-a*V)
    (commutator_coeff μ T hI V hV a) hC hb

include hI hV in
lemma commutes (a : H →L[ℂ] H) (hb : ∀ i, T i*a=a*T i) : V*a=a*V := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  exact le_antisymm (commutator_norm μ T hI V hV a le_rfl (by intro i; rw [hb i,sub_self,norm_zero]))
    (norm_nonneg _)

omit [IsProbabilityMeasure μ] in
include hV in
lemma sandwich_coeff (a b : H →L[ℂ] H) (x y : H) :
    inner ℂ ((a*V*b) x) y = ∫ i, inner ℂ ((a*T i*b) x) y ∂μ := by
  simp only [mul_apply_eq_comp]
  simp only [← ContinuousLinearMap.adjoint_inner_right a]
  exact hV _ _

include hV in
lemma preserves_sandwich (a b Z : H →L[ℂ] H) (hZ : ∀ i, a*T i*b=Z) : a*V*b=Z := by
  ext x
  apply ext_inner_right ℂ
  intro y
  rw [sandwich_coeff μ T V hV]
  simp_rw [hZ]
  simp only [integral_const,probReal_univ,one_smul]

end Kadison.WeakOperatorIntegral

namespace Kadison.WeakOperatorIntegral

open MeasureTheory Filter

variable {ι H : Type*} [MeasurableSpace ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (μ : Measure ι) [IsProbabilityMeasure μ] (T : ι → H →L[ℂ] H)
  (hI : ∀ x y, Integrable (fun i => inner ℂ (T i x) y) μ)
  (V : H →L[ℂ] H)
  (hV : ∀ x y, inner ℂ (V x) y = ∫ i, inner ℂ (T i x) y ∂μ)

omit [CompleteSpace H] in
include hI hV in
lemma difference_coeff (W : H →L[ℂ] H) (x y : H) :
    inner ℂ ((V-W) x) y = ∫ i, inner ℂ ((T i-W) x) y ∂μ := by
  simp only [sub_apply,inner_sub_left]
  rw [hV,integral_sub (hI x y) (integrable_const _)]
  simp only [integral_const,MeasureTheory.probReal_univ,one_smul]

omit [CompleteSpace H] in
include hI hV in
lemma difference_norm (W : H →L[ℂ] H) {C : ℝ} (hC : 0≤C)
    (hb : ∀ i, ‖T i-W‖≤C) : ‖V-W‖≤C :=
  norm_le_of_integral μ (fun i => T i-W) (V-W) (difference_coeff μ T hI V hV W) hC hb

omit [IsProbabilityMeasure μ] in
include hI hV in
lemma compressed_commutator_coeff (a b s : H →L[ℂ] H) (x y : H) :
    inner ℂ ((a*(V*s-s*V)*b) x) y = ∫ i, inner ℂ ((a*(T i*s-s*T i)*b) x) y ∂μ :=
  sandwich_coeff μ _ (V*s-s*V) (commutator_coeff μ T hI V hV s) a b x y

include hI hV in
lemma preserves_compressed_commutator (a b s W : H →L[ℂ] H)
    (hb : ∀ i, a*(T i*s-s*T i)*b=W) : a*(V*s-s*V)*b=W :=
  preserves_sandwich μ _ _ (commutator_coeff μ T hI V hV s) a b W hb

end Kadison.WeakOperatorIntegral

end

end
end

end OAI
