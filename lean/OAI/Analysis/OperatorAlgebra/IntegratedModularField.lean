import OAI.Analysis.ModularTheory.RightContinuity

namespace OAI

/-! Integrable bounded continuous coefficient fields give actual operators
in the modular crossed product. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : BoundedRecovery.StandardModularData H)

def modularFieldOperator (a : ℝ → H →L[ℂ] H) (r : ℝ) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  modularLpRepresentation volume S.D (a r) * modularLpTranslateOperator r

lemma modularFieldOperator_continuous (a : ℝ → H →L[ℂ] H) (ha : Continuous a)
    (f : Lp H 2 (volume : Measure ℝ)) :
    Continuous (fun r => modularFieldOperator S a r f) := by
  exact ((starHomContinuousLinear
    (modularLpRepresentation volume S.D).toNonUnitalStarAlgHom).continuous.comp ha).clm_apply
    (continuous_modularLpTranslate f)

lemma modularFieldOperator_norm_le (a : ℝ → H →L[ℂ] H) (C : ℝ)
    (hC : ∀ r, ‖a r‖ ≤ C) (r : ℝ) : ‖modularFieldOperator S a r‖ ≤ C := by
  exact (norm_mul_le _ _).trans ((mul_le_mul
    ((NonUnitalStarAlgHom.norm_apply_le
      (modularLpRepresentation volume S.D).toNonUnitalStarAlgHom (a r)).trans (hC r))
    (modularLpTranslate_opNorm_le r) (norm_nonneg _) (le_trans (norm_nonneg _) (hC r))).trans_eq
      (mul_one C))

def integratedModularField (a : ℝ → H →L[ℂ] H) (ha : Continuous a)
    (C : ℝ) (hC : ∀ r, ‖a r‖ ≤ C) (k : ℝ → ℂ) (hk : Integrable k) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  BoundedRecovery.strongIntegral k hk (modularFieldOperator S a)
    (modularFieldOperator_continuous S a ha) C (modularFieldOperator_norm_le S a C hC)

lemma integratedModularField_mem (a : ℝ → H →L[ℂ] H) (ha : Continuous a)
    (hM : ∀ r, a r ∈ S.M) (C : ℝ) (hC : ∀ r, ‖a r‖ ≤ C)
    (k : ℝ → ℂ) (hk : Integrable k) :
    integratedModularField S a ha C hC k hk ∈ modularCrossedProduct volume S := by
  rw [← (modularCrossedProduct volume S).commutant_commutant,
    VonNeumannAlgebra.mem_commutant_iff]
  intro b hb
  apply ContinuousLinearMap.ext
  intro f
  have hi := BoundedRecovery.integrable_smul_bounded_orbit hk
    (modularFieldOperator_continuous S a ha f)
    (fun r => (modularFieldOperator S a r).le_opNorm f |>.trans
      (mul_le_mul_of_nonneg_right (modularFieldOperator_norm_le S a C hC r) (norm_nonneg f)))
  change b (∫ r, k r • modularFieldOperator S a r f) =
    ∫ r, k r • modularFieldOperator S a r (b f)
  rw [← b.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with r
  rw [map_smul]
  congr 1
  have hm : modularFieldOperator S a r ∈ modularCrossedProduct volume S :=
    mul_mem (modularCrossedProduct_coeff volume S ⟨a r, hM r⟩)
      (modularCrossedProduct_translate volume S r)
  exact (congrArg (fun T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) => T f)
    (VonNeumannAlgebra.mem_commutant_iff.mp hb _ hm)).symm

end WeakPureInfiniteness

end

end OAI
