import OAI.Probability.ClassicalON.SpinIsotropy

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace ClassicalON

instance spinOperator_continuousStar (n : ℕ) : ContinuousStar (SpinOperator n) :=
  ⟨ContinuousLinearMap.adjoint.continuous⟩

abbrev SpinOrthogonal (n : ℕ) := unitary (SpinOperator n)

instance spinOrthogonal_compact (n : ℕ) [NeZero n] : CompactSpace (SpinOrthogonal n) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : SpinOperator n) 1).of_isClosed_subset isClosed_unitary
  intro Q hQ
  simpa only [Metric.mem_closedBall,dist_zero_right,CStarRing.norm_coe_unitary ⟨Q,hQ⟩] using (le_rfl : (1:ℝ) ≤ 1)

instance spinOrthogonal_measurableSpace (n : ℕ) : MeasurableSpace (SpinOrthogonal n) := borel _
instance spinOrthogonal_borelSpace (n : ℕ) : BorelSpace (SpinOrthogonal n) := ⟨rfl⟩

def orthogonalLaw (n : ℕ) [NeZero n] : Measure (SpinOrthogonal n) :=
  ((Measure.haar : Measure (SpinOrthogonal n)) Set.univ)⁻¹ • Measure.haar

instance orthogonalLaw_isProbability (n : ℕ) [NeZero n] : IsProbabilityMeasure (orthogonalLaw n) := by
  constructor
  unfold orthogonalLaw
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (isOpen_univ.measure_pos Measure.haar Set.univ_nonempty)) (measure_ne_top _ _)

instance orthogonalLaw_isHaar (n : ℕ) [NeZero n] : (orthogonalLaw n).IsHaarMeasure := by
  unfold orthogonalLaw
  exact Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr (ne_of_gt (isOpen_univ.measure_pos Measure.haar Set.univ_nonempty)))

instance orthogonalLaw_isRightInvariant (n : ℕ) [NeZero n] :
    (orthogonalLaw n).IsMulRightInvariant := by
  constructor
  intro R
  have hm : Measurable (fun Q : SpinOrthogonal n => Q*R) := (continuous_id.mul continuous_const).measurable
  have : IsProbabilityMeasure ((orthogonalLaw n).map (·*R)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have he := Measure.isMulInvariant_eq_smul_of_compactSpace
    ((orthogonalLaw n).map (·*R)) (orthogonalLaw n)
  have hmass := congrArg (fun μ : Measure (SpinOrthogonal n) => μ Set.univ) he
  simp only [measure_univ,Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,mul_one] at hmass
  have hc : Measure.haarScalarFactor ((orthogonalLaw n).map (·*R)) (orthogonalLaw n)=1 := by
    exact_mod_cast hmass.symm
  rw [hc,one_smul] at he
  exact he

def orthogonalSpin {n : ℕ} (Q : SpinOrthogonal n) (s : Spin n) : Spin n :=
  spinRotation (Unitary.linearIsometryEquiv Q) s

theorem continuous_orthogonalSpin (n : ℕ) :
    Continuous (Function.uncurry (orthogonalSpin (n := n))) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).clm_apply (continuous_subtype_val.comp continuous_snd)

@[simp] theorem orthogonalSpin_mul {n : ℕ} (Q R : SpinOrthogonal n) (s : Spin n) :
    orthogonalSpin (Q*R) s=orthogonalSpin Q (orthogonalSpin R s) := by
  rfl

theorem orthogonalSpin_transitive {n : ℕ} (s t : Spin n) :
    ∃ Q : SpinOrthogonal n,orthogonalSpin Q s=t := by
  let R := (Submodule.span ℝ {s.val-t.val})ᗮ.reflection
  refine ⟨Unitary.linearIsometryEquiv.symm R,?_⟩
  apply Subtype.ext
  change (Unitary.linearIsometryEquiv (Unitary.linearIsometryEquiv.symm R)) s.val=t.val
  rw [MulEquiv.apply_symm_apply]
  exact Submodule.reflection_sub (by rw [spin_norm,spin_norm])

theorem orthogonalSpin_preserves {n : ℕ} (Q : SpinOrthogonal n) :
    MeasurePreserving (orthogonalSpin Q) (sphereProbability n) (sphereProbability n) :=
  spinRotation_preserves_probability _

theorem integral_orthogonalSpin_eq {n : ℕ} [NeZero n] (f : Spin n → ℝ)
    (hf : Continuous f) (s : Spin n) :
    (∫ Q, f (orthogonalSpin Q s) ∂orthogonalLaw n)=∫ t,f t ∂sphereProbability n := by
  have he (t : Spin n) : (∫ Q,f (orthogonalSpin Q t) ∂orthogonalLaw n)=
      ∫ Q,f (orthogonalSpin Q s) ∂orthogonalLaw n := by
    obtain ⟨R,rfl⟩ := orthogonalSpin_transitive s t
    simp_rw [← orthogonalSpin_mul]
    exact integral_mul_right_eq_self (fun Q => f (orthogonalSpin Q s)) R
  have hh := integral_integral_swap (μ := sphereProbability n) (ν := orthogonalLaw n)
    (f := fun t Q => f (orthogonalSpin Q t)) (compact_integrable (show Continuous (fun p : Spin n×SpinOrthogonal n => f (orthogonalSpin p.2 p.1)) from
      hf.comp ((continuous_orthogonalSpin n).comp continuous_swap)))
  simp_rw [he] at hh
  rw [integral_const,probReal_univ,one_smul] at hh
  have hp (Q : SpinOrthogonal n) : (∫ t,f (orthogonalSpin Q t) ∂sphereProbability n)=∫ t,f t ∂sphereProbability n :=
    (orthogonalSpin_preserves Q).integral_comp (spinRotation (Unitary.linearIsometryEquiv Q)).measurableEmbedding f
  simp_rw [hp] at hh
  simpa using hh

end ClassicalON

end

end OAI
