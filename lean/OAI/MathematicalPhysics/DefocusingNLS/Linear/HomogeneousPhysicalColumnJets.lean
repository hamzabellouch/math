import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingRobin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalTrace

namespace OAI

/-! # Exact value and derivative maps of the physical outgoing columns -/

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "V₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem homogeneousCircularValue_derivatives (νp νm eta q : ℂ) (m : ℕ)
    (Y : ℝ → V₄) (t : ℝ)
    (hY : HasDerivAt Y (circularLeadingField t (Y t) +
      circularBoundedField νp νm eta m q (Y t)) t) :
    deriv (fun s => (Y s).1.1) t = (Y t).1.2 ∧
      deriv (fun s => (Y s).2.1) t = (Y t).2.2 := by
  have hp := (ContinuousLinearMap.fst ℝ V V).hasFDerivAt.comp_hasDerivAt t hY
  have hm := (ContinuousLinearMap.snd ℝ V V).hasFDerivAt.comp_hasDerivAt t hY
  constructor
  · simpa only [Function.comp_def, ContinuousLinearMap.coe_fst',
      circularLeadingField, circularBoundedField, Prod.fst_add, zero_add]
      using (homogeneousPair_fst_hasDerivAt hp).deriv
  · simpa only [Function.comp_def, ContinuousLinearMap.coe_snd',
      circularLeadingField, circularBoundedField, Prod.snd_add, Prod.fst_add, zero_add]
      using (homogeneousPair_fst_hasDerivAt hm).deriv

theorem homogeneousPhysicalState_pair_derivatives
    (νp νm eta : ℂ) (m : ℕ) (Q : ℂ) (Z : ℝ → V₄) (r : ℝ)
    (hZ : HasDerivAt Z (spectralPhysicalCircularField νp νm eta m Q r (Z r)) r) :
    HasDerivAt (fun s => spectralPhysicalValueMap (Z s))
        (spectralPhysicalDerivativeMap (Z r)) r ∧
      HasDerivAt (fun s => spectralPhysicalDerivativeMap (Z s))
        (-homogeneousRadialDamping r (spectralPhysicalDerivativeMap (Z r)) -
          homogeneousRadialStiffness νp νm eta m Q r (spectralPhysicalValueMap (Z r))) r := by
  have hv := (spectralPhysicalValueMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r hZ
  have hd := (spectralPhysicalDerivativeMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r hZ
  exact ⟨hv, hd.congr_deriv (homogeneousRadial_acceleration νp νm eta m Q r (Z r))⟩

theorem homogeneousPhysicalColumn_logValue (νp νm : ℂ) (Y : ℝ → V₄) (r : ℝ) :
    spectralPhysicalValueMap (spectralPhysicalPair νp νm Y r) =
      homogeneousPhysicalLogColumn νp νm (fun t => (Y t).1.1)
        (fun t => (Y t).2.1) (Real.log r) := rfl

theorem homogeneousPhysicalColumn_logDerivative
    (νp νm : ℂ) (Y : ℝ → V₄) (r : ℝ)
    (hp : deriv (fun t => (Y t).1.1) (Real.log r) = (Y (Real.log r)).1.2)
    (hm : deriv (fun t => (Y t).2.1) (Real.log r) = (Y (Real.log r)).2.2) :
    spectralPhysicalDerivativeMap (spectralPhysicalPair νp νm Y r) =
      r⁻¹ • homogeneousPhysicalLogDerivativeColumn νp νm
        (fun t => (Y t).1.1) (fun t => (Y t).2.1) (Real.log r) := by
  change (Complex.exp (νp * (Real.log r : ℂ)) / (r : ℂ) *
      (νp * (Y (Real.log r)).1.1 + (Y (Real.log r)).1.2),
    Complex.exp (νm * (Real.log r : ℂ)) / (r : ℂ) *
      (νm * (Y (Real.log r)).2.1 + (Y (Real.log r)).2.2)) = _
  rw [homogeneousPhysicalLogDerivativeColumn, homogeneousDiagonal_apply,
    homogeneousDiagonal_apply]
  apply Prod.ext
  all_goals
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Complex.real_smul, hp, hm, div_eq_mul_inv, Complex.ofReal_inv]
    ring

theorem homogeneousRobin_smul_derivatives (u v du dv : V) (c : ℝ) :
    spectralRobinOperator u v (c • du) (c • dv) = c • spectralRobinOperator u v du dv := by
  apply ContinuousLinearMap.ext
  intro w
  simp only [spectralRobinOperator, ContinuousLinearMap.comp_apply, smul_apply,
    spectralTwoColumns_apply]
  rw [smul_comm _ c du, smul_comm _ c dv, smul_add]

theorem homogeneousPhysicalColumn_robin (νp νm : ℂ) (Yp Ym : ℝ → V₄) (r : ℝ)
    (hpp : deriv (fun t => (Yp t).1.1) (Real.log r) = (Yp (Real.log r)).1.2)
    (hpm : deriv (fun t => (Yp t).2.1) (Real.log r) = (Yp (Real.log r)).2.2)
    (hmp : deriv (fun t => (Ym t).1.1) (Real.log r) = (Ym (Real.log r)).1.2)
    (hmm : deriv (fun t => (Ym t).2.1) (Real.log r) = (Ym (Real.log r)).2.2) :
    spectralRobinOperator
      (spectralPhysicalValueMap (spectralPhysicalPair νp νm Yp r))
      (spectralPhysicalValueMap (spectralPhysicalPair νp νm Ym r))
      (spectralPhysicalDerivativeMap (spectralPhysicalPair νp νm Yp r))
      (spectralPhysicalDerivativeMap (spectralPhysicalPair νp νm Ym r)) =
      r⁻¹ • spectralRobinOperator
        (homogeneousPhysicalLogColumn νp νm (fun t => (Yp t).1.1) (fun t => (Yp t).2.1)
          (Real.log r))
        (homogeneousPhysicalLogColumn νp νm (fun t => (Ym t).1.1) (fun t => (Ym t).2.1)
          (Real.log r))
        (homogeneousPhysicalLogDerivativeColumn νp νm
          (fun t => (Yp t).1.1) (fun t => (Yp t).2.1) (Real.log r))
        (homogeneousPhysicalLogDerivativeColumn νp νm
          (fun t => (Ym t).1.1) (fun t => (Ym t).2.1) (Real.log r)) := by
  rw [homogeneousPhysicalColumn_logValue, homogeneousPhysicalColumn_logValue,
    homogeneousPhysicalColumn_logDerivative νp νm Yp r hpp hpm,
    homogeneousPhysicalColumn_logDerivative νp νm Ym r hmp hmm,
    homogeneousRobin_smul_derivatives]

end DefocusingNLS

end OAI
