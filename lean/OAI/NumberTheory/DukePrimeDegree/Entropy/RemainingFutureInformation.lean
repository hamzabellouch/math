import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductKernel
import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureAtomCovariance
import OAI.NumberTheory.DukePrimeDegree.Entropy.RemainingExpansionInformation
import OAI.NumberTheory.DukePrimeDegree.Dynamics.OneSidedCoboundary

namespace OAI

/-! # Mean information of the actual whole-future root atom -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

/-- Positive finite whole-future mass converts exact leaf covariance into
an integrable information function with the canonical root mean. -/
theorem remainingFutureInformation_integrable_integral (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k = 0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1) :
    let I := fun x => -Real.log
      (c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) /
        c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 1 x)).toReal
    Integrable I μ ∧ (∫ x, I x ∂μ) =
      ∑ p : ↥(allPositiveRoots (d+1) \ P),
        (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  let T : X (d+1) → X (d+1) :=
    fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let M (k : ℕ) (x : X (d+1)) :=
    c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q k x)
  let C (x : X (d+1)) :=
    c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1)
  let J (x : X (d+1)) := Real.log (C x).toReal
  let f (x : X (d+1)) := -Real.log (M 0 x).toReal
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    dsimp [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hM : AEMeasurable (M 0) μ :=
    c.aemeasurable_remainingFutureMass d hP hf μ hA ell hell Q hQ 0
  have hfmeas : AEStronglyMeasurable f μ :=
    hM.ennreal_toReal.log.neg.aestronglyMeasurable
  have hJ := c.remainingExpansionInformation_integrable_integral hP hf ell μ hA
  have hcov := c.ae_remainingTimeProduct_futureAtom d hP hf μ hA ell hell Q hQ
  have hC := c.ae_remainingExpansionMass_pos_ne_top hP hf ell μ hA
  have hboth : ∀ᵐ x ∂μ, M 0 x ≠ 0 ∧ M 0 x ≠ ∞ ∧
      M 1 x ≠ 0 ∧ M 1 x ≠ ∞ ∧ C x ≠ 0 ∧ C x ≠ ∞ ∧
      M 0 (T x) = (C x)⁻¹ * M 1 x := by
    filter_upwards [hmass, hT.quasiMeasurePreserving.ae hmass, hcov, hC]
      with x hx hTx hcx hc
    have hmono : M 0 x ≤ M 1 x :=
      measure_mono (c.remainingFutureAtom_zero_subset_one ell hell Q x)
    have hfactor : M 1 x = C x * M 0 (T x) := by
      change M 0 (T x) = (C x)⁻¹ * M 1 x at hcx
      rw [hcx, ← mul_assoc, ENNReal.mul_inv_cancel hc.1.ne' hc.2, one_mul]
    refine ⟨hx.1.ne', ne_of_lt (hx.2.trans_lt ENNReal.one_lt_top),
      (hx.1.trans_le hmono).ne', ?_, hc.1.ne', hc.2, hcx⟩
    rw [hfactor]
    exact ENNReal.mul_ne_top hc.2 (ne_of_lt (hTx.2.trans_lt ENNReal.one_lt_top))
  have hI : ∀ᵐ x ∂μ, 0 ≤ -Real.log (M 0 x / M 1 x).toReal := by
    filter_upwards [hboth] with x hx
    rw [ENNReal.toReal_div]
    apply neg_nonneg.mpr
    apply Real.log_nonpos (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    apply (div_le_one (ENNReal.toReal_pos hx.2.2.1 hx.2.2.2.1)).mpr
    exact ENNReal.toReal_mono hx.2.2.2.1
      (measure_mono (c.remainingFutureAtom_zero_subset_one ell hell Q x))
  have heq : (fun x => -Real.log (M 0 x / M 1 x).toReal) =ᵐ[μ]
      fun x => J x + (f x-f (T x)) := by
    filter_upwards [hboth] with x hx
    have he := normalized_mass_log_identity hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1
      hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2
    simpa only [sub_eq_add_neg, add_assoc] using he
  have H := information_integrable_integral_of_ae_coboundary μ hT hfmeas hJ.1 hI heq
  exact ⟨H.1, H.2.trans hJ.2⟩

end EliminationChain
end DukePrimeDegree

end

end OAI
