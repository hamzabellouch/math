import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardFermionSpectrum
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.ChargeTransfer

namespace OAI

/-! The unit-charge application uses full Coulomb Gram coercivity rather
than absolute row dominance. These supporting estimates keep the actual
long-range penalty and its exact hole-double denominator. -/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace ContinuumCoulomb

/-- Full quadratic coercivity gives a gap on every half-filled charge defect. -/
theorem chargePenalty_Gram_gap {m : ℕ} (U c : ℝ) (V : Fin m → Fin m → ℝ)
    (hc : 0 ≤ c)
    (hGram : ∀ d : Fin m → ℝ,
      c * ∑ i, d i ^ 2 ≤ U * ∑ i, d i ^ 2 + ∑ i, ∑ j, V i j * d i * d j)
    (occupation : Fin m → Fin 3) (hfill : ∑ i, (occupation i : ℕ) = m)
    (hdefect : ¬∀ i, occupation i = 1) : c ≤ chargePenalty U V occupation := by
  have hquad := hGram (occupationDeviation occupation)
  have hsize := occupation_defect_size occupation hfill hdefect
  have hproduct := mul_nonneg hc (sub_nonneg.mpr hsize)
  unfold chargePenalty
  nlinarith

/-- The same Gram condition controls the physical virtual excitation
without replacing its exact denominator by the global coercivity constant. -/
theorem chargeTransfer_Gram_denominator {m : ℕ} (U c : ℝ) (V : Fin m → Fin m → ℝ)
    (hGram : ∀ d : Fin m → ℝ,
      c * ∑ i, d i ^ 2 ≤ U * ∑ i, d i ^ 2 + ∑ i, ∑ j, V i j * d i * d j)
    (hole double : Fin m) (hne : hole ≠ double)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0) :
    c ≤ U - V hole double := by
  have hquad := hGram (occupationDeviation (chargeTransferOccupation hole double))
  have hpen := chargeTransfer_penalty U V hole double hne hsymm hdiag
  unfold chargePenalty at hpen
  rw [chargeTransfer_deviation_sq_sum hole double hne] at hquad hpen
  nlinarith

theorem chargePenalty_Gram_inverse_data {m : ℕ} {Basis : Type*} [Fintype Basis]
    (U c : ℝ) (V : Fin m → Fin m → ℝ) (occupation : Basis → Fin m → Fin 3)
    (hc : 0 < c)
    (hGram : ∀ d : Fin m → ℝ,
      c * ∑ i, d i ^ 2 ≤ U * ∑ i, d i ^ 2 + ∑ i, ∑ j, V i j * d i * d j)
    (hfill : ∀ s, ∑ i, (occupation s i : ℕ) = m) :
    let weight : ChargeHighBasis occupation → ℝ :=
      fun s => chargePenalty U V (occupation s.val)
    (∀ x, diagonalPenalty weight (diagonalPenalty (fun s => (weight s)⁻¹) x) = x) ∧
      ‖diagonalPenalty (fun s => (weight s)⁻¹)‖ ≤ 1 / c ∧
      (∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, diagonalPenalty weight x⟫_ℝ) := by
  classical
  intro weight
  have hgap (s : ChargeHighBasis occupation) : c ≤ weight s :=
    chargePenalty_Gram_gap U c V hc.le hGram (occupation s.val) (hfill s.val) s.property
  exact ⟨diagonalPenalty_inverse_right weight (fun s => ne_of_gt (hc.trans_le (hgap s))),
    diagonalPenalty_inverse_norm hc weight hgap, diagonalPenalty_gap weight c hgap⟩

namespace HubbardGlobal
variable {Edge : Type*} [Fintype Edge]

/-- Actual full Fock blocks, with smallness measured against the Gram gap. -/
theorem actual_hubbard_Gram_second_order (m : ℕ) (U c : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ) (hc : 0 < c)
    (hGram : ∀ d : Fin (m + 1) → ℝ,
      c * ∑ i, d i ^ 2 ≤ U * ∑ i, d i ^ 2 + ∑ i, ∑ j, V i j * d i * d j)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon < 1 / 2)
    (ht : 4 * ∑ e, |t e| ≤ epsilon * c) :
    let weight : HalfFilledHighBasis m → ℝ :=
      fun A => chargePenalty U V (occupationAt m A.val.val)
    |Perturbation.blockBottom (diagonalPenalty weight)
        (actualHubbardHighHopping m left right t) (actualHubbardCoupling m left right t) -
      Perturbation.effectiveBottom (0 : ActualHubbardLowSpace m →L[ℝ] ActualHubbardLowSpace m)
        (diagonalPenalty (fun A => (weight A)⁻¹)) (actualHubbardCoupling m left right t)| ≤
      2 * c * epsilon ^ 3 := by
  classical
  intro weight
  obtain ⟨hAT, hT, hgap⟩ := chargePenalty_Gram_inverse_data U c V
    (fun A : HalfFilledBasis m => occupationAt m A.val) hc hGram (halfFilled_occupation_sum m)
  exact Perturbation.finite_blockBottom_second_order
    (diagonalPenalty weight) (diagonalPenalty (fun A => (weight A)⁻¹))
    (actualHubbardHighHopping m left right t) (actualHubbardCoupling m left right t)
    hc hepsilon hsmall hAT (diagonalPenalty_symmetric weight)
    (fun x => (mul_nonneg hc.le (sq_nonneg ‖x‖)).trans (hgap x))
    hgap hT ((actualHubbardCoupling_norm m left right t).trans ht)
    ((actualHubbardHighHopping_norm m left right t).trans ht)
    (hubbardLowUnit (m + 1)) (hubbardLowUnit_norm (m + 1))

/-- Complete fixed-particle fermion-to-spin spectrum under full Gram
coercivity. The exact denominators U−Vij follow from that same condition. -/
theorem hubbardFermionBottom_Gram_Heisenberg (m : ℕ) (U c : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0) (hc : 0 < c)
    (hGram : ∀ d : Fin (m + 1) → ℝ,
      c * ∑ i, d i ^ 2 ≤ U * ∑ i, d i ^ 2 + ∑ i, ∑ j, V i j * d i * d j)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hcal : ∀ e, t e ^ 2 = J e * (U - V (left e) (right e)))
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon < 1 / 2)
    (ht : 4 * ∑ e, |t e| ≤ epsilon * c) :
    |hubbardFermionBottom m U V left right t - graphSourceBottom m left right J| ≤
      2 * c * epsilon ^ 3 := by
  have hgap (e : Edge) : U - V (left e) (right e) ≠ 0 :=
    ne_of_gt (hc.trans_le (chargeTransfer_Gram_denominator U c V hGram
      (left e) (right e) (hloop e) hsymm hdiag))
  rw [hubbardFermionBottom_eq_blockBottom m U V left right t hloop,
    ← actualHubbard_effectiveBottom m U V hsymm hdiag left right t J
      hloop hsimple hgap hcal]
  exact actual_hubbard_Gram_second_order m U c V hc hGram left right t hepsilon hsmall ht

end HubbardGlobal
end ContinuumCoulomb

end

end OAI
