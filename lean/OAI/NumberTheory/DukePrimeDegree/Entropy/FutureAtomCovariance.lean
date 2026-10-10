import OAI.NumberTheory.DukePrimeDegree.Entropy.RemainingFutureShift

namespace OAI

/-! # Exact covariance of actual whole-future leaf masses -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_mass_log_identity {a b c d : ℝ≥0∞}
    (ha0 : a ≠ 0) (haT : a ≠ ∞) (hb0 : b ≠ 0) (hbT : b ≠ ∞)
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) (hd : d = c⁻¹ * b) :
    -Real.log (a / b).toReal =
      Real.log c.toReal + (-Real.log a.toReal) - (-Real.log d.toReal) := by
  have ha : a.toReal ≠ 0 := (ENNReal.toReal_pos ha0 haT).ne'
  have hb : b.toReal ≠ 0 := (ENNReal.toReal_pos hb0 hbT).ne'
  have hc : c.toReal ≠ 0 := (ENNReal.toReal_pos hc0 hcT).ne'
  rw [ENNReal.toReal_div, Real.log_div ha hb, hd,
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    Real.log_mul (inv_ne_zero hc) hb, Real.log_inv]
  ring

namespace EliminationChain

theorem ae_remainingTimeProduct_futureAtom (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k = 0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q) :
    ∀ᵐ x ∂μ,
      c.remainingTimeProduct hP hf μ (rightAction x (diagonalOneParameter ell hell (-1)))
          (c.remainingFutureAtom ell hell Q 0
            (rightAction x (diagonalOneParameter ell hell (-1)))) =
        (c.remainingTimeProduct hP hf μ x
          ((c.rootDilation ell 1) ⁻¹' c.cube 1))⁻¹ *
        c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 1 x) := by
  filter_upwards [ae_remainingTimeProduct_diagonal d c hP hf μ hA ell hell (-1)] with x hx
  rw [hx]
  simp only [neg_neg]
  rw [anchorNormalize, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (c.rootDilation ell 1).measurable
      (c.measurableSet_remainingFutureAtom hf ell hell Q hQ 0 _),
    c.remainingFutureAtom_shift ell hell Q x,
    Measure.map_apply (c.rootDilation ell 1).measurable (c.cube_open 1).measurableSet]

end EliminationChain
end DukePrimeDegree

end

end OAI
