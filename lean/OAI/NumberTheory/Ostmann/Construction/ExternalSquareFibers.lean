import OAI.NumberTheory.Ostmann.Construction.ExternalResidueReduction
import OAI.NumberTheory.Ostmann.Arithmetic.JointSquareLiftExclusions

namespace OAI

/-! # Exact disintegration into the two giant prime-square lift fibers -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def externalSquareFiberEquiv (p : ℕ) [Fact p.Prime]
    (z : ZMod p × (ZMod p)ˣ) :
    {w : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ //
      externalResidueReduction (dvd_pow_self p (by decide : 2 ≠ 0)) w = z} ≃
      SquareLiftPairs p z.1 (z.2 : ZMod p) where
  toFun w :=
    (⟨w.1.1, congrArg Prod.fst w.2⟩,
      ⟨w.1.2, congrArg (fun t : ZMod p × (ZMod p)ˣ => (t.2 : ZMod p)) w.2⟩)
  invFun v := by
    have hred : squareReduction p (v.2 : ZMod (p ^ 2)) ≠ 0 := by
      rw [v.2.property]
      exact Units.ne_zero z.2
    let hu := (isUnit_square_iff (v.2 : ZMod (p ^ 2))).mpr hred
    refine ⟨(v.1, hu.unit), ?_⟩
    apply Prod.ext
    · exact v.1.property
    · apply Units.ext
      change squareReduction p (hu.unit : ZMod (p ^ 2)) = (z.2 : ZMod p)
      rw [IsUnit.unit_spec]
      exact v.2.property
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Units.ext
      exact IsUnit.unit_spec _
  right_inv v := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp only
      exact IsUnit.unit_spec _

noncomputable def externalSquareDecompose (p : ℕ) [Fact p.Prime] :
    (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) ≃
      Σ z : ZMod p × (ZMod p)ˣ, SquareLiftPairs p z.1 (z.2 : ZMod p) :=
  (Equiv.sigmaFiberEquiv (externalResidueReduction (dvd_pow_self p (by decide : 2 ≠ 0)))).symm.trans
    (Equiv.sigmaCongrRight (externalSquareFiberEquiv p))

/-- The original uniform mixed law first chooses its residues modulo `p`,
then chooses uniformly among the `p²` lifts of that pair. -/
theorem externalSquare_average (p : ℕ) [Fact p.Prime]
    (F : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ → ℂ) :
    (Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ * (∑ z, F z) =
      (Fintype.card (ZMod p × (ZMod p)ˣ) : ℂ)⁻¹ *
        ∑ z : ZMod p × (ZMod p)ˣ, ((p : ℂ) ^ 2)⁻¹ *
          ∑ v : SquareLiftPairs p z.1 (z.2 : ZMod p),
            F ((externalSquareDecompose p).symm ⟨z, v⟩) := by
  let e := externalSquareDecompose p
  have hc : Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) =
      Fintype.card (ZMod p × (ZMod p)ˣ) * p ^ 2 := by
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [squareLiftPairs_card, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hs := e.symm.sum_comp F
  rw [Fintype.sum_sigma] at hs
  rw [← hs, hc, Nat.cast_mul, Nat.cast_pow, mul_inv_rev, ← Finset.mul_sum]
  ring

end Ostmann

end OAI
