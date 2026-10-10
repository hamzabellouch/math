import OAI.NumberTheory.Ostmann.Construction.ExternalSquareFibers

namespace OAI

/-! # Disintegration of the actual two-prime law at a prime square -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def primeSquareFiberEquiv (p : ℕ) [Fact p.Prime]
    (z : (ZMod p)ˣ × (ZMod p)ˣ) :
    {w : (ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ //
      primePairResidueReduction (dvd_pow_self p (by decide : 2 ≠ 0)) w = z} ≃
      SquareLiftPairs p (z.1 : ZMod p) (z.2 : ZMod p) where
  toFun w :=
    (⟨w.1.1, congrArg (fun t : (ZMod p)ˣ × (ZMod p)ˣ => (t.1 : ZMod p)) w.2⟩,
      ⟨w.1.2, congrArg (fun t : (ZMod p)ˣ × (ZMod p)ˣ => (t.2 : ZMod p)) w.2⟩)
  invFun v := by
    have hx : squareReduction p (v.1 : ZMod (p ^ 2)) ≠ 0 := by
      rw [v.1.property]
      exact Units.ne_zero z.1
    have hy : squareReduction p (v.2 : ZMod (p ^ 2)) ≠ 0 := by
      rw [v.2.property]
      exact Units.ne_zero z.2
    let ux := ((isUnit_square_iff (v.1 : ZMod (p ^ 2))).mpr hx).unit
    let uy := ((isUnit_square_iff (v.2 : ZMod (p ^ 2))).mpr hy).unit
    refine ⟨(ux, uy), ?_⟩
    apply Prod.ext <;> apply Units.ext
    · change squareReduction p (ux : ZMod (p ^ 2)) = (z.1 : ZMod p)
      rw [IsUnit.unit_spec]
      exact v.1.property
    · change squareReduction p (uy : ZMod (p ^ 2)) = (z.2 : ZMod p)
      rw [IsUnit.unit_spec]
      exact v.2.property
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext <;> apply Units.ext <;> exact IsUnit.unit_spec _
  right_inv v := by
    apply Prod.ext <;> apply Subtype.ext <;> dsimp only <;> exact IsUnit.unit_spec _

noncomputable def primeSquareDecompose (p : ℕ) [Fact p.Prime] :
    ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) ≃
      Σ z : (ZMod p)ˣ × (ZMod p)ˣ, SquareLiftPairs p (z.1 : ZMod p) (z.2 : ZMod p) :=
  (Equiv.sigmaFiberEquiv
    (primePairResidueReduction (dvd_pow_self p (by decide : 2 ≠ 0)))).symm.trans
      (Equiv.sigmaCongrRight (primeSquareFiberEquiv p))

theorem primeSquare_average (p : ℕ) [Fact p.Prime]
    (F : (ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ → ℂ) :
    (Fintype.card ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ * (∑ z, F z) =
      (Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) : ℂ)⁻¹ *
        ∑ z : (ZMod p)ˣ × (ZMod p)ˣ, ((p : ℂ) ^ 2)⁻¹ *
          ∑ v : SquareLiftPairs p (z.1 : ZMod p) (z.2 : ZMod p),
            F ((primeSquareDecompose p).symm ⟨z, v⟩) := by
  let e := primeSquareDecompose p
  have hc : Fintype.card ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) =
      Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) * p ^ 2 := by
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [squareLiftPairs_card, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hs := e.symm.sum_comp F
  rw [Fintype.sum_sigma] at hs
  rw [← hs, hc, Nat.cast_mul, Nat.cast_pow, mul_inv_rev, ← Finset.mul_sum]
  ring

theorem primeSquareDecompose_symm_values (p : ℕ) [Fact p.Prime]
    (z : (ZMod p)ˣ × (ZMod p)ˣ) (v : SquareLiftPairs p (z.1 : ZMod p) (z.2 : ZMod p)) :
    ((((primeSquareDecompose p).symm ⟨z, v⟩).1 : ZMod (p ^ 2)),
      (((primeSquareDecompose p).symm ⟨z, v⟩).2 : ZMod (p ^ 2))) =
      (v.1.val, v.2.val) := by
  exact congrArg (fun w : SquareLiftPairs p (z.1 : ZMod p) (z.2 : ZMod p) =>
    (w.1.val, w.2.val)) ((primeSquareFiberEquiv p z).apply_symm_apply v)

theorem primeSquare_raw_average (p : ℕ) [Fact p.Prime]
    (F : ZMod (p ^ 2) → ZMod (p ^ 2) → ℂ) :
    (Fintype.card ((ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
        (∑ z : (ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ, F z.1 z.2) =
      (Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) : ℂ)⁻¹ *
        ∑ z : (ZMod p)ˣ × (ZMod p)ˣ, ((p : ℂ) ^ 2)⁻¹ *
          ∑ v : SquareLiftPairs p (z.1 : ZMod p) (z.2 : ZMod p), F v.1.val v.2.val := by
  have h := primeSquare_average p
    (fun z : (ZMod (p ^ 2))ˣ × (ZMod (p ^ 2))ˣ => F z.1 z.2)
  have he (z : (ZMod p)ˣ × (ZMod p)ˣ)
      (v : SquareLiftPairs p (z.1 : ZMod p) (z.2 : ZMod p)) :
      F ((primeSquareDecompose p).symm ⟨z, v⟩).1
          ((primeSquareDecompose p).symm ⟨z, v⟩).2 = F v.1.val v.2.val :=
    congrArg (fun a : ZMod (p ^ 2) × ZMod (p ^ 2) => F a.1 a.2)
      (primeSquareDecompose_symm_values p z v)
  simpa only [he] using h

end Ostmann

end OAI
