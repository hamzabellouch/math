import OAI.NumberTheory.Ostmann.Construction.ExternalSquareFibers

namespace OAI

/-! # Original coordinates of the exact square-fiber disintegration -/

namespace Ostmann
open scoped Classical BigOperators

theorem externalSquareFiberEquiv_symm_values (p : ℕ) [Fact p.Prime]
    (z : ZMod p × (ZMod p)ˣ) (v : SquareLiftPairs p z.1 (z.2 : ZMod p)) :
    (((externalSquareFiberEquiv p z).symm v).val.1,
      (((externalSquareFiberEquiv p z).symm v).val.2 : ZMod (p ^ 2))) =
      (v.1.val, v.2.val) := by
  exact congrArg (fun w : SquareLiftPairs p z.1 (z.2 : ZMod p) => (w.1.val, w.2.val))
    ((externalSquareFiberEquiv p z).apply_symm_apply v)

theorem externalSquareDecompose_symm_values (p : ℕ) [Fact p.Prime]
    (z : ZMod p × (ZMod p)ˣ) (v : SquareLiftPairs p z.1 (z.2 : ZMod p)) :
    (((externalSquareDecompose p).symm ⟨z, v⟩).1,
      (((externalSquareDecompose p).symm ⟨z, v⟩).2 : ZMod (p ^ 2))) =
      (v.1.val, v.2.val) :=
  externalSquareFiberEquiv_symm_values p z v

/-- The disintegration formula with the two raw residue coordinates exposed. -/
theorem externalSquare_raw_average (p : ℕ) [Fact p.Prime]
    (F : ZMod (p ^ 2) → ZMod (p ^ 2) → ℂ) :
    (Fintype.card (ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ) : ℂ)⁻¹ *
        (∑ z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ, F z.1 z.2) =
      (Fintype.card (ZMod p × (ZMod p)ˣ) : ℂ)⁻¹ *
        ∑ z : ZMod p × (ZMod p)ˣ, ((p : ℂ) ^ 2)⁻¹ *
          ∑ v : SquareLiftPairs p z.1 (z.2 : ZMod p), F v.1.val v.2.val := by
  have h := externalSquare_average p
    (fun z : ZMod (p ^ 2) × (ZMod (p ^ 2))ˣ => F z.1 z.2)
  have he (z : ZMod p × (ZMod p)ˣ) (v : SquareLiftPairs p z.1 (z.2 : ZMod p)) :
      F ((externalSquareDecompose p).symm ⟨z, v⟩).1
          ((externalSquareDecompose p).symm ⟨z, v⟩).2 = F v.1.val v.2.val :=
    congrArg (fun a : ZMod (p ^ 2) × ZMod (p ^ 2) => F a.1 a.2)
      (externalSquareDecompose_symm_values p z v)
  simpa only [he] using h

end Ostmann

end OAI
