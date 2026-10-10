import OAI.Combinatorics.ProgressionColoring.HeavyLabelReturn

namespace OAI

/-!
# Finite rational labels for an actual heavy return

The previously proved reduced integer numerator lies in `[0,h)`. Converting
it to `Fin h` preserves primitivity and both rational paths. The second path
uses the actual second-system displacement, via the proved real dilation
identity.
-/

namespace QuantitativeVanDerWaerden.IsHeavyLabelReturn

variable {mesh : AdaptiveMesh} {q D lam Ucount k M j h : ℕ} {hU : 0 < Ucount}
  {a d : CyclicGroup q D} {beta : (Fin D → Fin Ucount) × (Fin D → mesh.Label)}
  (R : IsHeavyLabelReturn mesh q D lam Ucount k M hU a d beta j h)

include R

/-- The actual rational return paths with a finite numerator label and the
actual displacements in both coordinate systems. -/
theorem exists_fin_return_path (hq : 0 < q) :
    ∃ t : Fin D → Fin h,
      PrimitiveVector h (fun i => ((t i).val : ℤ)) ∧
      (∀ (n : ℕ) (i : Fin D), ∃ z : ℤ,
        xRep q D (a + n • d) i - xRep q D a i - (n : ℝ) / h *
          ((t i).val + (xRep q D (a + (j + h) • d) i - xRep q D (a + j • d) i)) = z) ∧
      (∀ (n : ℕ) (i : Fin D), ∃ z : ℤ,
        yRep q D lam (a + n • d) i - yRep q D lam a i - (n : ℝ) / h *
          ((lam : ℝ) * (t i).val +
            (yRep q D lam (a + (j + h) • d) i - yRep q D lam (a + j • d) i)) = z) := by
  obtain ⟨T, hTrange, hprimitive, hx, hy⟩ := R.primitive_return_path hq
  let t : Fin D → Fin h := fun i =>
    ⟨(T i).toNat, by have hr := hTrange i; omega⟩
  have htInt (i : Fin D) : ((t i).val : ℤ) = T i :=
    Int.toNat_of_nonneg (hTrange i).1
  have htReal (i : Fin D) : ((t i).val : ℝ) = (T i : ℝ) := by
    exact_mod_cast htInt i
  refine ⟨t, ?_, ?_, ?_⟩
  · have ht : (fun i => ((t i).val : ℤ)) = T := funext htInt
    rw [ht]
    exact hprimitive
  · intro n i
    simpa only [htReal i] using hx n i
  · intro n i
    obtain ⟨z, hz⟩ := hy n i
    refine ⟨z, ?_⟩
    rw [htReal i, R.dilation_eq i]
    convert hz using 1; ring

end QuantitativeVanDerWaerden.IsHeavyLabelReturn

end OAI
