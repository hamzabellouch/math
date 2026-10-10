import OAI.Analysis.KadisonKastler.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous

namespace OAI

/-! # The centralizer of an infinite product state is irreducible

The proof uses only dense local vectors and state-preserving local swaps
which move a local observable to an independent set of sites. These are
the finite-site properties of the two-ratio tensor product in section 6.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ambient vector functional, without any trace assumption. -/
def productVectorState (Ω : H) (T : H →L[ℂ] H) : ℂ := inner ℂ Ω (T Ω)

omit [CompleteSpace H] in
theorem norm_productVectorState_le (Ω : H) (hΩ : ‖Ω‖ = 1) (T : H →L[ℂ] H) :
    ‖productVectorState Ω T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖Ω‖ * ‖T Ω‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ω‖ * (‖T‖ * ‖Ω‖) := mul_le_mul_of_nonneg_left (T.le_opNorm Ω) (norm_nonneg Ω)
    _ = ‖T‖ := by rw [hΩ]; ring

/-- The state centralizer identity used by a finite-site swap. -/
def ProductStateCentralizes (D : VonNeumannAlgebra H) (Ω : H) (u : H →L[ℂ] H) : Prop :=
  ∀ x ∈ D, productVectorState Ω (u * x) = productVectorState Ω (x * u)

/-- State centralization and commutation with `x` allow a local observable
to be moved by the swap while leaving its pairing with `x` unchanged. -/
theorem productVectorState_swap (D : VonNeumannAlgebra H) (Ω : H)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ D)
    (hcentral : ProductStateCentralizes D Ω u)
    (a x : H →L[ℂ] H) (ha : a ∈ D) (hx : x ∈ D)
    (hcomm : (u : H →L[ℂ] H) * x = x * u) :
    productVectorState Ω (unitaryConj u a * x) = productVectorState Ω (a * x) := by
  have hxu : star (u : H →L[ℂ] H) * x * u = x := by
    calc
      _ = star (u : H →L[ℂ] H) * (x * u) := mul_assoc _ _ _
      _ = star (u : H →L[ℂ] H) * (u * x) := by rw [← hcomm]
      _ = x := by rw [← mul_assoc, Unitary.star_mul_self_of_mem u.property, one_mul]
  calc
    _ = productVectorState Ω ((u : H →L[ℂ] H) * (a * star (u : H →L[ℂ] H) * x)) := by
      simp only [unitaryConj, mul_assoc]
    _ = productVectorState Ω ((a * star (u : H →L[ℂ] H) * x) * u) :=
      hcentral _ (D.mul_mem (D.mul_mem ha (D.toStarSubalgebra.star_mem' hu)) hx)
    _ = productVectorState Ω (a * x) := by rw [mul_assoc a, mul_assoc a, hxu]

omit [CompleteSpace H] in
/-- A vector-functional error only sees the vector error in the right factor. -/
theorem productVectorState_mul_error (Ω : H) (hΩ : ‖Ω‖ = 1)
    (a x y : H →L[ℂ] H) :
    ‖productVectorState Ω (a * x) - productVectorState Ω (a * y)‖ ≤
      ‖a‖ * ‖(x - y) Ω‖ := by
  calc
    _ = ‖inner ℂ Ω (a ((x - y) Ω))‖ := by
      simp only [productVectorState, mul_apply_eq_comp, sub_apply, map_sub, inner_sub_right]
    _ ≤ ‖Ω‖ * ‖a ((x - y) Ω)‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ω‖ * (‖a‖ * ‖(x - y) Ω‖) :=
      mul_le_mul_of_nonneg_left (a.le_opNorm _) (norm_nonneg Ω)
    _ = ‖a‖ * ‖(x - y) Ω‖ := by rw [hΩ, one_mul]

/-- The two finite-site properties sufficient for the product-state argument.
No centralizer irreducibility or core-type conclusion is a field here. -/
structure LocalProductSwaps (D : VonNeumannAlgebra H) (Ω : H) where
  localAlgebra : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)
  local_le : ∀ n, localAlgebra n ≤ D.toStarSubalgebra
  dense : DenseRange (fun p : Σ n, localAlgebra n => (p.2 : H →L[ℂ] H) Ω)
  independent_swap : ∀ (k : ℕ) (a : localAlgebra k) (n : ℕ),
    ∃ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ D ∧
      ProductStateCentralizes D Ω u ∧
      ∀ b : localAlgebra n,
        productVectorState Ω (unitaryConj u a * b) =
          productVectorState Ω a * productVectorState Ω b

end

end KadisonKastler

end OAI
