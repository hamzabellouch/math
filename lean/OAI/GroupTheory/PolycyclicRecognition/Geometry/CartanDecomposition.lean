import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularPrimary
import Mathlib.Algebra.Lie.CartanExists

namespace OAI

/-! # Cartan models for the real triangular adjoint action

The nilpotent ideal and Cartan subalgebra span the algebra, and the Cartan
subalgebra maps onto the actual canonical height quotient.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)

theorem triangular_cartan_spanning (T : TriangularAdjoint L n)
    (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] :
    (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule = ⊤ := by
  let := T.isTriangularizable
  exact cartanRootIdeal_sup_cartan H

/-- Every height has a representative in the Cartan subalgebra. -/
theorem cartan_height_surjective (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] :
    Function.Surjective ((heightProjection T.character).comp H.subtype) := by
  intro w
  obtain ⟨x, hx⟩ := heightProjection_surjective T.character w
  have hx' : x ∈ (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule := by
    rw [triangular_cartan_spanning T H]
    trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx'
  refine ⟨⟨v, hv⟩, ?_⟩
  have hz : heightProjection T.character u = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (cartanRootIdeal_le_kernel H T hu)
  change heightProjection T.character v = w
  rw [← hx, ← huv, map_add, hz, zero_add]

/-- Existence and the Lie-algebra assertions of the manuscript's Cartan
model lemma. All terms are constructed from the actual adjoint basis. -/
theorem exists_cartan_model :
    ∃ H : LieSubalgebra ℝ L, ∃ _ : H.IsCartanSubalgebra,
      LieRing.IsNilpotent (cartanRootIdeal H) ∧
      cartanRootIdeal H ≤ derivedSeries ℝ L 1 ∧
      (cartanRootIdeal H).toSubmodule ⊔ H.toSubmodule = ⊤ ∧
      Function.Surjective ((heightProjection T.character).comp H.subtype) := by
  obtain ⟨x, hx⟩ := exists_isCartanSubalgebra_engel ℝ L
  let := hx
  exact ⟨LieSubalgebra.engel ℝ x, hx, cartanRootIdeal_nilpotent _ T,
    cartanRootIdeal_le_derived _, triangular_cartan_spanning T _,
    cartan_height_surjective T _⟩

omit T in
/-- A nilpotent ambient algebra has no nonzero Cartan roots. -/
theorem cartanRootIdeal_eq_bot_of_nilpotent
    (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] [LieRing.IsNilpotent L] :
    cartanRootIdeal H = ⊥ := by
  apply le_antisymm _ bot_le
  apply LieSubmodule.lieSpan_le.mpr
  rintro v ⟨χ, hχ, _⟩
  have hz : (χ : H → ℝ) = 0 := by
    funext h
    exact χ.apply_eq_zero_of_isNilpotent h
      ((LieAlgebra.isNilpotent_iff_forall (R := ℝ) (L := L)).mp inferInstance h)
  exact (hχ hz).elim

/-- The model's nilpotent root ideal vanishes exactly in the nilpotent case. -/
theorem cartanRootIdeal_eq_bot_iff (T : TriangularAdjoint L n)
    (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] :
    cartanRootIdeal H = ⊥ ↔ LieRing.IsNilpotent L := by
  constructor
  · intro h
    have htop : H = ⊤ := by
      apply LieSubalgebra.toSubmodule_injective
      simpa only [h, LieSubmodule.bot_toSubmodule, bot_sup_eq,
        LieSubalgebra.top_toSubmodule] using triangular_cartan_spanning T H
    let f : H →ₗ⁅ℝ⁆ L := H.incl
    have hf : Function.Surjective f := by
      intro x
      exact ⟨⟨x, by rw [htop]; trivial⟩, rfl⟩
    exact hf.lieAlgebra_isNilpotent
  · intro h
    let := h
    exact cartanRootIdeal_eq_bot_of_nilpotent H

end PolycyclicRecognition

end

end OAI
