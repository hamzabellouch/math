import OAI.GroupTheory.PolycyclicRecognition.Algebra.BracketWords
import Mathlib.Algebra.Lie.Nilpotent

namespace OAI

/-! # Lifting generators from the nilpotent abelianization

For the Cartan model, homogeneous lifts of a basis modulo the derived algebra
generate the whole nilpotent ideal. The proof pushes the error down its actual
lower central series; no generation hypothesis is substituted for this step.
-/

namespace PolycyclicRecognition

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Lie generation implies linear spanning modulo brackets. -/
theorem span_sup_lowerCentralSeries_one_of_lieSpan
    (S : Set L) (hS : LieSubalgebra.lieSpan ℝ L S = ⊤) :
    Submodule.span ℝ S ⊔ (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule = ⊤ := by
  let V := Submodule.span ℝ S ⊔ (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule
  have hmem : ∀ x ∈ LieSubalgebra.lieSpan ℝ L S, x ∈ V := by
    intro x hx
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem x hx => exact Submodule.mem_sup_left (Submodule.subset_span hx)
    | zero => exact V.zero_mem
    | add x y _ _ hx hy => exact V.add_mem hx hy
    | smul r x _ hx => exact V.smul_mem r hx
    | lie x y _ _ _ _ =>
      apply Submodule.mem_sup_right
      change ⁅x, y⁆ ∈ LieModule.lowerCentralSeries ℝ L L (0 + 1)
      rw [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)
  apply top_unique
  intro x _
  exact hmem x (hS ▸ LieSubalgebra.mem_top x)

theorem lieSubalgebra_sup_lowerCentralSeries
    (U : LieSubalgebra ℝ L)
    (hU : U.toSubmodule ⊔ (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule = ⊤) :
    ∀ k, U.toSubmodule ⊔ (LieModule.lowerCentralSeries ℝ L L k).toSubmodule = ⊤ := by
  intro k
  induction k with
  | zero => simp
  | succ k hk =>
    let C := LieModule.lowerCentralSeries ℝ L L k
    let C' := LieModule.lowerCentralSeries ℝ L L (k + 1)
    let S := U.toSubmodule ⊔ C'.toSubmodule
    have hright (x y : L) (hy : y ∈ C) : ⁅x, y⁆ ∈ C' := by
      change ⁅x, y⁆ ∈ LieModule.lowerCentralSeries ℝ L L (k + 1)
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hy
    have hbracket (x y : L) : ⁅x, y⁆ ∈ S := by
      have hx : x ∈ U.toSubmodule ⊔ C.toSubmodule := by rw [hk]; trivial
      have hy : y ∈ U.toSubmodule ⊔ C.toSubmodule := by rw [hk]; trivial
      obtain ⟨u, hu, a, ha, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨v, hv, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
      rw [add_lie, lie_add, lie_add]
      apply S.add_mem
      · exact S.add_mem (Submodule.mem_sup_left (U.lie_mem hu hv))
          (Submodule.mem_sup_right (hright u b hb))
      · apply S.add_mem
        · rw [← lie_skew]
          exact Submodule.mem_sup_right (C'.neg_mem (hright v a ha))
        · exact Submodule.mem_sup_right (hright a b hb)
    have hC : (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule ≤ S := by
      rw [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero,
        LieSubmodule.lieIdeal_oper_eq_linear_span']
      apply Submodule.span_le.mpr
      rintro _ ⟨x, _, y, _, rfl⟩
      exact hbracket x y
    apply top_unique
    rw [← hU]
    exact sup_le le_sup_left hC

/-- Lifts spanning the abelianization generate a nilpotent Lie algebra. -/
theorem lieSubalgebra_eq_top_of_sup_lowerCentralSeries_one
    [LieRing.IsNilpotent L] (U : LieSubalgebra ℝ L)
    (hU : U.toSubmodule ⊔ (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule = ⊤) :
    U = ⊤ := by
  obtain ⟨k, hk⟩ := LieModule.IsNilpotent.nilpotent ℝ L L
  have h := lieSubalgebra_sup_lowerCentralSeries U hU k
  rw [hk, LieSubmodule.bot_toSubmodule, sup_bot_eq] at h
  exact SetLike.coe_injective (congrArg (fun V : Submodule ℝ L => (V : Set L)) h)

/-- The resulting generating family has a basis of evaluated bracket words. -/
theorem exists_bracketWord_basis_of_abelianization
    [LieRing.IsNilpotent L] [FiniteDimensional ℝ L]
    {I : Type*} (X : I → L)
    (hX : Submodule.span ℝ (Set.range X) ⊔
      (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ L)) ℝ L,
      ∀ k, ∃ w : FreeMagma I, evalBracketWord X w = b k := by
  apply exists_bracketWord_basis X
  apply lieSubalgebra_eq_top_of_sup_lowerCentralSeries_one
  apply top_unique
  rw [← hX]
  apply sup_le_sup_right
  exact Submodule.span_le.mpr LieSubalgebra.subset_lieSpan

end PolycyclicRecognition

end OAI
