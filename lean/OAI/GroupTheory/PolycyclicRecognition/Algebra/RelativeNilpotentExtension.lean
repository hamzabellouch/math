import OAI.GroupTheory.PolycyclicRecognition.Algebra.RelativeCommutatorSeries
import Mathlib.GroupTheory.GroupExtension.Basic

namespace OAI

/-! # Nilpotence from a terminating relative kernel series -/

namespace PolycyclicRecognition
open scoped commutatorElement IsMulCommutative
variable {N G Q : Type} [Group N] [Group G] [Group Q] [IsMulCommutative Q]

theorem nilpotent_of_relative_kernel_series (E : GroupExtension N G Q)
    (c : ℕ) (hc : relativeCommutatorSeries ⊤ E.inl.range c = ⊥) :
    Group.IsNilpotent G := by
  have hbase : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ E.inl.range := by
    rw [E.range_inl_eq_ker_rightHom, Subgroup.lowerCentralSeries_succ,
      Subgroup.lowerCentralSeries_zero]
    apply Subgroup.commutator_le.mpr
    intro g _ h _
    change E.rightHom ⁅g, h⁆ = 1
    simp only [commutatorElement_def, map_mul, map_inv]
    rw [mul_comm (E.rightHom g) (E.rightHom h)]
    group
  have hbound (n : ℕ) : (⊤ : Subgroup G).lowerCentralSeries (n + 1) ≤
      relativeCommutatorSeries ⊤ E.inl.range n := by
    induction n with
    | zero => exact hbase
    | succ n ih =>
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
      exact Subgroup.commutator_mono_right ih
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  exact ⟨c + 1, eq_bot_iff.mpr (hc ▸ hbound c)⟩

theorem relative_series_descends_finite_layers {H : Type} [Group H]
    (K : Subgroup H) (F : ℕ → Subgroup H)
    (hstep : ∀ i, ∃ c, relativeCommutatorSeries K (F i) c ≤ F (i + 1)) (k : ℕ) :
    ∃ c, relativeCommutatorSeries K (F 0) c ≤ F k := by
  induction k with
  | zero => exact ⟨0, le_rfl⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := hstep k
    refine ⟨a + b, ?_⟩
    rw [relativeCommutatorSeries_add]
    exact (relativeCommutatorSeries_mono K ha b).trans hb

end PolycyclicRecognition

end OAI
