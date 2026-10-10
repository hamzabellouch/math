import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith

namespace OAI

namespace MarkovSuperreflexivity

universe u v w

def FinitelyRepresentable (Y : Type v) (X : Type u)
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (E : Submodule ℝ Y) [FiniteDimensional ℝ E] (η : ℝ), 0 < η →
    ∃ T : E →ₗ[ℝ] X, ∀ z : E,
      ‖z‖ ≤ ‖T z‖ ∧ ‖T z‖ ≤ (1 + η) * ‖z‖

def CanonicallyReflexive (X : Type u)
    [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)

namespace FinitelyRepresentable

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem refl (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    FinitelyRepresentable X X := by
  intro E hE η hη
  refine ⟨E.subtype, ?_⟩
  intro z
  change ‖z‖ ≤ ‖z‖ ∧ ‖z‖ ≤ (1 + η) * ‖z‖
  constructor
  · exact le_rfl
  · nlinarith [norm_nonneg z]

theorem of_subsingleton [Subsingleton Y] : FinitelyRepresentable Y X := by
  intro E hE η hη
  refine ⟨0, ?_⟩
  intro z
  have hz : z = 0 := Subsingleton.elim _ _
  simp [hz]

theorem target_linearIsometry (h : FinitelyRepresentable Y X)
    (f : X →ₗᵢ[ℝ] Z) : FinitelyRepresentable Y Z := by
  intro E hE η hη
  obtain ⟨T, hT⟩ := h E η hη
  refine ⟨f.toLinearMap.comp T, ?_⟩
  intro z
  simpa only [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap,
    LinearIsometry.norm_map] using hT z

theorem injective_of_lower_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →ₗ[ℝ] X) (hT : ∀ z, ‖z‖ ≤ ‖T z‖) : Function.Injective T := by
  intro x y hxy
  have hzero : T (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hnorm : ‖x - y‖ ≤ 0 := by simpa only [hzero, norm_zero] using hT (x - y)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hnorm)

theorem compose_bounds {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →ₗ[ℝ] X) (S : X →ₗ[ℝ] Z) {a b : ℝ}
    (hb : 0 ≤ b)
    (hT : ∀ z, ‖z‖ ≤ ‖T z‖ ∧ ‖T z‖ ≤ a * ‖z‖)
    (hS : ∀ x, ‖x‖ ≤ ‖S x‖ ∧ ‖S x‖ ≤ b * ‖x‖) :
    ∀ z, ‖z‖ ≤ ‖(S.comp T) z‖ ∧
      ‖(S.comp T) z‖ ≤ (b * a) * ‖z‖ := by
  intro z
  constructor
  · exact (hT z).1.trans (hS (T z)).1
  · calc
      ‖(S.comp T) z‖ ≤ b * ‖T z‖ := (hS (T z)).2
      _ ≤ b * (a * ‖z‖) := mul_le_mul_of_nonneg_left (hT z).2 hb
      _ = (b * a) * ‖z‖ := (mul_assoc b a ‖z‖).symm

theorem trans (hYX : FinitelyRepresentable Y X)
    (hXZ : FinitelyRepresentable X Z) : FinitelyRepresentable Y Z := by
  intro E hE η hη
  let δ : ℝ := min (η / 3) 1
  have hδ : 0 < δ := lt_min (by linarith) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδη : δ ≤ η / 3 := min_le_left _ _
  have hfactor : (1 + δ) * (1 + δ) ≤ 1 + η := by
    have hsquare : δ * δ ≤ δ := by nlinarith
    nlinarith
  obtain ⟨T, hT⟩ := hYX E δ hδ
  let R : Submodule ℝ X := LinearMap.range T
  let : FiniteDimensional ℝ R := LinearMap.finiteDimensional_range T
  obtain ⟨S, hS⟩ := hXZ R δ hδ
  refine ⟨S.comp T.rangeRestrict, ?_⟩
  intro z
  have hnorm : ‖T.rangeRestrict z‖ = ‖T z‖ := rfl
  constructor
  · calc
      ‖z‖ ≤ ‖T z‖ := (hT z).1
      _ = ‖T.rangeRestrict z‖ := hnorm.symm
      _ ≤ ‖(S.comp T.rangeRestrict) z‖ := (hS (T.rangeRestrict z)).1
  · calc
      ‖(S.comp T.rangeRestrict) z‖ ≤ (1 + δ) * ‖T.rangeRestrict z‖ :=
        (hS (T.rangeRestrict z)).2
      _ = (1 + δ) * ‖T z‖ := by rw [hnorm]
      _ ≤ (1 + δ) * ((1 + δ) * ‖z‖) :=
        mul_le_mul_of_nonneg_left (hT z).2 (by linarith)
      _ = ((1 + δ) * (1 + δ)) * ‖z‖ := (mul_assoc _ _ _).symm
      _ ≤ (1 + η) * ‖z‖ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg z)

end FinitelyRepresentable

end MarkovSuperreflexivity

end OAI
