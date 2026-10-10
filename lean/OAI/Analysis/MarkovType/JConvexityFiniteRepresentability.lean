import OAI.Analysis.MarkovType.JConvexityBasic
import OAI.Analysis.MarkovType.FinitelyRepresentable
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.Positivity

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem JConvexWitness.finitelyRepresentable {n : ℕ} {δ : ℝ}
    (h : JConvexWitness (normSeminorm ℝ X) n δ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hYX : FinitelyRepresentable Y X) :
    JConvexWitness (normSeminorm ℝ Y) n (δ / 2) := by
  classical
  intro x hx
  let E : Submodule ℝ Y := Submodule.span ℝ (Set.range x)
  let : FiniteDimensional ℝ E :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range x)
  let z : Fin n → E := fun i => ⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hz (i : Fin n) : ‖z i‖ ≤ 1 := hx i
  let c : ℝ := 1 + δ / 2
  have hc : 0 < c := by dsimp [c]; linarith
  obtain ⟨T, hT⟩ := hYX E (δ / 2) (by positivity)
  let y : Fin n → X := fun i => c⁻¹ • T (z i)
  have hy (i : Fin n) : ‖y i‖ ≤ 1 := by
    change ‖c⁻¹ • T (z i)‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    calc
      c⁻¹ * ‖T (z i)‖ ≤ c⁻¹ * (c * ‖z i‖) :=
        mul_le_mul_of_nonneg_left (hT (z i)).2 (inv_nonneg.mpr hc.le)
      _ = ‖z i‖ := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ 1 := hz i
  obtain ⟨r, hr⟩ := h y hy
  have hsub : E.subtype (cutSum z r) = cutSum x r := by
    have hmap := map_cutSum E.subtype z r
    change E.subtype (cutSum z r) = cutSum x r at hmap
    exact hmap
  have hsum : T (cutSum z r) = c • cutSum y r := by
    rw [map_cutSum]
    dsimp only [y]
    rw [cutSum_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hnorm : ‖cutSum x r‖ ≤ c * ‖cutSum y r‖ := by
    calc
      ‖cutSum x r‖ = ‖cutSum z r‖ := by rw [← hsub]; rfl
      _ ≤ ‖T (cutSum z r)‖ := (hT (cutSum z r)).1
      _ = c * ‖cutSum y r‖ := by
        rw [hsum, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hfactor : c * (1 - δ) ≤ 1 - δ / 2 := by
    dsimp only [c]
    nlinarith [sq_nonneg δ]
  refine ⟨r, ?_⟩
  change ‖cutSum x r‖ ≤ (n : ℝ) * (1 - δ / 2)
  calc
    ‖cutSum x r‖ ≤ c * ‖cutSum y r‖ := hnorm
    _ ≤ c * ((n : ℝ) * (1 - δ)) := mul_le_mul_of_nonneg_left hr hc.le
    _ = (n : ℝ) * (c * (1 - δ)) := by ring
    _ ≤ (n : ℝ) * (1 - δ / 2) :=
      mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg n)

theorem AmbientJConvex.finitelyRepresentable (hX : AmbientJConvex X)
    (hYX : FinitelyRepresentable Y X) : AmbientJConvex Y := by
  obtain ⟨n, hn, δ, hδ, hδ1, h⟩ := hX
  exact ⟨n, hn, δ / 2, by positivity, by linarith,
    h.finitelyRepresentable hδ hδ1 hYX⟩

end MarkovSuperreflexivity

end

end OAI
