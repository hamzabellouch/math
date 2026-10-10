import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Normal graphs from projection cones

A cone estimate makes tangential projection injective on a set. Its inverse supplies
the normal component of a Lipschitz graph over the projected set.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem projection_cone_injOn {d : ℕ} (P : Submodule ℝ (Ambient d))
    (A : Set (Ambient d)) (L : ℝ)
    (hcone : ∀ x ∈ A, ∀ y ∈ A,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        L * dist (P.starProjection x) (P.starProjection y)) :
    Set.InjOn P.starProjection A := by
  intro x hx y hy hxy
  have hp : P.starProjection (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h := hcone x hx y hy
  rw [hxy, dist_self, mul_zero] at h
  have hq : (Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y) = 0 :=
    norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hd := P.starProjection_add_starProjection_orthogonal (x - y)
  rw [hp, hq, zero_add] at hd
  exact sub_eq_zero.mp hd.symm

theorem exists_normal_graph_of_projection_cone {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (A : Set (Ambient d)) (L : ℝ) (hL : 0 ≤ L)
    (hcone : ∀ x ∈ A, ∀ y ∈ A,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        L * dist (P.starProjection x) (P.starProjection y)) :
    ∃ g : (P.starProjection '' A) → Ambient d,
      LipschitzWith (Real.toNNReal L) g ∧
      (∀ u, g u ∈ (Pᗮ : Submodule ℝ (Ambient d))) ∧
      A = Set.range (fun u : P.starProjection '' A => u.val + g u) := by
  classical
  have hex (u : P.starProjection '' A) : ∃ x ∈ A, P.starProjection x = u.val := u.property
  choose a ha hpa using hex
  let g : (P.starProjection '' A) → Ambient d :=
    fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (a u)
  have hgraph (u : P.starProjection '' A) : u.val + g u = a u := by
    rw [← hpa u]
    exact P.starProjection_add_starProjection_orthogonal (a u)
  refine ⟨g, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [Real.coe_toNNReal _ hL]
    change dist ((Pᗮ : Submodule ℝ (Ambient d)).starProjection (a u))
      ((Pᗮ : Submodule ℝ (Ambient d)).starProjection (a v)) ≤ L * dist u v
    rw [dist_eq_norm, ← map_sub]
    have h := hcone (a u) (ha u) (a v) (ha v)
    rw [hpa u, hpa v] at h
    exact h
  · intro u
    exact ((Pᗮ : Submodule ℝ (Ambient d)).orthogonalProjectionOnto (a u)).property
  · ext x
    constructor
    · intro hx
      let u : P.starProjection '' A := ⟨P.starProjection x, ⟨x, hx, rfl⟩⟩
      refine ⟨u, ?_⟩
      calc
        _ = a u := hgraph u
        _ = x := projection_cone_injOn P A L hcone (ha u) hx (hpa u)
    · rintro ⟨u, rfl⟩
      change u.val + g u ∈ A
      rw [hgraph u]
      exact ha u

end

end RieszRectifiability

end OAI
