import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
namespace YauCounterexamples

def gridPoint (d m : ℕ) (δ : ℝ) (k : Fin d → Fin (2 * m + 1)) : Fin d → ℝ :=
  fun j => δ * ((k j : ℕ) - (m : ℝ))

theorem gridPoint_cover (d m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (x : Fin d → ℝ) (hx : ‖x‖ ≤ (m : ℝ) * δ) :
    ∃ k : Fin d → Fin (2 * m + 1), dist x (gridPoint d m δ k) ≤ δ := by
  have hcoord (j : Fin d) : |x j| ≤ (m : ℝ) * δ :=
    (norm_le_pi_norm x j).trans hx
  have hy0 (j : Fin d) : 0 ≤ x j / δ + (m : ℝ) := by
    have hh : -(m : ℝ) ≤ x j / δ :=
      (le_div_iff₀ hδ).mpr (by nlinarith [(abs_le.mp (hcoord j)).1])
    linarith
  have hy2 (j : Fin d) : x j / δ + (m : ℝ) ≤ (2 * m : ℕ) := by
    have h := (abs_le.mp (hcoord j)).2
    have hh : x j / δ ≤ (m : ℝ) := (div_le_iff₀ hδ).mpr h
    push_cast
    linarith
  let k : Fin d → Fin (2 * m + 1) := fun j =>
    ⟨⌊x j / δ + (m : ℝ)⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le (hy2 j))⟩
  refine ⟨k, ?_⟩
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
  intro j
  change |x j - δ * ((⌊x j / δ + (m : ℝ)⌋₊ : ℝ) - m)| ≤ δ
  have h := Nat.abs_sub_floor_le (hy0 j)
  have heq : x j - δ * ((⌊x j / δ + (m : ℝ)⌋₊ : ℝ) - m) =
      δ * (x j / δ + m - ⌊x j / δ + (m : ℝ)⌋₊) := by field_simp; ring
  rw [heq, abs_mul, abs_of_pos hδ]
  nlinarith

theorem gridPoint_card (d m : ℕ) :
    Fintype.card (Fin d → Fin (2 * m + 1)) = (2 * m + 1) ^ d := by simp

theorem recenter_finite_net {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    (p : I → X) (K : Set X) (δ : ℝ)
    (hcover : ∀ x ∈ K, ∃ i, dist x (p i) ≤ δ) :
    ∃ t : Finset X, (↑t : Set X) ⊆ K ∧ t.card ≤ Fintype.card I ∧
      ∀ x ∈ K, ∃ y ∈ t, dist x y ≤ 2 * δ := by
  classical
  let A : Set I := {i | ∃ x ∈ K, dist x (p i) ≤ δ}
  let : Fintype A := Fintype.ofFinite A
  let q : A → X := fun i => i.property.choose
  have hq (i : A) : q i ∈ K ∧ dist (q i) (p i) ≤ δ := i.property.choose_spec
  refine ⟨Finset.univ.image q, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (hq i).1
  · exact (Finset.card_image_le).trans (Fintype.card_le_of_injective (fun i : A => (i : I)) Subtype.val_injective)
  · intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    let j : A := ⟨i, x, hx, hi⟩
    refine ⟨q j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    calc
      dist x (q j) ≤ dist x (p i) + dist (p i) (q j) := dist_triangle _ _ _
      _ ≤ δ + δ := add_le_add hi (by simpa [dist_comm] using (hq j).2)
      _ = 2 * δ := by ring

theorem cube_subset_finite_net (d m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (K : Set (Fin d → ℝ)) (hK : ∀ x ∈ K, ‖x‖ ≤ (m : ℝ) * δ) :
    ∃ t : Finset (Fin d → ℝ), (↑t : Set (Fin d → ℝ)) ⊆ K ∧
      t.card ≤ (2 * m + 1) ^ d ∧
      ∀ x ∈ K, ∃ y ∈ t, dist x y ≤ 2 * δ := by
  simpa only [gridPoint_card] using recenter_finite_net (gridPoint d m δ) K δ
    (fun x hx => gridPoint_cover d m δ hδ x (hK x hx))

theorem norm_lower_of_net {X V I : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] (p : I → X) (K : Set X) (δ τ L : ℝ)
    (hcover : ∀ x ∈ K, ∃ i, dist x (p i) ≤ δ)
    (F : X → V) (hL : ∀ x ∈ K, ∀ i, ‖F x - F (p i)‖ ≤ L * dist x (p i))
    (hL0 : 0 ≤ L) (hlower : ∀ i, τ + L * δ ≤ ‖F (p i)‖) :
    ∀ x ∈ K, τ ≤ ‖F x‖ := by
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  have h := (hL x hx i).trans (mul_le_mul_of_nonneg_left hi hL0)
  have ht := norm_sub_norm_le (F (p i)) (F x)
  rw [norm_sub_rev] at ht
  linarith [hlower i]

end YauCounterexamples

end

end OAI
