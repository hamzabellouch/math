import OAI.Analysis.Unitarizability.EndpointAssignment
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace OAI

/-! Spectral norm bounds imply sparse endpoint assignments.
The input is a bounded convolution operator with its coefficient formula. -/
noncomputable section
namespace Dixmier
open Finset
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {G I : Type*} [Fintype I]

abbrev ScalarL2 (G : Type*) := lp (fun _ : G => ℂ) 2

def indicatorL2 (U : Finset G) : ScalarL2 G := ∑ x ∈ U, lp.single 2 x 1

@[simp] theorem indicatorL2_apply (U : Finset G) (x : G) :
    indicatorL2 U x = if x ∈ U then 1 else 0 := by
  change (∑ i ∈ U, lp.single 2 i (1 : ℂ)) x = _
  rw [lp.coeFn_sum]
  simp [Finset.sum_apply, lp.coeFn_single, Pi.single_apply]

theorem indicatorL2_norm_sq (U : Finset G) : ‖indicatorL2 U‖ ^ 2 = U.card := by
  have h := lp.norm_sum_single (p := 2) (by norm_num) (fun _ : G => (1 : ℂ)) U
  simpa [indicatorL2] using h

theorem indicatorL2_norm (U : Finset G) : ‖indicatorL2 U‖ = Real.sqrt U.card := by
  rw [← indicatorL2_norm_sq, Real.sqrt_sq (norm_nonneg _)]

variable [Group G]

def rectangleEdges (s : I → G) (U V : Finset G) : Finset (G × I) :=
  (U ×ˢ univ).filter fun e => e.1 * s e.2 ∈ V

/-- Pairing convolution with the two indicator vectors counts labelled edges. -/
theorem indicator_convolution_inner (s : I → G)
    (A : ScalarL2 G →L[ℂ] ScalarL2 G)
    (hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ i, ξ (x * s i))
    (U V : Finset G) :
    ⟪indicatorL2 U, A (indicatorL2 V)⟫_ℂ = (rectangleEdges s U V).card := by
  calc
    _ = ∑ x ∈ U, ∑ i, if x * s i ∈ V then (1 : ℂ) else 0 := by
      change ⟪∑ x ∈ U, lp.single 2 x (1 : ℂ), A (indicatorL2 V)⟫_ℂ = _
      simp only [sum_inner, lp.inner_single_left, hA, indicatorL2_apply]
      simp
    _ = (rectangleEdges s U V).card := by
      rw [Finset.card_eq_sum_ones]
      simp only [Nat.cast_sum, Nat.cast_one]
      rw [rectangleEdges, Finset.sum_filter, Finset.sum_product]

/-- The rectangular edge-count bound with all multiplicities retained. -/
theorem rectangleEdges_card_le (s : I → G)
    (A : ScalarL2 G →L[ℂ] ScalarL2 G)
    (hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ i, ξ (x * s i))
    {q : ℝ} (hq : ‖A‖ ≤ q) (U V : Finset G) :
    ((rectangleEdges s U V).card : ℝ) ≤ q * Real.sqrt ((U.card : ℝ) * V.card) := by
  have hq0 : 0 ≤ q := (norm_nonneg A).trans hq
  calc
    _ = ‖⟪indicatorL2 U, A (indicatorL2 V)⟫_ℂ‖ := by
      rw [indicator_convolution_inner s A hA]
      simp
    _ ≤ ‖indicatorL2 U‖ * ‖A (indicatorL2 V)‖ := norm_inner_le_norm _ _
    _ ≤ ‖indicatorL2 U‖ * (q * ‖indicatorL2 V‖) :=
      mul_le_mul_of_nonneg_left ((A.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hq (norm_nonneg _))) (norm_nonneg _)
    _ = q * Real.sqrt ((U.card : ℝ) * V.card) := by
      rw [indicatorL2_norm, indicatorL2_norm, Real.sqrt_mul (Nat.cast_nonneg _)]
      ring

/-- Every finite edge family lies in the rectangle of its endpoints. -/
theorem edges_subset_endpoint_rectangle (s : I → G) (F : Finset (G × I)) :
    F ⊆ rectangleEdges s (F.image Prod.fst) (F.image fun e => e.1 * s e.2) := by
  intro e he
  simp only [rectangleEdges, mem_filter, mem_product, mem_univ, and_true]
  exact ⟨mem_image.mpr ⟨e, he, rfl⟩, mem_image.mpr ⟨e, he, rfl⟩⟩

/-- Arithmetic used in the Hall argument, including its factor one half. -/
theorem sqrt_mul_le_half_add {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u * v) ≤ (u + v) / 2 := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [sq_nonneg (u - v)]

/-- The finite Hall density follows from the rectangular spectral estimate. -/
theorem endpoint_density_of_rectangle_bound (s : I → G) {q : ℝ} {r : ℕ}
    (hq : 0 ≤ q) (hqr : q ≤ r)
    (hrect : ∀ U V : Finset G, ((rectangleEdges s U V).card : ℝ) ≤
      q * Real.sqrt ((U.card : ℝ) * V.card))
    (F : Finset (G × I)) :
    F.card ≤ r * ((F.image Prod.fst).card + (F.image fun e => e.1 * s e.2).card) := by
  let U := F.image Prod.fst
  let V := F.image fun e => e.1 * s e.2
  have he : (F.card : ℝ) ≤ (rectangleEdges s U V).card := by
    exact_mod_cast card_le_card (edges_subset_endpoint_rectangle s F)
  have hsum : (0 : ℝ) ≤ (U.card : ℝ) + V.card := by positivity
  have hhalf : ((U.card : ℝ) + V.card) / 2 ≤ (U.card : ℝ) + V.card := by linarith
  have h : (F.card : ℝ) ≤ (r : ℝ) * ((U.card : ℝ) + V.card) := calc
    _ ≤ q * Real.sqrt ((U.card : ℝ) * V.card) := he.trans (hrect U V)
    _ ≤ q * (((U.card : ℝ) + V.card) / 2) :=
      mul_le_mul_of_nonneg_left (sqrt_mul_le_half_add (by positivity) (by positivity)) hq
    _ ≤ q * ((U.card : ℝ) + V.card) := mul_le_mul_of_nonneg_left hhalf hq
    _ ≤ (r : ℝ) * ((U.card : ℝ) + V.card) := mul_le_mul_of_nonneg_right hqr hsum
  exact_mod_cast h

/-- Sparse assignment from a bounded convolution operator, at any integer
capacity above its norm. -/
theorem sparse_mask_of_convolution_bound (s : I → G)
    (A : ScalarL2 G →L[ℂ] ScalarL2 G)
    (hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ i, ξ (x * s i))
    {r : ℕ} (hr : ‖A‖ ≤ r) :
    ∃ a : G → I → Bool, (∀ x, (rowOnes a x).card ≤ r) ∧
      ∀ y, (columnZeros a s y).card ≤ r := by
  apply exists_sparse_mask
  exact endpoint_density_of_rectangle_bound s (norm_nonneg A) hr
    (rectangleEdges_card_le s A hA le_rfl)

end Dixmier

end

end OAI
