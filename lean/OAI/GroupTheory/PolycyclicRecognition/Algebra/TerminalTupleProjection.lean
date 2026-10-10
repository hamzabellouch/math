import OAI.GroupTheory.PolycyclicRecognition.Algebra.SourceBundleStates
import Mathlib.Topology.MetricSpace.Pseudo.Pi

namespace OAI

/-! # Projecting a thickened increment tuple at its terminal coordinate

The right correction to the Cartan lift is retained explicitly. This
identity does not require uniqueness of Cartan factorization.
-/

noncomputable section
namespace PolycyclicRecognition

open Metric
open Set

variable {N D G : Type*} [Group N] [Group D] [Group G]
  [MeasurableSpace N] [MeasurableMul₂ N] [MeasurableInv N]

theorem prefixCoordinateEquiv_terminal {h : ℕ} (hh : 0 < h)
    (u : Fin h → N) :
    prefixCoordinateEquiv h u ⟨h - 1, Nat.sub_lt hh (by decide)⟩ = (List.ofFn u).prod := by
  cases h with
  | zero => omega
  | succ h => simpa only [Fin.last, Nat.add_sub_cancel] using prefixCoordinateEquiv_last h u

theorem terminal_thickening_projection {h : ℕ}
    (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (u pN zN : Fin (h + 1) → N) (pD zD : Fin (h + 1) → D)
    (x : Fin (h + 1) → G)
    (hp : ∀ i, ι (pN i) * κ (pD i) = x i)
    (hu : prefixCoordinateEquiv (h + 1) u = fun i => pN i * φ (pD i) (zN i)) :
    ι (List.ofFn u).prod * κ (pD (Fin.last h) * zD (Fin.last h)) =
      x (Fin.last h) * (ι (zN (Fin.last h)) * κ (zD (Fin.last h))) := by
  rw [← prefixCoordinateEquiv_last h u, hu, map_mul, hconj, map_mul, ← hp]
  group

theorem terminal_thickening_dist {h : ℕ} [MetricSpace G] [IsIsometricSMul G G]
    (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (u pN zN : Fin (h + 1) → N) (pD zD : Fin (h + 1) → D)
    (x : Fin (h + 1) → G)
    (hp : ∀ i, ι (pN i) * κ (pD i) = x i)
    (hu : prefixCoordinateEquiv (h + 1) u = fun i => pN i * φ (pD i) (zN i))
    {ρ : ℝ} (hz : dist (1 : Fin (h + 1) → G) (fun i => ι (zN i) * κ (zD i)) < ρ) :
    dist (ι (List.ofFn u).prod * κ (pD (Fin.last h) * zD (Fin.last h))) (x (Fin.last h)) < ρ := by
  rw [terminal_thickening_projection ι κ φ hconj u pN zN pD zD x hp hu]
  have he := dist_mul_left (x (Fin.last h))
    (ι (zN (Fin.last h)) * κ (zD (Fin.last h))) 1
  rw [mul_one] at he
  rw [he, dist_comm]
  exact (dist_le_pi_dist (1 : Fin (h + 1) → G) (fun i => ι (zN i) * κ (zD i)) (Fin.last h)).trans_lt hz

theorem terminal_tuple_product_cover {h : ℕ} [MetricSpace G] [IsIsometricSMul G G]
    (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (s : Finset (Fin (h + 1) → G))
    (p : (Fin (h + 1) → G) → (Fin (h + 1) → N) × (Fin (h + 1) → D))
    (U : Set ((Fin (h + 1) → N) × (Fin (h + 1) → D)))
    (I : Set (Fin (h + 1) → N)) (C : Set N) (A : Set D) (t : Finset G)
    (hp : ∀ x ∈ s, ∀ i, ι ((p x).1 i) * κ ((p x).2 i) = x i)
    (hI : ∀ u ∈ I, ∃ x ∈ s, ∃ z ∈ U,
      prefixCoordinateEquiv (h + 1) u = fun i => (p x).1 i * φ ((p x).2 i) (z.1 i))
    {ρ R : ℝ}
    (hsmall : ∀ z ∈ U, dist (1 : Fin (h + 1) → G) (fun i => ι (z.1 i) * κ (z.2 i)) < ρ)
    (hA : ∀ x ∈ s, ∀ z ∈ U, (p x).2 (Fin.last h) * z.2 (Fin.last h) ∈ A)
    (hcover : ∀ x ∈ s, ∃ y ∈ t, dist (x (Fin.last h)) y ≤ R)
    (hC : C ⊆ (fun u : Fin (h + 1) → N => (List.ofFn u).prod) '' I) :
    ∀ u ∈ C, ∃ d ∈ A, ∃ y ∈ t, dist (ι u * κ d) y ≤ ρ + R := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := hC hu
  obtain ⟨x, hx, z, hz, he⟩ := hI v hv
  obtain ⟨y, hy, hxy⟩ := hcover x hx
  refine ⟨(p x).2 (Fin.last h) * z.2 (Fin.last h), hA x hx z hz, y, hy, ?_⟩
  calc
    _ ≤ dist (ι (List.ofFn v).prod * κ ((p x).2 (Fin.last h) * z.2 (Fin.last h)))
        (x (Fin.last h)) + dist (x (Fin.last h)) y := dist_triangle _ _ _
    _ ≤ ρ + R := add_le_add
      (terminal_thickening_dist ι κ φ hconj v (p x).1 z.1 (p x).2 z.2 x (hp x hx) he (hsmall z hz)).le hxy

/-- The terminal-cover statement for an arbitrary positive tuple length,
including the even length of a chronological alternating product. -/
theorem terminal_tuple_product_cover_pos {h : ℕ} (hh : 0 < h)
    [MetricSpace G] [IsIsometricSMul G G]
    (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
    (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (s : Finset (Fin h → G))
    (p : (Fin h → G) → (Fin h → N) × (Fin h → D))
    (U : Set ((Fin h → N) × (Fin h → D)))
    (I : Set (Fin h → N)) (C : Set N) (A : Set D) (t : Finset G)
    (hp : ∀ x ∈ s, ∀ i, ι ((p x).1 i) * κ ((p x).2 i) = x i)
    (hI : ∀ u ∈ I, ∃ x ∈ s, ∃ z ∈ U,
      prefixCoordinateEquiv h u = fun i => (p x).1 i * φ ((p x).2 i) (z.1 i))
    {ρ R : ℝ}
    (hsmall : ∀ z ∈ U, dist (1 : Fin h → G) (fun i => ι (z.1 i) * κ (z.2 i)) < ρ)
    (hA : ∀ x ∈ s, ∀ z ∈ U,
      (p x).2 ⟨h - 1, Nat.sub_lt hh (by decide)⟩ *
        z.2 ⟨h - 1, Nat.sub_lt hh (by decide)⟩ ∈ A)
    (hcover : ∀ x ∈ s, ∃ y ∈ t,
      dist (x ⟨h - 1, Nat.sub_lt hh (by decide)⟩) y ≤ R)
    (hC : C ⊆ (fun u : Fin h → N => (List.ofFn u).prod) '' I) :
    ∀ u ∈ C, ∃ d ∈ A, ∃ y ∈ t, dist (ι u * κ d) y ≤ ρ + R := by
  cases h with
  | zero => omega
  | succ h =>
    exact terminal_tuple_product_cover ι κ φ hconj s p U I C A t hp hI hsmall hA hcover hC

end PolycyclicRecognition

end

end OAI
