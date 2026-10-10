import OAI.Geometry.RCD.Coordinates.ChartTopology
import OAI.Geometry.RCD.Coordinates.TaylorControl

namespace OAI

/-!
# From finite-scale Taylor estimates to the limiting chart

Geometric increments, derivative bounds on scale-selected value-space
segments, and linear separation give two-sided distance bounds for the
limit. Euclidean invariance of domain gives its open image, as in
Hatcher, *Algebraic Topology* (2002), Theorem 2B.3.
-/

open Set Filter
open scoped Topology

namespace RegularPointCoordinates

private theorem quarter_scale_arithmetic {q t v : ℝ} (hq : 1 ≤ q)
    (ht : 0 ≤ t)
    (hl : ((2 * q)⁻¹ - (8 * q)⁻¹ - (8 * q)⁻¹) * t ≤ v)
    (hu : v ≤ (2 * q + (8 * q)⁻¹ + (8 * q)⁻¹) * t) :
    (4 * q)⁻¹ * t ≤ v ∧ v ≤ (4 * q) * t := by
  have heq : (2 * q)⁻¹ - (8 * q)⁻¹ - (8 * q)⁻¹ = (4 * q)⁻¹ := by
    field_simp; ring
  have hinv : (8 * q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hcoeff : 2 * q + (8 * q)⁻¹ + (8 * q)⁻¹ ≤ 4 * q := by
    linarith
  exact ⟨heq ▸ hl, hu.trans (mul_le_mul_of_nonneg_right hcoeff ht)⟩

/-- The all-pairs metric conclusion from scale-selected Taylor estimates
and a geometric increment bound. All source distances are ambient ones. -/
theorem exists_limit_dist_bounds_of_taylor
    {X : Type*} [MetricSpace X] {n : ℕ}
    (u : X → Euclidean n) (h : ℕ → Euclidean n → Euclidean n)
    (dh : ℕ → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (ddh : ℕ → Euclidean n → Euclidean n →L[ℝ]
      (Euclidean n →L[ℝ] Euclidean n))
    {q C : ℝ} (hq : 1 ≤ q)
    (hstep : ∀ i x, dist (h i (u x)) (h (i + 1) (u x)) ≤ C * (1 / 2 : ℝ) ^ i)
    (hpairs : ∀ x z : X, x ≠ z → ∃ i M,
      0 ≤ M ∧
      (∀ y ∈ segment ℝ (u x) (u z), HasFDerivAt (h i) (dh i y) y) ∧
      (∀ y ∈ segment ℝ (u x) (u z), HasFDerivAt (dh i) (ddh i y) y) ∧
      (∀ y ∈ segment ℝ (u x) (u z), ‖ddh i y (u z - u x) (u z - u x)‖ ≤ M) ∧
      (2 * q)⁻¹ * dist x z ≤ ‖dh i (u x) (u z - u x)‖ ∧
      ‖dh i (u x) (u z - u x)‖ ≤ (2 * q) * dist x z ∧
      M ≤ (8 * q)⁻¹ * dist x z ∧
      4 * C * (1 / 2 : ℝ) ^ i ≤ (8 * q)⁻¹ * dist x z) :
    ∃ F : X → Euclidean n,
      (∀ x, Tendsto (fun i => h i (u x)) atTop (𝓝 (F x))) ∧
      ∀ x z, (4 * q)⁻¹ * dist x z ≤ dist (F x) (F z) ∧
        dist (F x) (F z) ≤ (4 * q) * dist x z := by
  obtain ⟨F, hlim, htail⟩ := exists_limit_of_geometric_step
    (by norm_num : (1 / 2 : ℝ) < 1) hstep
  refine ⟨F, hlim, ?_⟩
  intro x z
  by_cases hxz : x = z
  · subst z
    simp
  obtain ⟨i, M, hM, hd, hdd, hnorm, hl, hu, hrem, ht⟩ := hpairs x z hxz
  have happrox := dist_bounds_of_directional_taylor hM hd hdd hnorm hl hu hrem
  rw [dist_comm (h i (u z)) (h i (u x))] at happrox
  have htailx : dist (F x) (h i (u x)) ≤ 2 * C * (1 / 2 : ℝ) ^ i := by
    have hh := htail i x
    rw [dist_comm] at hh
    norm_num at hh ⊢
    nlinarith
  have htailz : dist (F z) (h i (u z)) ≤ 2 * C * (1 / 2 : ℝ) ^ i := by
    have hh := htail i z
    rw [dist_comm] at hh
    norm_num at hh ⊢
    nlinarith
  have herror : dist (F x) (h i (u x)) + dist (F z) (h i (u z)) ≤
      (8 * q)⁻¹ * dist x z := by linarith
  have hbound := dist_bounds_of_approximation
    (f := fun x => h i (u x)) (F := F) x z happrox.1 happrox.2 herror
  apply quarter_scale_arithmetic hq dist_nonneg
  · exact hbound.1
  · exact hbound.2

/-- Scale-selected Taylor bounds and geometric increment estimates give an open
bi-Lipschitz chart by Euclidean invariance of domain. -/
theorem hasOpenBilipschitzChart_of_taylor_data
    {X : Type*} [MetricSpace X] {n : ℕ} {p : X}
    (hIOD : EuclideanInvarianceOfDomain n)
    {U : Set X} (hU : IsOpen U) (hp : p ∈ U)
    {O : Set (Euclidean n)} (hO : IsOpen O) (u : U ≃ₜ O)
    (h : ℕ → Euclidean n → Euclidean n)
    (dh : ℕ → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (ddh : ℕ → Euclidean n → Euclidean n →L[ℝ]
      (Euclidean n →L[ℝ] Euclidean n))
    {q C : ℝ} (hq : 1 ≤ q)
    (hstep : ∀ i (x : U),
      dist (h i (u x)) (h (i + 1) (u x)) ≤ C * (1 / 2 : ℝ) ^ i)
    (hpairs : ∀ x z : U, x ≠ z → ∃ i M,
      0 ≤ M ∧
      (∀ y ∈ segment ℝ (u x : Euclidean n) (u z : Euclidean n),
        HasFDerivAt (h i) (dh i y) y) ∧
      (∀ y ∈ segment ℝ (u x : Euclidean n) (u z : Euclidean n),
        HasFDerivAt (dh i) (ddh i y) y) ∧
      (∀ y ∈ segment ℝ (u x : Euclidean n) (u z : Euclidean n),
        ‖ddh i y ((u z : Euclidean n) - u x) ((u z : Euclidean n) - u x)‖ ≤ M) ∧
      (2 * q)⁻¹ * dist x z ≤ ‖dh i (u x) ((u z : Euclidean n) - u x)‖ ∧
      ‖dh i (u x) ((u z : Euclidean n) - u x)‖ ≤ (2 * q) * dist x z ∧
      M ≤ (8 * q)⁻¹ * dist x z ∧
      4 * C * (1 / 2 : ℝ) ^ i ≤ (8 * q)⁻¹ * dist x z) :
    HasOpenBilipschitzChart n p := by
  obtain ⟨F, _, hF⟩ := exists_limit_dist_bounds_of_taylor
    (fun x : U => (u x : Euclidean n)) h dh ddh hq hstep hpairs
  exact hasOpenBilipschitzChart_of_coordinates_and_bounds hIOD hU hp hO u
    (by linarith : 1 ≤ 4 * q) hF

end RegularPointCoordinates

end OAI
