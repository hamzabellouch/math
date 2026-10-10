import OAI.Geometry.IsometricImmersion.Calculus.MixedCoordinateCalculus

namespace OAI

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace SmoothLocal.Geometry
open SmoothLocal.HighEquation

theorem coordinate_basis_decomposition (v : Coord) :
    v = ∑ i : Fin 2, v i • (Pi.single i (1 : ℝ) : Coord) := by
  ext j
  simp [Pi.single_apply, Finset.sum_apply, smul_eq_mul]

theorem multilinear_coordinate_components {n : ℕ}
    (L : Coord [×n]→L[ℝ] ℝ) (v : Fin n → Coord) :
    L v = ∑ r : Fin n → Fin 2,
      L (fun i => Pi.single (r i) (1 : ℝ)) * ∏ i, v i (r i) := by
  classical
  calc
    L v = L (fun i => ∑ j : Fin 2, v i j • (Pi.single j (1 : ℝ) : Coord)) := by
      congr 1
      funext i
      exact coordinate_basis_decomposition (v i)
    _ = ∑ r : Fin n → Fin 2, L (fun i => v i (r i) • Pi.single (r i) (1 : ℝ)) :=
      L.map_sum (fun i j => v i j • (Pi.single j (1 : ℝ) : Coord))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [L.map_smul_univ]
      simp only [smul_eq_mul, mul_comm]

theorem multilinear_norm_le_coordinate_bound {n : ℕ}
    (L : Coord [×n]→L[ℝ] ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hL : ∀ r : Fin n → Fin 2, ‖L (fun i => Pi.single (r i) (1 : ℝ))‖ ≤ B) :
    ‖L‖ ≤ (2 : ℝ)^n * B := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hB)
  intro v
  rw [multilinear_coordinate_components]
  calc
    _ ≤ ∑ r : Fin n → Fin 2, ‖L (fun i => Pi.single (r i) (1 : ℝ)) * ∏ i, v i (r i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r : Fin n → Fin 2, B * ∏ i, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul, norm_prod]
      apply mul_le_mul (hL r) _ (by positivity) hB
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => norm_le_pi_norm (v i) (r i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

theorem full_jet_norm_le_coordinate_words {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hword : ∀ ds : List (Fin 2), ds.length = n → |iteratedCoordPartial ds f p| ≤ B) :
    ‖iteratedFDeriv ℝ n f p‖ ≤ (2 : ℝ)^n * B := by
  apply multilinear_norm_le_coordinate_bound _ hB
  intro r
  rw [fullJet_coordinate_inputs_eq_ordered hf hU n r hp, Real.norm_eq_abs]
  exact hword (List.ofFn r) (by simp)

theorem CoordinateBound.full_jet_norm_bound {f : Coord → ℝ} {U S : Set Coord}
    {N n : ℕ} {B : ℝ} (h : CoordinateBound f S N B)
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hSU : S ⊆ U) (hB : 0 ≤ B)
    (hn : n ≤ N) {p : Coord} (hp : p ∈ S) :
    ‖iteratedFDeriv ℝ n f p‖ ≤ (2 : ℝ)^n * B := by
  apply full_jet_norm_le_coordinate_words hf hU (hSU hp) n hB
  intro ds hds
  exact h ds (by omega) p hp

end SmoothLocal.Geometry

end

end OAI
