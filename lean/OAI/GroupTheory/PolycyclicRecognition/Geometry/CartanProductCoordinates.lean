import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordLogarithms

namespace OAI

/-! # Coordinates of Cartan support positions

The actual product of a pivot and a scaled support direction has polynomial
logarithmic coordinates. This uses only the finite published Dynkin identity;
it does not identify multiplication with vector addition.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {ED D : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hbijD : Function.Bijective ExpD)

/-- Polynomial coordinates of the actual product of two Cartan exponentials. -/
theorem exists_cartan_mul_log_bound
    (hExpD : IsGroupExponential ExpD) (dynkinD : NilpotentDynkinExpansionInput ED D) :
    ∃ (C : ℝ) (c : ℕ), 0 ≤ C ∧ ∀ x y : H,
      ‖(finBasis ℝ H).equivFun
        (cartanLog H eD ExpD hbijD (ExpD (eD x) * ExpD (eD y)))‖ ≤
      C * (1 + ‖(finBasis ℝ H).equivFun x‖ + ‖(finBasis ℝ H).equivFun y‖) ^ c := by
  obtain ⟨c, hc⟩ := LieModule.IsNilpotent.nilpotent ℝ H H
  obtain ⟨K, hK, hbracket⟩ := exists_basis_structureConstant_bound (finBasis ℝ H)
  let C : ℝ := (c : ℝ) * 2 ^ c * (1 + (finrank ℝ H : ℝ) ^ 2 * K) ^ c * 3 ^ c
  refine ⟨C, c, by dsimp [C]; positivity, ?_⟩
  intro x y
  let R := ‖(finBasis ℝ H).equivFun x‖ + ‖(finBasis ℝ H).equivFun y‖
  have hR : 0 ≤ R := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hg (i : Fin 2) : (![ExpD (eD x), ExpD (eD y)] : Fin 2 → D) i ∈
      exponentialCoordinateBox (ExpD ∘ eD) (finBasis ℝ H) R := by
    fin_cases i
    · exact ⟨x, rfl, le_add_of_nonneg_right (norm_nonneg _)⟩
    · exact ⟨y, rfl, le_add_of_nonneg_left (norm_nonneg _)⟩
  obtain ⟨z, hz, hb⟩ := product_mem_exponentialCoordinateBox dynkinD eD ExpD hExpD hc
    (finBasis ℝ H) hK hR hbracket _ hg
  have hz' : ExpD (eD z) = ExpD (eD x) * ExpD (eD y) := by
    simpa [List.ofFn_succ] using hz
  rw [← hz', cartanLog_exp]
  calc
    _ ≤ (c : ℝ) * 2 ^ c * (1 + (finrank ℝ H : ℝ) ^ 2 * K) ^ c *
        (1 + R) ^ c * 3 ^ c := by
          simpa only [Fintype.card_fin, Nat.cast_ofNat,
            show (1 + (2 : ℝ)) = 3 by norm_num] using hb
    _ = _ := by dsimp [C, R]; ring

/-- A polynomially bounded pivot remains polynomially bounded after every
scaled support visit. The exponent and constant are uniform over the pivot. -/
theorem exists_cartan_scaled_mul_log_bound
    (hExpD : IsGroupExponential ExpD) (dynkinD : NilpotentDynkinExpansionInput ED D)
    {A V : ℝ} (hA : 0 ≤ A) (hV : 0 ≤ V) (p : ℕ) :
    ∃ (C : ℝ) (q : ℕ), 0 ≤ C ∧ ∀ (r : ℝ), 0 ≤ r → ∀ h v : H,
      ‖(finBasis ℝ H).equivFun h‖ ≤ A * (1 + r) ^ p →
      ‖(finBasis ℝ H).equivFun v‖ ≤ V →
      ‖(finBasis ℝ H).equivFun
        (cartanLog H eD ExpD hbijD (ExpD (eD h) * ExpD (eD (r • v))))‖ ≤
        C * (1 + r) ^ q := by
  obtain ⟨B, c, hB, hb⟩ := exists_cartan_mul_log_bound H eD ExpD hbijD hExpD dynkinD
  refine ⟨B * (1 + A + V) ^ c, (p + 1) * c, by positivity, ?_⟩
  intro r hr h v hh hv
  have hs : 1 ≤ 1 + r := by linarith
  have hp : 1 ≤ (1 + r) ^ p := one_le_pow₀ hs
  have hp' : 1 ≤ (1 + r) ^ (p + 1) := one_le_pow₀ hs
  have hpp : (1 + r) ^ p ≤ (1 + r) ^ (p + 1) := by
    rw [pow_succ]
    nlinarith [pow_nonneg (by linarith : 0 ≤ 1 + r) p]
  have hrp : r ≤ (1 + r) ^ (p + 1) := by rw [pow_succ]; nlinarith
  have hv' : ‖(finBasis ℝ H).equivFun (r • v)‖ ≤ V * (1 + r) ^ (p + 1) := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    calc
      r * ‖(finBasis ℝ H).equivFun v‖ ≤ r * V := mul_le_mul_of_nonneg_left hv hr
      _ ≤ V * (1 + r) ^ (p + 1) := by nlinarith
  have hh' : ‖(finBasis ℝ H).equivFun h‖ ≤ A * (1 + r) ^ (p + 1) :=
    hh.trans (mul_le_mul_of_nonneg_left hpp hA)
  have hsum : 1 + ‖(finBasis ℝ H).equivFun h‖ +
      ‖(finBasis ℝ H).equivFun (r • v)‖ ≤ (1 + A + V) * (1 + r) ^ (p + 1) := by
    nlinarith
  calc
    _ ≤ B * (1 + ‖(finBasis ℝ H).equivFun h‖ +
        ‖(finBasis ℝ H).equivFun (r • v)‖) ^ c := hb h (r • v)
    _ ≤ B * ((1 + A + V) * (1 + r) ^ (p + 1)) ^ c := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end PolycyclicRecognition

end

end OAI
