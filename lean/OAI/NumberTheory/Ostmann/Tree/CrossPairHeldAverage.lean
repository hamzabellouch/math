import OAI.NumberTheory.Ostmann.Characters.SquareRatioCoefficient

namespace OAI

/-! # Averaging the two held leaves in a cross-pair quartet -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance crossHeldFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem sum_square_coset_pair_le_four {p : ℕ} [Fact p.Prime]
    (K L : (ZMod p)ˣ) (f : (ZMod p)ˣ → (ZMod p)ˣ → ℝ)
    (hf : ∀ z t, 0 ≤ f z t) :
    (∑ a : (ZMod p)ˣ, ∑ b : (ZMod p)ˣ, f (K * a ^ 2) (L * b ^ 2)) ≤
      4 * ∑ z : (ZMod p)ˣ, ∑ t : (ZMod p)ˣ, f z t := by
  calc
    _ ≤ ∑ a : (ZMod p)ˣ, 2 * ∑ t : (ZMod p)ˣ, f (K * a ^ 2) t :=
      Finset.sum_le_sum fun a _ => sum_square_coset_le_twice L _ (hf _)
    _ = 2 * ∑ a : (ZMod p)ˣ, ∑ t : (ZMod p)ˣ, f (K * a ^ 2) t := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (2 * ∑ z : (ZMod p)ˣ, ∑ t : (ZMod p)ˣ, f z t) :=
      mul_le_mul_of_nonneg_left
        (sum_square_coset_le_twice K _ (fun z => Finset.sum_nonneg fun t _ => hf z t))
        (by norm_num)
    _ = _ := by ring

theorem crossPairMajorant_parameter_average {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y : ZMod p) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ z : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ t : (ZMod p)ˣ,
        squareCharacterMass (fun ν => ‖quartetParameterValue g h left right ν y z t‖ ^ 2) ρ) =
      crossPairMajorant g h left right ρ y := by
  classical
  unfold crossPairMajorant squareCharacterMass quartetParameterMoment
  simp only [Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (ZMod p)ˣ))
    (t := Finset.univ.filter (fun ν : MulChar (ZMod p) ℂ => ν ^ 2 = ρ))]

/-- Both held leaves may have any fixed square-coset multipliers. The moving
coordinate multiplier may depend on both held leaves. -/
theorem crossPair_held_coefficient_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y : (ZMod p)ˣ)
    (K L : (ZMod p)ˣ) (M : (ZMod p)ˣ → (ZMod p)ˣ → (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r => quartetRatioValue g h left right y
          (K * a ^ 2) (L * b ^ 2) (M a b * r ^ 2)) ρ‖ ^ 2) ≤
      8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        crossPairMajorant g h left right ρ⁻¹ y := by
  let U : ℝ := Fintype.card (ZMod p)ˣ
  let C : ℝ := 2 * ((p : ℝ) / U) ^ 2
  let f (z t : (ZMod p)ˣ) :=
    squareCharacterMass (fun ν => ‖quartetParameterValue g h left right ν y z t‖ ^ 2) ρ⁻¹
  have hC : 0 ≤ C := by positivity
  have hU : 0 ≤ U⁻¹ := by positivity
  have hf (z t : (ZMod p)ˣ) : 0 ≤ f z t :=
    squareCharacterMass_nonneg _ (fun ν => sq_nonneg _) _
  have hpoint (a b : (ZMod p)ˣ) :
      ‖mellinCoefficient (fun r => quartetRatioValue g h left right y
        (K * a ^ 2) (L * b ^ 2) (M a b * r ^ 2)) ρ‖ ^ 2 ≤ C * f (K * a ^ 2) (L * b ^ 2) :=
    quartetRatioValue_square_mellin_bound g h left right y _ _ _ ρ
  calc
    _ ≤ U⁻¹ * (∑ a : (ZMod p)ˣ, U⁻¹ * ∑ b : (ZMod p)ˣ,
        C * f (K * a ^ 2) (L * b ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hU
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => hpoint a b) hU
    _ = U⁻¹ * U⁻¹ * C * (∑ a : (ZMod p)ˣ, ∑ b : (ZMod p)ˣ,
        f (K * a ^ 2) (L * b ^ 2)) := by
      simp only [← Finset.mul_sum]
      ring
    _ ≤ U⁻¹ * U⁻¹ * C * (4 * ∑ z : (ZMod p)ˣ, ∑ t : (ZMod p)ˣ, f z t) :=
      mul_le_mul_of_nonneg_left (sum_square_coset_pair_le_four K L f hf)
        (mul_nonneg (mul_nonneg hU hU) hC)
    _ = 8 * ((p : ℝ) / U) ^ 2 *
        (U⁻¹ * ∑ z : (ZMod p)ˣ, U⁻¹ * ∑ t : (ZMod p)ˣ, f z t) := by
      simp only [← Finset.mul_sum, C]
      ring
    _ = _ := by rw [crossPairMajorant_parameter_average]

end Ostmann

end OAI
