import OAI.NumberTheory.Ostmann.Characters.QuartetHorizontalMean
import OAI.NumberTheory.Ostmann.Characters.QuartetCycleMean

namespace OAI

/-! # Moving and untouched quartets in one character sum -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance allMajorantsCharFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def quartetOptionalMajorant {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (cL cR : Bool) (choice : Option QuartetMovingCase)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ := by
  classical
  exact match choice with
  | some moving => quartetMovingMajorant g cL cR moving ρ y
  | none => if ρ = 1 then
      8 * differenceMajorant (fieldPairMoment g) (fieldPairMoment g) y else 0

theorem quartetOptionalMajorant_nonneg {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (cL cR : Bool) (choice : Option QuartetMovingCase)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) :
    0 ≤ quartetOptionalMajorant g cL cR choice ρ y := by
  classical
  cases choice with
  | some moving => exact quartetMovingMajorant_nonneg g cL cR moving ρ y
  | none =>
    simp only [quartetOptionalMajorant]
    split_ifs
    · exact mul_nonneg (by norm_num) (mul_nonneg (by positivity)
        (differenceMoment_nonneg _ _ (fieldPairMoment_nonneg g) (fieldPairMoment_nonneg g) y))
    · exact le_rfl

theorem quartetOptionalMajorant_total_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (cL cR : Bool) (choice : Option QuartetMovingCase) :
    (∑ ρ : MulChar (ZMod p) ℂ,
      (∑ y : (ZMod p)ˣ, quartetOptionalMajorant g cL cR choice ρ y) /
        (Fintype.card (ZMod p)ˣ : ℝ)) ≤
      8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4 := by
  classical
  cases choice with
  | some moving => exact quartetMovingMajorant_total_mean_le g hg henergy cL cR moving
  | none =>
    simp only [quartetOptionalMajorant]
    simp_rw [Finset.sum_div]
    rw [Finset.sum_comm]
    simp only [ite_div, zero_div, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (untouchedQuartetMajorant_mean_le g hg henergy) (by norm_num)

/-- The horizontal sum includes every untouched quartet, and loses a small
factor at any one quartet participating in the signed cycle. -/
theorem quartetOptional_cut_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (D : (ZMod p)ˣ) (n : ℕ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ (n + 2) C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool (n + 2))
    (cL cR : TreeLeafIndex n → Bool) (choice : TreeLeafIndex n → Option QuartetMovingCase)
    (sign : TreeLeafIndex n → ℤ) (i : TreeLeafIndex n)
    (hi : sign i = 1 ∨ sign i = -1) (moving : QuartetMovingCase) (hmoving : choice i = some moving) :
    (∑ P : TreeLeafTuple (ZMod p)ˣ n,
      rationalCutCharacterSum D n T XL XR c
        (fun j => quartetOptionalMajorant g (cL j) (cR j) (choice j)) sign P) /
      (Fintype.card (TreeLeafTuple (ZMod p)ˣ n) : ℝ) ≤
      (2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
        (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1)) := by
  apply rationalCutCharacterSum_mean_le D n T XL XR c _ sign i hi
    (quartetLocalMeanError p ε) _ (quartetLocalMeanError_nonneg p ε)
  · exact fun j ρ y => quartetOptionalMajorant_nonneg g (cL j) (cR j) (choice j) ρ y
  · intro ρ
    simp only [hmoving, quartetOptionalMajorant]
    exact quartetMovingMajorant_mean_le g hg henergy ε hε hflat (cL i) (cR i) moving ρ
  · exact fun j => quartetOptionalMajorant_total_mean_le g hg henergy (cL j) (cR j) (choice j)

end Ostmann

end OAI
