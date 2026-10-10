import OAI.Combinatorics.Progressions.Lattices.WeightedSliceIntegerImage

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def rectangularResidueCharacter {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) : AddChar (J → ZMod M) ℂ where
  toFun z := ∏ j, cyclicIntegerCharacter M ((k j).val : ℤ) (z j)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Pi.add_apply, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

theorem rectangularResidueCharacter_integerGridResidue {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : J → ℤ) :
    rectangularResidueCharacter M k (integerGridResidue M y) = rectangularGridCharacter M k y := by
  change (∏ j, cyclicIntegerCharacter M ((k j).val : ℤ) (y j : ZMod M)) =
    ∏ j, cyclicIntegerCharacter M (y j) ((k j).val : ZMod M)
  apply Finset.prod_congr rfl
  intro j _
  change CircleFourier.character (ZMod.toAddCircle ((y j : ZMod M) * (((k j).val : ℤ) : ZMod M))) =
    CircleFourier.character (ZMod.toAddCircle (((k j).val : ZMod M) * (y j : ZMod M)))
  simp only [Int.cast_natCast, mul_comm]

noncomputable def rectangularResidueMode {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) : AddChar (J → ZMod M) ℂ :=
  (rectangularResidueCharacter M k)⁻¹

theorem rectangularResidueMode_integerGridResidue {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : J → ℤ) :
    rectangularResidueMode M k (integerGridResidue M y) = star (rectangularGridCharacter M k y) := by
  rw [rectangularResidueMode, AddChar.inv_apply, AddChar.map_neg_eq_inv, AddChar.inv_apply_eq_conj,
    rectangularResidueCharacter_integerGridResidue]
  rfl

noncomputable def residueGridApproximation {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) [NeZero M]
    (S : Finset (J → Fin M)) (z : J → ZMod M) : ℂ :=
  ∑ k : S, integerRetainedCoefficient p Y K M k * rectangularResidueMode M k z

theorem residueGridApproximation_integerGridResidue {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) [NeZero M]
    (S : Finset (J → Fin M)) (y : J → ℤ) :
    residueGridApproximation p Y K M S (integerGridResidue M y) =
      integerGridApproximation p Y K M S y := by
  rw [residueGridApproximation, integerGridApproximation_eq_sum]
  simp_rw [rectangularResidueMode_integerGridResidue]
  exact Finset.sum_coe_sort S
    (fun k => integerRetainedCoefficient p Y K M k * star (rectangularGridCharacter M k y))

theorem residueGridProjection_tested_error {X J H G : Type*}
    [Fintype X] [Fintype J] [AddCommGroup H] [Fintype H] [Fintype G]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) [NeZero M]
    (S : Finset (J → Fin M)) (q : FiniteProbabilityWeights G) (ι : H →+ (J → ZMod M))
    (f w : G → ℂ) (path : G → J → ℤ) {B C ρ τ : ℝ}
    (hKM : K ≤ M) (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) (hw : q.mean (fun x => ‖w x‖) ≤ B)
    (hcap : (∑ k, ‖integerGridCoefficient p Y M k‖) ≤ C)
    (happrox : ∀ x, q.weight x ≠ 0 → ‖f x - integerGridApproximation p Y K M S (path x)‖ ≤ ρ)
    (hdiscard : ∀ k : S, (rectangularResidueMode M k).compAddMonoidHom ι ≠ 1 →
      ‖q.complexMean (fun x => w x * star (rectangularGridCharacter M k (path x)))‖ ≤ τ) :
    ‖q.complexMean (fun x => w x * f x) -
      q.complexMean (fun x => w x * finiteCosetAverage ι (residueGridApproximation p Y K M S)
        (integerGridResidue M (path x)))‖ ≤ B * ρ + C * τ := by
  apply finiteCosetAverage_truncation_tested_error q ι f (fun x => integerGridResidue M (path x)) w
    (fun k : S => integerRetainedCoefficient p Y K M k) (fun k : S => rectangularResidueMode M k)
    hρ hτ hw
  · calc
      _ = ∑ k ∈ S, ‖integerRetainedCoefficient p Y K M k‖ :=
        Finset.sum_coe_sort S (fun k => ‖integerRetainedCoefficient p Y K M k‖)
      _ ≤ C := integerRetainedCoefficient_mass_le p Y K M S hKM hcap
  · intro x hx
    change ‖f x - residueGridApproximation p Y K M S (integerGridResidue M (path x))‖ ≤ ρ
    rw [residueGridApproximation_integerGridResidue]
    exact happrox x hx
  · intro k hk
    simpa only [rectangularResidueMode_integerGridResidue] using hdiscard k hk

end Erdos3

end

end OAI
