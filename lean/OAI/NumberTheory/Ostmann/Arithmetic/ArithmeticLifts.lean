import Mathlib.Data.Fintype.BigOperators
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticLines

namespace OAI

/-! # Uniform lifts of a nonzero line modulo a prime square

The reduction map has exactly `p` lifts over every residue. A line with a
unit coefficient has exactly `p` zero lifts among the `p²` pairs over a
fixed solution modulo `p`. This is the relative `1/p` loss in §8.
-/

namespace Ostmann

open scoped BigOperators

/-- Translate an additive fiber to the zero fiber. -/
def additiveFiberEquiv {G H : Type*} [AddGroup G] [AddGroup H]
    (φ : G →+ H) (x : G) : {y : G // φ y = φ x} ≃ {y : G // φ y = 0} where
  toFun y := ⟨y - x, by simp [y.property]⟩
  invFun y := ⟨y + x, by simp [y.property]⟩
  left_inv y := by ext; simp
  right_inv y := by ext; simp

/-- Every fiber of a surjective homomorphism between finite additive groups
has the same size. -/
theorem card_additiveFiber {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] [DecidableEq H]
    (φ : G →+ H) (hφ : Function.Surjective φ) (a : H) :
    Fintype.card G = Fintype.card H * Fintype.card {y : G // φ y = a} := by
  have hsame (b : H) : Fintype.card {y : G // φ y = b} =
      Fintype.card {y : G // φ y = a} := by
    obtain ⟨x, rfl⟩ := hφ a
    obtain ⟨y, rfl⟩ := hφ b
    exact Fintype.card_congr ((additiveFiberEquiv φ y).trans (additiveFiberEquiv φ x).symm)
  calc
    _ = Fintype.card (Σ b : H, {y : G // φ y = b}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv φ)).symm
    _ = ∑ b : H, Fintype.card {y : G // φ y = b} := Fintype.card_sigma
    _ = _ := by simp only [hsame, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- The actual reduction map modulo a prime. -/
def squareReduction (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)

@[simp] theorem squareReduction_natCast (p n : ℕ) :
    squareReduction p (n : ZMod (p ^ 2)) = (n : ZMod p) := map_natCast _ _

theorem card_squareReduction_fiber {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    Fintype.card {x : ZMod (p ^ 2) // squareReduction p x = a} = p := by
  have h := card_additiveFiber (squareReduction p).toAddMonoidHom
    (ZMod.castHom_surjective (dvd_pow_self p (by decide : 2 ≠ 0))) a
  simp only [ZMod.card] at h
  exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos (h.symm.trans (pow_two p))

/-- A prime-square residue is a unit exactly when its reduction is nonzero. -/
theorem isUnit_square_iff {p : ℕ} [Fact p.Prime] (x : ZMod (p ^ 2)) :
    IsUnit x ↔ squareReduction p x ≠ 0 := by
  constructor
  · intro hx
    exact (hx.map (squareReduction p)).ne_zero
  · intro hx
    have hv : squareReduction p x = (x.val : ZMod p) := by
      have h := congrArg (squareReduction p) (ZMod.natCast_zmod_val x)
      simpa only [map_natCast] using h.symm
    have hc : x.val.Coprime p := (ZMod.isUnit_iff_coprime _ _).mp
      (isUnit_iff_ne_zero.mpr (hv ▸ hx))
    have hunit : IsUnit (x.val : ZMod (p ^ 2)) :=
      (ZMod.isUnit_iff_coprime _ _).mpr (hc.pow_right 2)
    simpa only [ZMod.natCast_zmod_val] using hunit

/-- Above a nonzero residue every lift is a unit; passing to Haar-unit
coordinates leaves the same `p` uniformly weighted lifts. -/
noncomputable def squareUnitLiftEquiv {p : ℕ} [Fact p.Prime]
    (a : ZMod p) (ha : a ≠ 0) :
    {u : (ZMod (p ^ 2))ˣ // squareReduction p u = a} ≃
      {x : ZMod (p ^ 2) // squareReduction p x = a} where
  toFun u := ⟨u.1, u.property⟩
  invFun x := by
    have hred : squareReduction p (x : ZMod (p ^ 2)) ≠ 0 := by
      rw [x.property]
      exact ha
    have hu : IsUnit (x : ZMod (p ^ 2)) :=
      (isUnit_square_iff (p := p) (x : ZMod (p ^ 2))).mpr hred
    exact ⟨hu.unit, by simpa only [IsUnit.unit_spec] using x.property⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    exact IsUnit.unit_spec _
  right_inv x := by
    apply Subtype.ext
    dsimp only
    exact IsUnit.unit_spec _

theorem card_squareUnitLift {p : ℕ} [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    Fintype.card {u : (ZMod (p ^ 2))ˣ // squareReduction p u = a} = p := by
  rw [Fintype.card_congr (squareUnitLiftEquiv a ha), card_squareReduction_fiber]

/-- In both giant environments the second residue is a unit. A nonzero
row vanishing there must have a unit first coefficient. -/
theorem square_line_first_isUnit {p : ℕ} [Fact p.Prime]
    (a b : ZMod (p ^ 2)) (x₀ y₀ : ZMod p) (hy : y₀ ≠ 0)
    (hrow : squareReduction p a ≠ 0 ∨ squareReduction p b ≠ 0)
    (hbase : squareReduction p a * x₀ + squareReduction p b * y₀ = 0) :
    IsUnit a := by
  apply (isUnit_square_iff a).mpr
  intro ha
  have hb := hrow.resolve_left (not_not.mpr ha)
  exact line_zero_first_coefficient (squareReduction p b) x₀ y₀ hb hy (ha ▸ hbase)

private theorem unit_linear_solution {R : Type*} [CommRing R]
    (a : Rˣ) (b x y : R) (h : (a : R) * x + b * y = 0) :
    x = -(a⁻¹ : Rˣ) * b * y := by
  have he := congrArg (fun z : R => (a⁻¹ : Rˣ) * z) h
  simp only [mul_add, ← mul_assoc, Units.inv_mul, one_mul, mul_zero] at he
  linear_combination he

/-- A line with a unit first coefficient has one zero lift for each lift of
the second coordinate, over any fixed solution in the quotient. -/
def liftedLineEquiv {R K : Type*} [CommRing R] [CommRing K]
    (φ : R →+* K) (a : Rˣ) (b : R) (x₀ y₀ : K)
    (hbase : φ a * x₀ + φ b * y₀ = 0) :
    {xy : R × R // φ xy.1 = x₀ ∧ φ xy.2 = y₀ ∧ (a : R) * xy.1 + b * xy.2 = 0} ≃
      {y : R // φ y = y₀} where
  toFun xy := ⟨xy.1.2, xy.property.2.1⟩
  invFun y := ⟨(-(a⁻¹ : Rˣ) * b * y, y), by
    refine ⟨?_, y.property, ?_⟩
    · have he := unit_linear_solution (Units.map φ.toMonoidHom a) (φ b) x₀ y₀ hbase
      change x₀ = -φ (↑(a⁻¹)) * φ b * y₀ at he
      simpa only [map_mul, map_neg, y.property] using he.symm
    · simp [mul_assoc]⟩
  left_inv xy := by
    apply Subtype.ext
    apply Prod.ext
    · exact (unit_linear_solution a b xy.1.1 xy.1.2 xy.property.2.2).symm
    · rfl
  right_inv y := rfl

/-- Exactly one out of `p` uniform pairs of lifts makes the line vanish
modulo `p²`, conditional on its vanishing modulo `p`. -/
theorem square_line_lift_probability {p : ℕ} [Fact p.Prime]
    (a : (ZMod (p ^ 2))ˣ) (b : ZMod (p ^ 2)) (x₀ y₀ : ZMod p)
    (hbase : squareReduction p a * x₀ + squareReduction p b * y₀ = 0) :
    (Fintype.card {xy : ZMod (p ^ 2) × ZMod (p ^ 2) //
      squareReduction p xy.1 = x₀ ∧ squareReduction p xy.2 = y₀ ∧
        (a : ZMod (p ^ 2)) * xy.1 + b * xy.2 = 0} : ℝ) /
    ((Fintype.card {x : ZMod (p ^ 2) // squareReduction p x = x₀} : ℝ) *
      (Fintype.card {y : ZMod (p ^ 2) // squareReduction p y = y₀} : ℝ)) =
      (p : ℝ)⁻¹ := by
  rw [Fintype.card_congr (liftedLineEquiv (squareReduction p) a b x₀ y₀ hbase)]
  simp only [card_squareReduction_fiber]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp

end Ostmann

end OAI
