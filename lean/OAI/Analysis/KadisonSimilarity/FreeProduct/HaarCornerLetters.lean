import OAI.Analysis.KadisonSimilarity.Representation.CStarCorner
import Mathlib.Analysis.InnerProductSpace.Orthonormal

namespace OAI

/-! Normalized Haar powers in a tracial corner. Their adjoints give the
orthonormal first-letter sequence used in the propagation argument. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P] {q : P} {hq : IsStarProjection q}

/-- Integer powers are taken in the unital corner, whose identity is `q`. -/
def haarCornerPower (z : unitary (CStarCorner q hq)) (k : ℤ) : P :=
  (((z ^ k : unitary (CStarCorner q hq)) : CStarCorner q hq) : P)

@[simp] theorem haarCornerPower_zero (z : unitary (CStarCorner q hq)) :
    haarCornerPower z 0 = q := by
  simp only [haarCornerPower, zpow_zero, OneMemClass.coe_one, CStarCorner.coe_one]

@[simp] theorem haarCornerPower_mul (z : unitary (CStarCorner q hq)) (i j : ℤ) :
    haarCornerPower z i * haarCornerPower z j = haarCornerPower z (i + j) := by
  change (((z ^ i * z ^ j : unitary (CStarCorner q hq)) : CStarCorner q hq) : P) = _
  rw [← zpow_add]
  rfl

@[simp] theorem star_haarCornerPower (z : unitary (CStarCorner q hq)) (k : ℤ) :
    star (haarCornerPower z k) = haarCornerPower z (-k) := by
  change (((star (z ^ k) : unitary (CStarCorner q hq)) : CStarCorner q hq) : P) = _
  rw [Unitary.star_eq_inv, ← zpow_neg]
  rfl

@[simp] theorem mul_haarCornerPower (z : unitary (CStarCorner q hq)) (k : ℤ) :
    q * haarCornerPower z k = haarCornerPower z k :=
  ((z ^ k : unitary (CStarCorner q hq)) : CStarCorner q hq).property.1

@[simp] theorem haarCornerPower_mul_support (z : unitary (CStarCorner q hq)) (k : ℤ) :
    haarCornerPower z k * q = haarCornerPower z k :=
  ((z ^ k : unitary (CStarCorner q hq)) : CStarCorner q hq).property.2

/-- The coefficient `a⁻¹ᐟ²`, embedded in the complex scalars. -/
def haarCornerCoefficient (a : ℝ) : ℂ := ((Real.sqrt a)⁻¹ : ℝ)

@[simp] theorem star_haarCornerCoefficient (a : ℝ) :
    star (haarCornerCoefficient a) = haarCornerCoefficient a := by
  simp only [haarCornerCoefficient, Complex.star_def, Complex.conj_ofReal]

theorem haarCornerCoefficient_sq {a : ℝ} (ha : 0 ≤ a) :
    haarCornerCoefficient a * haarCornerCoefficient a = ((a⁻¹ : ℝ) : ℂ) := by
  have h : (Real.sqrt a)⁻¹ * (Real.sqrt a)⁻¹ = a⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt ha]
  unfold haarCornerCoefficient
  exact_mod_cast h

/-- Positive Haar powers, normalized in the ambient tracial Hilbert norm. -/
def haarCornerLetter (z : unitary (CStarCorner q hq)) (a : ℝ) (n : ℕ) : P :=
  haarCornerCoefficient a • haarCornerPower z ((n : ℤ) + 1)

@[simp] theorem support_mul_haarCornerLetter (z : unitary (CStarCorner q hq))
    (a : ℝ) (n : ℕ) : q * haarCornerLetter z a n = haarCornerLetter z a n := by
  simp only [haarCornerLetter, mul_smul_comm, mul_haarCornerPower]

@[simp] theorem haarCornerLetter_mul_support (z : unitary (CStarCorner q hq))
    (a : ℝ) (n : ℕ) : haarCornerLetter z a n * q = haarCornerLetter z a n := by
  simp only [haarCornerLetter, smul_mul_assoc, haarCornerPower_mul_support]

@[simp] theorem star_haarCornerLetter (z : unitary (CStarCorner q hq))
    (a : ℝ) (n : ℕ) : star (haarCornerLetter z a n) =
      haarCornerCoefficient a • haarCornerPower z (-((n : ℤ) + 1)) := by
  simp only [haarCornerLetter, star_smul, star_haarCornerCoefficient, star_haarCornerPower]

theorem star_haarCornerLetter_mul_self (z : unitary (CStarCorner q hq))
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    star (haarCornerLetter z a n) * haarCornerLetter z a n = ((a⁻¹ : ℝ) : ℂ) • q := by
  rw [star_haarCornerLetter]
  simp only [haarCornerLetter, smul_mul_smul, haarCornerPower_mul,
    neg_add_cancel, haarCornerPower_zero, haarCornerCoefficient_sq ha]

theorem haarCornerLetter_mul_star_self (z : unitary (CStarCorner q hq))
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    haarCornerLetter z a n * star (haarCornerLetter z a n) = ((a⁻¹ : ℝ) : ℂ) • q := by
  rw [star_haarCornerLetter]
  simp only [haarCornerLetter, smul_mul_smul, haarCornerPower_mul,
    add_neg_cancel, haarCornerPower_zero, haarCornerCoefficient_sq ha]

variable (τ : P →ₗ[ℂ] ℂ) (z : unitary (CStarCorner q hq)) {a : ℝ}

/-- Haar moments for the corner trace `τ(·)/a`; the zero moment is supplied
by `τ q = a` in the following lemmas. -/
def HaarCornerMoments (a : ℝ) : Prop :=
  ∀ k : ℤ, k ≠ 0 → (a : ℂ)⁻¹ * τ (haarCornerPower z k) = 0

/-- Normalized Haar moments give the unnormalized ambient trace formula. -/
theorem haarCornerPower_trace (ha : 0 < a) (htrace : τ q = (a : ℂ))
    (hhaar : HaarCornerMoments τ z a) (k : ℤ) :
    τ (haarCornerPower z k) = if k = 0 then (a : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simpa only [haarCornerPower_zero, ↓reduceIte] using htrace
  · have h := hhaar k hk
    have hane : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have hz := (mul_eq_zero.mp h).resolve_left (inv_ne_zero hane)
    simpa only [hk, ↓reduceIte] using hz

theorem haarCornerLetter_trace_zero (ha : 0 < a) (htrace : τ q = (a : ℂ))
    (hhaar : HaarCornerMoments τ z a) (n : ℕ) : τ (haarCornerLetter z a n) = 0 := by
  have hn : (n : ℤ) + 1 ≠ 0 := by omega
  simp only [haarCornerLetter, map_smul, haarCornerPower_trace τ z ha htrace hhaar,
    hn, ↓reduceIte, smul_zero]

/-- The opposite-order products of the normalized powers have delta trace.
This order is the one appearing in the inner products of adjoint letters. -/
theorem haarCornerLetter_mul_star_trace (ha : 0 < a) (htrace : τ q = (a : ℂ))
    (hhaar : HaarCornerMoments τ z a) (i j : ℕ) :
    τ (haarCornerLetter z a i * star (haarCornerLetter z a j)) =
      if i = j then 1 else 0 := by
  rw [star_haarCornerLetter]
  simp only [haarCornerLetter, smul_mul_smul, haarCornerPower_mul,
    map_smul, smul_eq_mul, haarCornerCoefficient_sq ha.le,
    haarCornerPower_trace τ z ha htrace hhaar]
  by_cases hij : i = j
  · subst j
    have he : (i : ℤ) + 1 + -((i : ℤ) + 1) = 0 := by omega
    have hane : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    simp only [he, ↓reduceIte, Complex.ofReal_inv, inv_mul_cancel₀ hane]
  · have he : (i : ℤ) + 1 + -((j : ℤ) + 1) ≠ 0 := by omega
    simp only [hij, he, ↓reduceIte, mul_zero]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

/-- The algebraic Haar normalization gives the exact operator identity
used to scale the fixed propagation error. -/
theorem haarCornerLetter_left_scale (G : TracialCornerGeometry P H)
    (z : unitary (CStarCorner q hq)) {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    (G.left (haarCornerLetter z a n)).adjoint.comp (G.left (haarCornerLetter z a n)) =
      ((a⁻¹ : ℝ) : ℂ) • G.left q := by
  have h := congrArg G.left (star_haarCornerLetter_mul_self z ha n)
  simpa only [map_mul, map_star, map_smul, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.mul_def] using h

/-- The adjoint Haar letters form the actual orthonormal Hilbert sequence
required by the vacuum-slice propagation argument. -/
theorem haarCornerLetter_adjoint_orthonormal (G : TracialCornerGeometry P H)
    (z : unitary (CStarCorner q hq)) {a : ℝ} (ha : 0 < a)
    (htrace : G.trace q = (a : ℂ)) (hhaar : HaarCornerMoments G.trace z a) :
    Orthonormal ℂ (fun n : ℕ => G.vector (star (haarCornerLetter z a n))) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [G.inner_vector, star_star]
  exact haarCornerLetter_mul_star_trace G.trace z ha htrace hhaar i j

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
