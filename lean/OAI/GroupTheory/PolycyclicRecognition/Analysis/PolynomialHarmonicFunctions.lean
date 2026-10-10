import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBallQuadraticForms

namespace OAI

/-! # The translation representation on polynomial-growth harmonic functions -/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

def PolynomiallyBoundedOnWords (S : Finset G) (d : ℕ) (f : G → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ wordBall S n → |f x| ≤ C * (1 + (n : ℝ)) ^ d

def polynomialWordFunctions (S : Finset G) (d : ℕ) : Submodule ℝ (G → ℝ) where
  carrier := {f | PolynomiallyBoundedOnWords S d f}
  zero_mem' := ⟨0, le_rfl, by intro n x _; simp⟩
  add_mem' := by
    rintro f g ⟨C, hC, hf⟩ ⟨D, hD, hg⟩
    refine ⟨C + D, add_nonneg hC hD, fun n x hx => ?_⟩
    exact (abs_add_le (f x) (g x)).trans ((add_le_add (hf n x hx) (hg n x hx)).trans_eq (by ring))
  smul_mem' := by
    rintro c f ⟨C, hC, hf⟩
    refine ⟨|c| * C, mul_nonneg (abs_nonneg _) hC, fun n x hx => ?_⟩
    change |c * f x| ≤ _
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hf n x hx) (abs_nonneg c)).trans_eq (by ring)

def cayleyHarmonicFunctions (S : Finset G) : Submodule ℝ (G → ℝ) where
  carrier := {f | CayleyHarmonic S f}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro f g hf hg x
    change ∑ s ∈ S, (f (x * s) + g (x * s) - (f x + g x)) = 0
    simp only [add_sub_add_comm, sum_add_distrib, hf x, hg x, add_zero]
  smul_mem' := by
    intro c f hf x
    change ∑ s ∈ S, (c * f (x * s) - c * f x) = 0
    simp only [← mul_sub, ← mul_sum, hf x, mul_zero]

def polynomialHarmonicFunctions (S : Finset G) (d : ℕ) : Submodule ℝ (G → ℝ) :=
  polynomialWordFunctions S d ⊓ cayleyHarmonicFunctions S

def cayleyLeftTranslate (g : G) (f : G → ℝ) (x : G) : ℝ := f (g⁻¹ * x)

omit [DecidableEq G] in
theorem cayleyHarmonic_leftTranslate (S : Finset G) {f : G → ℝ}
    (hf : CayleyHarmonic S f) (g : G) : CayleyHarmonic S (cayleyLeftTranslate g f) := by
  intro x
  simpa only [cayleyLeftTranslate, mul_assoc] using hf (g⁻¹ * x)

theorem polynomialWord_leftTranslate (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (d : ℕ) {f : G → ℝ}
    (hf : PolynomiallyBoundedOnWords S d f) (g : G) :
    PolynomiallyBoundedOnWords S d (cayleyLeftTranslate g f) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨m, hm⟩ := wordBall_exhaustive S hS hgen g⁻¹
  refine ⟨C * (1 + (m : ℝ)) ^ d, mul_nonneg hC (by positivity), fun n x hx => ?_⟩
  have hp : 1 + ((m + n : ℕ) : ℝ) ≤ (1 + (m : ℝ)) * (1 + (n : ℝ)) := by
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) n)]
  calc
    _ ≤ C * (1 + ((m + n : ℕ) : ℝ)) ^ d := hf (m + n) _ (mul_mem_wordBall hm hx)
    _ ≤ C * ((1 + (m : ℝ)) * (1 + (n : ℝ))) ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp d) hC
    _ = _ := by rw [mul_pow]; ring

def polynomialHarmonicLeftTranslation (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (d : ℕ) (g : G) :
    polynomialHarmonicFunctions S d ≃ₗ[ℝ] polynomialHarmonicFunctions S d where
  toFun f := ⟨cayleyLeftTranslate g f.val,
    polynomialWord_leftTranslate S hS hgen d f.property.1 g,
    cayleyHarmonic_leftTranslate S f.property.2 g⟩
  invFun f := ⟨cayleyLeftTranslate g⁻¹ f.val,
    polynomialWord_leftTranslate S hS hgen d f.property.1 g⁻¹,
    cayleyHarmonic_leftTranslate S f.property.2 g⁻¹⟩
  left_inv f := by ext x; simp [cayleyLeftTranslate]
  right_inv f := by ext x; simp [cayleyLeftTranslate]
  map_add' f h := by ext x; rfl
  map_smul' c f := by ext x; rfl

def polynomialHarmonicRepresentation (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (d : ℕ) :
    G →* (polynomialHarmonicFunctions S d ≃ₗ[ℝ] polynomialHarmonicFunctions S d) where
  toFun := polynomialHarmonicLeftTranslation S hS hgen d
  map_one' := by ext f x; simp [polynomialHarmonicLeftTranslation, cayleyLeftTranslate]
  map_mul' g h := by
    ext f x
    simp [polynomialHarmonicLeftTranslation, cayleyLeftTranslate, mul_inv_rev, mul_assoc]

end PolycyclicRecognition

end

end OAI
