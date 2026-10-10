import OAI.Computability.UniqueGames.Inverse.EqualityFiber

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.FactorSampling

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Information

variable {A B : Type*} [Fintype A] [Fintype B] [Zero A] [Zero B]

def fullAverage (p : A → ℝ) (q : B → ℝ) (h : A → B → ℝ) : ℝ :=
  ∑ a, ∑ b, p a * q b * h a b

def nonzeroFlow (p : A → ℝ) (q : B → ℝ) (h : A → B → ℝ) : ℝ :=
  ∑ a, ∑ b, p a * q b * if a ≠ 0 ∧ b ≠ 0 then h a b else 0

def zeroMass (p : A → ℝ) (q : B → ℝ) : ℝ :=
  p 0 + q 0 - p 0 * q 0

omit [Fintype A] [Fintype B] in
private theorem boundary_indicator (a : A) (b : B) :
    (if a = 0 ∨ b = 0 then (1 : ℝ) else 0) =
      (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) -
        (if a = 0 then 1 else 0) * (if b = 0 then 1 else 0) := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]

/-- The overlap of the two zero-factor events is subtracted exactly once. -/
theorem boundary_mass (p : A → ℝ) (q : B → ℝ)
    (hp : IsProbability p) (hq : IsProbability q) :
    fullAverage p q (fun a b => if a = 0 ∨ b = 0 then 1 else 0) = zeroMass p q := by
  unfold fullAverage zeroMass
  simp_rw [boundary_indicator, mul_sub, mul_add]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h₁ : (∑ a, ∑ b, p a * q b * if a = 0 then 1 else 0) = p 0 := by
    calc
      _ = ∑ a, p a * (∑ b, q b) * if a = 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = p 0 := by simp [hq.2, mul_ite]
  have h₂ : (∑ a, ∑ b, p a * q b * if b = 0 then 1 else 0) = q 0 := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.sum_mul, hp.2, one_mul]
  have h₃ : (∑ a, ∑ b, p a * q b *
      ((if a = 0 then 1 else 0) * (if b = 0 then 1 else 0))) = p 0 * q 0 := by
    simp [mul_ite]
  rw [h₁, h₂, h₃]

/-- A self-loop occurs whenever either perturbation factor is zero. -/
theorem fullAverage_eq_zeroMass_add_nonzeroFlow (p : A → ℝ) (q : B → ℝ)
    (hp : IsProbability p) (hq : IsProbability q) (h : A → B → ℝ)
    (hleft : ∀ b, h 0 b = 1) (hright : ∀ a, h a 0 = 1) :
    fullAverage p q h = zeroMass p q + nonzeroFlow p q h := by
  have hpoint (a : A) (b : B) : h a b =
      (if a = 0 ∨ b = 0 then 1 else 0) +
        (if a ≠ 0 ∧ b ≠ 0 then h a b else 0) := by
    by_cases ha : a = 0
    · subst a
      simp [hleft]
    · by_cases hb : b = 0
      · subst b
        simp [hright]
      · simp [ha, hb]
  calc
    fullAverage p q h =
        fullAverage p q (fun a b => if a = 0 ∨ b = 0 then 1 else 0) +
          nonzeroFlow p q h := by
      unfold fullAverage nonzeroFlow
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simpa only [mul_add] using congrArg (fun z : ℝ => p a * q b * z) (hpoint a b)
    _ = _ := by rw [boundary_mass p q hp hq]

def conditionedRetention (p : A → ℝ) (q : B → ℝ) (h : A → B → ℝ) : ℝ :=
  nonzeroFlow p q h / (1 - zeroMass p q)

theorem fullAverage_eq_mixture (p : A → ℝ) (q : B → ℝ)
    (hp : IsProbability p) (hq : IsProbability q) (h : A → B → ℝ)
    (hleft : ∀ b, h 0 b = 1) (hright : ∀ a, h a 0 = 1)
    (hzero : zeroMass p q < 1) :
    fullAverage p q h = zeroMass p q +
      (1 - zeroMass p q) * conditionedRetention p q h := by
  rw [fullAverage_eq_zeroMass_add_nonzeroFlow p q hp hq h hleft hright]
  unfold conditionedRetention
  have hne : 1 - zeroMass p q ≠ 0 := by linarith
  field_simp

/-- This is the full sampling-law implication, rather than only the scalar
inequality under an assumed mixture identity. -/
theorem conditionedRetention_ge_half (p : A → ℝ) (q : B → ℝ)
    (hp : IsProbability p) (hq : IsProbability q) (h : A → B → ℝ)
    (hleft : ∀ b, h 0 b = 1) (hright : ∀ a, h a 0 = 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hzero : 0 ≤ zeroMass p q) (hzeroη : zeroMass p q ≤ η / 2)
    (haccept : η ≤ fullAverage p q h) : η / 2 ≤ conditionedRetention p q h := by
  apply EqualityFiber.nonzero_retention_ge_half hη hη1 hzero hzeroη
  rw [← fullAverage_eq_mixture p q hp hq h hleft hright (by linarith)]
  exact haccept

omit [Fintype A] [Fintype B] in
/-- Specialization of the excluded zero-factor mass to uniform binary vector
spaces. The powers are supplied by the cardinalities, so the formula also
keeps track of the overlap when both factors are zero. -/
theorem zeroMass_binary_uniform (p : A → ℝ) (q : B → ℝ) (ell m : ℕ)
    (hp0 : p 0 = ((2 : ℝ) ^ ell)⁻¹) (hq0 : q 0 = ((2 : ℝ) ^ m)⁻¹) :
    zeroMass p q = ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ - ((2 : ℝ) ^ (ell + m))⁻¹ := by
  unfold zeroMass
  rw [hp0, hq0, pow_add, mul_inv]

end
end UniqueGamesTheorem.Inverse.FactorSampling

end

end OAI
