import Mathlib

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Parameters

noncomputable section

def a (m : ℕ) : ℝ := 1 / (4*m)
def b₀ (m : ℕ) : ℝ := 1 / (2*m)
def ν (m : ℕ) : ℝ := 1 / (2^7 * (m:ℝ)^3)
def β (m : ℕ) : ℝ := 1 / (2^10 * (m:ℝ)^3)
def ell (m : ℕ) : ℕ := 2^11*m^3
def h (m : ℕ) : ℕ := 2^12*m^3
def d (m : ℕ) : ℕ := 2^38*m^10
def σ (m : ℕ) : ℝ := 1 / (2^46 * (m:ℝ)^12)
def p (m : ℕ) : ℕ := 2*d m+1
def t (m : ℕ) : ℕ := 2^17*m^4

theorem d_square (m : ℕ) : d m = (2^19*m^5)^2 := by
  unfold d
  ring

theorem sqrt_d (m : ℕ) : Real.sqrt (d m) = 2^19*(m:ℝ)^5 := by
  rw [d_square]
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (by positivity)

theorem t_eq (m : ℕ) (hm : 0 < m) : (t m : ℝ) = a m * Real.sqrt (d m) := by
  rw [sqrt_d]
  have hp : (m:ℝ) ≠ 0 := by positivity
  simp only [t, a, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ring

theorem positive (m : ℕ) (hm : 0 < m) :
    0 < ν m ∧ 0 < β m ∧ 0 < ell m ∧ 0 < h m ∧ 0 < d m ∧ 0 < σ m := by
  dsimp [ν, β, ell, h, d, σ]
  constructor <;> try positivity
  constructor <;> try positivity
  constructor <;> try positivity
  constructor <;> try positivity
  constructor <;> positivity

theorem dimensions (m : ℕ) (hm : 4 ≤ m) :
    4 ≤ d m ∧ 2 ≤ h m ∧ h m < d m ∧ Even (d m) := by
  have h1 : 1 ≤ m := by omega
  have h3 : 1 ≤ m^3 := one_le_pow₀ h1
  have h310 : m^3 ≤ m^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h10 : 1 ≤ m^10 := one_le_pow₀ h1
  dsimp [d, h]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · omega
  · exact ⟨137438953472*m^10, by omega⟩

theorem restriction_budget (m : ℕ) (hm : 4 ≤ m) :
    16*(h m : ℝ)+32*(h m : ℝ)^2 ≤ ν m*(d m : ℝ)/2 := by
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hp : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have h36 : (m:ℝ)^3 ≤ (m:ℝ)^6 := pow_le_pow_right₀ hm1 (by decide)
  have h67 : (m:ℝ)^6 ≤ (m:ℝ)^7 := pow_le_pow_right₀ hm1 (by decide)
  have h6 : (0:ℝ) ≤ (m:ℝ)^6 := by positivity
  have heq : ν m*(d m : ℝ)/2 = 2^30*(m:ℝ)^7 := by
    simp only [ν, d, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  rw [heq]
  simp only [h, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith [sq_nonneg ((m:ℝ)^3)]

theorem β_h (m : ℕ) (hm : 0 < m) : β m*(h m : ℝ)/2 = 2 := by
  have hp : (m:ℝ) ≠ 0 := by positivity
  simp only [β, h, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem ell_eq (m : ℕ) (hm : 0 < m) : (ell m : ℝ) = 2/β m := by
  have hp : (m:ℝ) ≠ 0 := by positivity
  simp only [ell, β, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem σ_eq (m : ℕ) : σ m = 1 / ((h m : ℝ)^2*(ell m : ℝ)^2) := by
  unfold σ h ell
  push_cast
  congr 1
  ring

theorem grid_budget (m : ℕ) (hm : 4 ≤ m) :
    (d m : ℝ)/(p m : ℝ) < 1/2 ∧ (1:ℝ)/2 < (t m : ℝ)/2 ∧ 2*m < p m := by
  have hd := (dimensions m hm).1
  have hm1 : 1 ≤ m := by omega
  have hm4 : 1 ≤ m^4 := one_le_pow₀ hm1
  have hmd : m ≤ d m := by
    have hpow : m^1 ≤ m^10 := Nat.pow_le_pow_right (by omega) (by decide)
    simp only [pow_one] at hpow
    dsimp [d]
    omega
  refine ⟨?_, ?_, ?_⟩
  · have hp : (0:ℝ) < p m := by unfold p; positivity
    apply (div_lt_iff₀ hp).mpr
    simp only [p, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    linarith
  · have ht : 1 < t m := by dsimp [t]; omega
    have ht' : (1:ℝ) < t m := by exact_mod_cast ht
    linarith
  · dsimp [p]; omega

end

end VertexCover.Parameters

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
