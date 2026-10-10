import OAI.Geometry.HeilbronnTriangle.RankOneMinors

namespace OAI


namespace Problem355.UnitPivot

open Matrix

variable {R : Type*} [CommRing R]
variable {m n l : Type*}

theorem MinorsVanish.mul_left [Fintype m]
    {A : Matrix m n R} (hA : MinorsVanish A) (P : Matrix l m R) :
    MinorsVanish (P * A) := by
  intro i k j t
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  calc
    (P i b * A b j) * (P k a * A a t) =
        (P i b * P k a) * (A b j * A a t) := by ring
    _ = (P i b * P k a) * (A b t * A a j) := by rw [hA b a j t]
    _ = (P i b * A b t) * (P k a * A a j) := by ring

theorem minorsVanish_transpose_iff (A : Matrix m n R) :
    MinorsVanish A.transpose ↔ MinorsVanish A := by
  constructor <;> intro h i k j t
  · simpa only [Matrix.transpose_apply, mul_comm] using h j t i k
  · simpa only [Matrix.transpose_apply, mul_comm] using h j t i k

theorem MinorsVanish.mul_right [Fintype n]
    {A : Matrix m n R} (hA : MinorsVanish A) (Q : Matrix n l R) :
    MinorsVanish (A * Q) := by
  apply (minorsVanish_transpose_iff _).mp
  rw [Matrix.transpose_mul]
  exact ((minorsVanish_transpose_iff A).mpr hA).mul_left Q.transpose

theorem minorsVanish_unit_mul_iff [Fintype m] [DecidableEq m]
    (P : Matrix.GeneralLinearGroup m R) (A : Matrix m n R) :
    MinorsVanish ((P : Matrix m m R) * A) ↔ MinorsVanish A := by
  constructor
  · intro h
    have hh := h.mul_left (↑(P⁻¹) : Matrix m m R)
    simpa only [← Matrix.mul_assoc, P.inv_mul, Matrix.one_mul] using hh
  · exact fun h => h.mul_left _

theorem minorsVanish_mul_unit_iff [Fintype n] [DecidableEq n]
    (A : Matrix m n R) (Q : Matrix.GeneralLinearGroup n R) :
    MinorsVanish (A * (Q : Matrix n n R)) ↔ MinorsVanish A := by
  constructor
  · intro h
    have hh := h.mul_right (↑(Q⁻¹) : Matrix n n R)
    simpa only [Matrix.mul_assoc, Q.mul_inv, Matrix.mul_one] using hh
  · exact fun h => h.mul_right _

theorem minorsVanish_equivalent_iff [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (P : Matrix.GeneralLinearGroup m R) (Q : Matrix.GeneralLinearGroup n R)
    (A : Matrix m n R) :
    MinorsVanish ((P : Matrix m m R) * A * (Q : Matrix n n R)) ↔
      MinorsVanish A := by
  rw [minorsVanish_mul_unit_iff, minorsVanish_unit_mul_iff]

theorem minorsVanish_diagonal_three_iff (D E : R) :
    MinorsVanish (Matrix.diagonal ![1, D, E]) ↔ D = 0 ∧ E = 0 := by
  rw [minorsVanish_iff_pivot _ 0 0 (1 : Rˣ) (by simp)]
  constructor
  · intro h
    exact ⟨by simpa using h 1 1, by simpa using h 2 2⟩
  · rintro ⟨rfl, rfl⟩ i j
    fin_cases i <;> fin_cases j <;> simp

theorem minorsVanish_diagonal_prime_power_iff
    {p b e j : ℕ} (hp : p.Prime) (hbe : b ≤ e) :
    MinorsVanish (Matrix.diagonal
      ![1, ((p ^ b : ℕ) : ZMod (p ^ j)), ((p ^ e : ℕ) : ZMod (p ^ j))]) ↔
      j ≤ b := by
  rw [minorsVanish_diagonal_three_iff]
  simp only [ZMod.natCast_eq_zero_iff, Nat.pow_dvd_pow_iff_le_right hp.one_lt]
  omega

theorem minorsVanish_map_of_diagonal_form_iff
    {S : Type*} [CommRing S] (f : R →+* S)
    (D E : R) (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (C : Matrix (Fin 3) (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * Matrix.diagonal ![1, D, E] *
      (Q : Matrix (Fin 3) (Fin 3) R)) :
    MinorsVanish (C.map f) ↔ f D = 0 ∧ f E = 0 := by
  have hd : (Matrix.diagonal ![1, D, E]).map f = Matrix.diagonal ![1, f D, f E] := by
    rw [Matrix.diagonal_map (map_zero f)]
    congr 1
    funext i
    fin_cases i <;> simp
  have hmap : C.map f =
      (Matrix.GeneralLinearGroup.map f P : Matrix (Fin 3) (Fin 3) S) *
        Matrix.diagonal ![1, f D, f E] *
        (Matrix.GeneralLinearGroup.map f Q : Matrix (Fin 3) (Fin 3) S) := by
    rw [hC, Matrix.map_mul, Matrix.map_mul]
    rw [hd]
    rfl
  rw [hmap, minorsVanish_equivalent_iff, minorsVanish_diagonal_three_iff]

theorem minorsVanish_reduce_prime_power_iff
    {p k b e j : ℕ} (hp : p.Prime) (hbe : b ≤ e) (hjk : j ≤ k)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
    (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))) *
      Matrix.diagonal ![1, ((p ^ b : ℕ) : ZMod (p ^ k)),
        ((p ^ e : ℕ) : ZMod (p ^ k))] *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))) :
    MinorsVanish (C.map (ZMod.castHom (Nat.pow_dvd_pow p hjk) (ZMod (p ^ j)))) ↔
      j ≤ b := by
  rw [minorsVanish_map_of_diagonal_form_iff _ _ _ P Q C hC]
  simp only [map_natCast, ZMod.natCast_eq_zero_iff,
    Nat.pow_dvd_pow_iff_le_right hp.one_lt]
  omega

theorem smaller_exponent_eq_of_diagonal_forms
    {p k b₁ e₁ b₂ e₂ : ℕ} (hp : p.Prime)
    (hbe₁ : b₁ ≤ e₁) (he₁ : e₁ ≤ k) (hbe₂ : b₂ ≤ e₂) (he₂ : e₂ ≤ k)
    (P₁ Q₁ P₂ Q₂ : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
    (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
    (hC₁ : C = (P₁ : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))) *
      Matrix.diagonal ![1, ((p ^ b₁ : ℕ) : ZMod (p ^ k)),
        ((p ^ e₁ : ℕ) : ZMod (p ^ k))] *
      (Q₁ : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))))
    (hC₂ : C = (P₂ : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))) *
      Matrix.diagonal ![1, ((p ^ b₂ : ℕ) : ZMod (p ^ k)),
        ((p ^ e₂ : ℕ) : ZMod (p ^ k))] *
      (Q₂ : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))) : b₁ = b₂ := by
  apply Nat.le_antisymm
  · exact (minorsVanish_reduce_prime_power_iff hp hbe₂ (hbe₁.trans he₁)
      P₂ Q₂ C hC₂).mp
      ((minorsVanish_reduce_prime_power_iff hp hbe₁ (hbe₁.trans he₁)
        P₁ Q₁ C hC₁).mpr le_rfl)
  · exact (minorsVanish_reduce_prime_power_iff hp hbe₁ (hbe₂.trans he₂)
      P₁ Q₁ C hC₁).mp
      ((minorsVanish_reduce_prime_power_iff hp hbe₂ (hbe₂.trans he₂)
        P₂ Q₂ C hC₂).mpr le_rfl)

end Problem355.UnitPivot

end OAI
