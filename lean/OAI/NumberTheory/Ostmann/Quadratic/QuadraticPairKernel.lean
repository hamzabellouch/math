import OAI.NumberTheory.Ostmann.QuadraticSieve.ComplexJacobiPrimitive

namespace OAI

/-! # The primitive kernel of a pair of odd squarefree denominators

Writing `d = gcd n₁ n₂`, the product character has squarefree kernel
`(n₁/d)(n₂/d)` and the remaining factor is precisely the coprimality mask
modulo `d`. This is the arithmetic decomposition in Heath-Brown (1995), §3.
-/

namespace Ostmann

def quadraticPairKernel (n₁ n₂ : ℕ) : ℕ :=
  (n₁ / n₁.gcd n₂) * (n₂ / n₁.gcd n₂)

 theorem quadraticPairKernel_factor (n₁ n₂ : ℕ) :
    n₁.gcd n₂ ^ 2 * quadraticPairKernel n₁ n₂ = n₁ * n₂ := by
  unfold quadraticPairKernel
  calc
    _ = (n₁.gcd n₂ * (n₁ / n₁.gcd n₂)) *
        (n₁.gcd n₂ * (n₂ / n₁.gcd n₂)) := by ring
    _ = _ := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n₁ n₂),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right n₁ n₂)]

 theorem quadraticPairKernel_squarefree {n₁ n₂ : ℕ}
    (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    Squarefree (quadraticPairKernel n₁ n₂) := by
  apply (Nat.squarefree_mul (Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h₁.ne_zero)))).mpr
  exact ⟨h₁.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n₁ n₂)),
    h₂.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right n₁ n₂))⟩

 theorem quadraticPairKernel_odd {n₁ n₂ : ℕ} (h₁ : Odd n₁) (h₂ : Odd n₂) :
    Odd (quadraticPairKernel n₁ n₂) :=
  (h₁.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n₁ n₂))).mul
    (h₂.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right n₁ n₂)))

 theorem quadraticPairKernel_coprime_gcd {n₁ n₂ : ℕ}
    (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    (n₁.gcd n₂).Coprime (quadraticPairKernel n₁ n₂) := by
  apply Nat.Coprime.mul_right
  · exact ((Nat.coprime_div_gcd_of_squarefree h₁ h₂.ne_zero).of_dvd_right
      (Nat.gcd_dvd_right n₁ n₂)).symm
  · rw [Nat.gcd_comm n₁ n₂]
    exact ((Nat.coprime_div_gcd_of_squarefree h₂ h₁.ne_zero).of_dvd_right
      (Nat.gcd_dvd_right n₂ n₁)).symm

 theorem quadraticPairKernel_eq_one_iff {n₁ n₂ : ℕ}
    (h₁ : Squarefree n₁) (_h₂ : Squarefree n₂) :
    quadraticPairKernel n₁ n₂ = 1 ↔ n₁ = n₂ := by
  constructor
  · intro h
    change (n₁ / n₁.gcd n₂) * (n₂ / n₁.gcd n₂) = 1 at h
    have ha : n₁ / n₁.gcd n₂ = 1 := Nat.eq_one_of_dvd_one
      ⟨n₂ / n₁.gcd n₂, h.symm⟩
    have hb : n₂ / n₁.gcd n₂ = 1 := Nat.eq_one_of_dvd_one
      ⟨n₁ / n₁.gcd n₂, by simpa only [mul_comm] using h.symm⟩
    have ha' := Nat.mul_div_cancel' (Nat.gcd_dvd_left n₁ n₂)
    have hb' := Nat.mul_div_cancel' (Nat.gcd_dvd_right n₁ n₂)
    rw [ha, mul_one] at ha'
    rw [hb, mul_one] at hb'
    exact ha'.symm.trans hb'
  · rintro rfl
    simp [quadraticPairKernel, Nat.div_self (Nat.pos_of_ne_zero h₁.ne_zero)]

 theorem jacobi_pair_kernel {n₁ n₂ : ℕ} (h₁ : Squarefree n₁)
    (h₂ : Squarefree n₂) (m : ℤ) :
    jacobiSym m n₁ * jacobiSym m n₂ =
      if m.gcd (n₁.gcd n₂) = 1 then jacobiSym m (quadraticPairKernel n₁ n₂) else 0 := by
  let : NeZero n₁ := ⟨h₁.ne_zero⟩
  let : NeZero n₂ := ⟨h₂.ne_zero⟩
  have hd : n₁.gcd n₂ ≠ 0 := (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h₁.ne_zero)).ne'
  have hq : quadraticPairKernel n₁ n₂ ≠ 0 := (quadraticPairKernel_squarefree h₁ h₂).ne_zero
  rw [← jacobiSym.mul_right, ← quadraticPairKernel_factor,
    jacobiSym.mul_right' m (pow_ne_zero _ hd) hq, jacobiSym.pow_right]
  split_ifs with hm
  · rw [jacobiSym.sq_one hm, one_mul]
  · rw [(jacobiSym.eq_zero_iff).mpr ⟨hd, hm⟩, zero_pow (by decide), zero_mul]

end Ostmann

end OAI
