import OAI.LinearAlgebra.Hadamard.TaoExponents

namespace OAI

/-! Cubic roots of unity and complex symmetries of Tao's matrix. -/

namespace HadamardSix.CubicSymmetry

lemma omega_ne_zero : omega ≠ 0 := by
  exact Complex.exp_ne_zero _

lemma omega_norm : ‖omega‖ = 1 := by
  rw [omega, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

lemma omega_cube : omega ^ (3 : ℕ) = 1 := by
  let z : ℂ := 2 * (Real.pi : ℂ) * Complex.I / 3
  have h : (3 : ℂ) * z = 2 * (Real.pi : ℂ) * Complex.I := by
    dsimp [z]
    ring
  calc
    omega ^ (3 : ℕ) = Complex.exp ((3 : ℂ) * z) := by
      simpa only [omega, z, Nat.cast_ofNat] using
        (Complex.exp_nat_mul z 3).symm
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I) :=
      congrArg Complex.exp h
    _ = 1 := Complex.exp_two_pi_mul_I

lemma omega_zpow_three : omega ^ (3 : ℤ) = 1 := by
  simpa using omega_cube

lemma omega_zpow_mod_three (m : ℤ) :
    omega ^ m = omega ^ (m % 3) := by
  calc
    omega ^ m = omega ^ (m % 3 + 3 * (m / 3)) := by
      rw [Int.emod_add_mul_ediv]
    _ = omega ^ (m % 3) := by
      rw [zpow_add₀ omega_ne_zero, zpow_mul, omega_zpow_three]
      simp

lemma omega_zpow_eq_of_zmod_eq {m n : ℤ}
    (h : (m : ZMod 3) = (n : ZMod 3)) :
    omega ^ m = omega ^ n := by
  have hm : m % 3 = n % 3 :=
    (ZMod.intCast_eq_intCast_iff' m n 3).mp h
  rw [omega_zpow_mod_three m, omega_zpow_mod_three n, hm]

lemma omega_zpow_neg_star (m : ℤ) :
    omega ^ (-m) = star (omega ^ m) := by
  rw [zpow_neg, ← inv_zpow, unit_inv omega_norm]
  exact (map_zpow₀ (starRingEnd ℂ) omega m).symm

lemma tao_unimodular : Unimodular taoMatrix := by
  intro i j
  simp [taoMatrix, norm_zpow, omega_norm]

private lemma zmod_three_nonzero_sign :
    ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by
  decide

/-- Every specified row permutation extends on the literal cubic matrix. -/
theorem every_row_permutation_complex (p : Equiv.Perm Index) :
    ∃ (q : Equiv.Perm Index) (conjugate : Bool)
      (U V : Index → ℂ),
      (∀ i, ‖U i‖ = 1) ∧
      (∀ j, ‖V j‖ = 1) ∧
      ∀ i j,
        taoMatrix (p i) (q j) =
          U i * V j *
            (if conjugate then star (taoMatrix i j)
             else taoMatrix i j) := by
  classical
  obtain ⟨q, s, u, v, he⟩ :=
    TaoSymmetry.every_row_permutation p
  let U : Index → ℂ := fun i => omega ^ ((u i).val : ℤ)
  let V : Index → ℂ := fun j => omega ^ ((v j).val : ℤ)
  have hU : ∀ i, ‖U i‖ = 1 := by
    intro i
    simp [U, norm_zpow, omega_norm]
  have hV : ∀ j, ‖V j‖ = 1 := by
    intro j
    simp [V, norm_zpow, omega_norm]
  have hs : (s : ZMod 3) = 1 ∨ (s : ZMod 3) = -1 :=
    zmod_three_nonzero_sign s (Units.ne_zero s)
  rcases hs with hs | hs
  · refine ⟨q, false, U, V, hU, hV, ?_⟩
    intro i j
    change taoMatrix (p i) (q j) =
      U i * V j * taoMatrix i j
    have hc :
        (taoExponent (p i) (q j) : ZMod 3) =
          ((taoExponent i j + ((u i).val : ℤ) +
            ((v j).val : ℤ) : ℤ) : ZMod 3) := by
      simpa [TaoSymmetry.exponent, hs,
        ZMod.natCast_zmod_val] using he i j
    calc
      taoMatrix (p i) (q j) =
          omega ^ (taoExponent i j + ((u i).val : ℤ) +
            ((v j).val : ℤ)) :=
        omega_zpow_eq_of_zmod_eq hc
      _ = U i * V j * taoMatrix i j := by
        dsimp [U, V, taoMatrix]
        rw [zpow_add₀ omega_ne_zero, zpow_add₀ omega_ne_zero]
        ring
  · refine ⟨q, true, U, V, hU, hV, ?_⟩
    intro i j
    change taoMatrix (p i) (q j) =
      U i * V j * star (taoMatrix i j)
    have hc :
        (taoExponent (p i) (q j) : ZMod 3) =
          ((-taoExponent i j + ((u i).val : ℤ) +
            ((v j).val : ℤ) : ℤ) : ZMod 3) := by
      simpa [TaoSymmetry.exponent, hs,
        ZMod.natCast_zmod_val] using he i j
    calc
      taoMatrix (p i) (q j) =
          omega ^ (-taoExponent i j + ((u i).val : ℤ) +
            ((v j).val : ℤ)) :=
        omega_zpow_eq_of_zmod_eq hc
      _ = U i * V j * star (taoMatrix i j) := by
        dsimp [U, V, taoMatrix]
        rw [zpow_add₀ omega_ne_zero, zpow_add₀ omega_ne_zero,
          omega_zpow_neg_star]
        simp only [starRingEnd_apply]
        ring

end HadamardSix.CubicSymmetry

end OAI
