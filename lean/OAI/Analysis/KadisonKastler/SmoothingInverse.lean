import OAI.Analysis.KadisonKastler.ContinuousPolarPath

namespace OAI

/-! # Invertibility and inverse bounds for the smoothed pair -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Two approximate inverse identities give an actual inverse. The algebra
need not be directly finite. -/
theorem isUnit_of_two_approximate_inverses (a c : A)
    (hac : ‖a * c - 1‖ < 1) (hca : ‖c * a - 1‖ < 1) : IsUnit a := by
  let u : Aˣ := Units.oneSub (1 - a * c) (by simpa only [norm_sub_rev] using hac)
  let v : Aˣ := Units.oneSub (1 - c * a) (by simpa only [norm_sub_rev] using hca)
  have hu : (u : A) = a * c := by simp only [u, Units.val_oneSub, sub_sub_cancel]
  have hv : (v : A) = c * a := by simp only [v, Units.val_oneSub, sub_sub_cancel]
  let r : A := c * ((u⁻¹ : Aˣ) : A)
  let l : A := ((v⁻¹ : Aˣ) : A) * c
  have har : a * r = 1 := by
    dsimp only [r]
    rw [← mul_assoc, ← hu, Units.mul_inv]
  have hla : l * a = 1 := by
    dsimp only [l]
    rw [mul_assoc, ← hv, Units.inv_mul]
  have hlr : l = r := by
    calc
      l = l * (a * r) := by rw [har, mul_one]
      _ = (l * a) * r := (mul_assoc _ _ _).symm
      _ = r := by rw [hla, one_mul]
  exact ⟨⟨a, r, har, by rw [← hlr]; exact hla⟩, rfl⟩

/-- The inverse bound only needs the approximate right inverse once actual
invertibility has been established. -/
theorem norm_inverse_le_of_approximate_inverse (a : Aˣ) (c : A) {η : ℝ}
    (hη : η < 1) (hac : ‖(a : A) * c - 1‖ ≤ η) :
    ‖((a⁻¹ : Aˣ) : A)‖ ≤ ‖c‖ / (1 - η) := by
  have he : ((a⁻¹ : Aˣ) : A) = c + ((a⁻¹ : Aˣ) : A) * (1 - (a : A) * c) := by
    rw [mul_sub, mul_one, ← mul_assoc, Units.inv_mul, one_mul]
    abel
  have hh : ‖((a⁻¹ : Aˣ) : A)‖ ≤ ‖c‖ + ‖((a⁻¹ : Aˣ) : A)‖ * η := by
    calc
      _ = ‖c + ((a⁻¹ : Aˣ) : A) * (1 - (a : A) * c)‖ := congrArg norm he
      _ ≤ ‖c‖ + ‖((a⁻¹ : Aˣ) : A) * (1 - (a : A) * c)‖ := norm_add_le _ _
      _ ≤ ‖c‖ + ‖((a⁻¹ : Aˣ) : A)‖ * η := by
        exact add_le_add le_rfl ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
          (by simpa only [norm_sub_rev] using hac) (norm_nonneg _)))
  apply (le_div_iff₀ (sub_pos.mpr hη)).mpr
  nlinarith

theorem norm_unitary_star_sub_approximate_inverse_le
    (t : Aˣ) (u : unitary A) (c : A) {r η : ℝ}
    (hu : ‖(u : A) - (t : A)‖ ≤ r) (hc : ‖(t : A) * c - 1‖ ≤ η) :
    ‖star (u : A) - c‖ ≤ ‖((t⁻¹ : Aˣ) : A)‖ * (r + η) := by
  have he : star (u : A) - c =
      ((t⁻¹ : Aˣ) : A) * ((t : A) - u) * star (u : A) +
      ((t⁻¹ : Aˣ) : A) * (1 - (t : A) * c) := by
    rw [mul_sub, sub_mul, mul_sub, mul_one, ← mul_assoc,
      Units.inv_mul, one_mul, mul_assoc, Unitary.mul_star_self_of_mem u.property]
    simp only [mul_one, one_mul]
    abel
  rw [he]
  calc
    _ ≤ ‖((t⁻¹ : Aˣ) : A) * ((t : A) - u) * star (u : A)‖ +
        ‖((t⁻¹ : Aˣ) : A) * (1 - (t : A) * c)‖ := norm_add_le _ _
    _ = ‖((t⁻¹ : Aˣ) : A) * ((t : A) - u)‖ +
        ‖((t⁻¹ : Aˣ) : A) * (1 - (t : A) * c)‖ := by
      rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
    _ ≤ ‖((t⁻¹ : Aˣ) : A)‖ * ‖(t : A) - u‖ +
        ‖((t⁻¹ : Aˣ) : A)‖ * ‖1 - (t : A) * c‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖((t⁻¹ : Aˣ) : A)‖ * r + ‖((t⁻¹ : Aˣ) : A)‖ * η :=
      add_le_add (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hu)
        (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hc) (norm_nonneg _))
    _ = _ := by ring

end

end KadisonKastler

end OAI
