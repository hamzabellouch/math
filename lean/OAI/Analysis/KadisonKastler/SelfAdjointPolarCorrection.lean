import OAI.Analysis.KadisonKastler.PolarSmoothing

namespace OAI

/-! # Correcting an almost involutive selfadjoint element

The polar factor stays selfadjoint. A small square defect gives a linear
norm bound, as required when rounding nearby reducing projections.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem polar_unitary_selfAdjoint (t : Aˣ) (ht : IsSelfAdjoint (t : A))
    (u : unitary A) (hu : (u : A) * CFC.abs (t : A) = (t : A)) :
    IsSelfAdjoint (u : A) := by
  have hc : CFC.abs (t : A) * (u : A) = (u : A) * CFC.abs (t : A) := by
    apply (isUnit_abs t).mul_right_cancel
    have h := (CFC.commute_abs_self (t : A) ht.isStarNormal).eq
    calc
      (CFC.abs (t : A) * (u : A)) * CFC.abs (t : A) =
          CFC.abs (t : A) * ((u : A) * CFC.abs (t : A)) := mul_assoc _ _ _
      _ = CFC.abs (t : A) * (t : A) := by rw [hu]
      _ = (t : A) * CFC.abs (t : A) := h
      _ = ((u : A) * CFC.abs (t : A)) * CFC.abs (t : A) :=
        congrArg (fun a : A => a * CFC.abs (t : A)) hu.symm
  change star (u : A) = (u : A)
  apply (isUnit_abs t).mul_left_cancel
  calc
    CFC.abs (t : A) * star (u : A) = star ((u : A) * CFC.abs (t : A)) := by
      rw [star_mul, (CFC.abs_nonneg (t : A)).star_eq]
    _ = star (t : A) := congrArg star hu
    _ = (t : A) := ht.star_eq
    _ = (u : A) * CFC.abs (t : A) := hu.symm
    _ = CFC.abs (t : A) * (u : A) := hc.symm

theorem exists_selfAdjoint_unitary_of_square_defect [Nontrivial A]
    (x : A) (hx : IsSelfAdjoint x) {r : ℝ} (hr : 0 ≤ r) (hrsmall : r < 1 / 4)
    (hn : ‖x‖ ≤ 1 + r) (hd : ‖x * x - 1‖ ≤ r) :
    ∃ u : unitary A, IsSelfAdjoint (u : A) ∧ ‖(u : A) - x‖ ≤ 3 * r := by
  have hr1 : r < 1 := by linarith
  have hp : IsUnit (x * x) := by
    exact ⟨Units.ofNearby 1 (x * x) (by simpa using hd.trans_lt hr1), rfl⟩
  have hunit : IsUnit x := (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp (by
    simpa only [pow_two] using hp)
  let t : Aˣ := hunit.unit
  have ht : (t : A) = x := hunit.unit_spec
  have htn : ‖((t * t : Aˣ) : A) - 1‖ ≤ r := by simpa only [Units.val_mul, ht] using hd
  have hi := norm_unit_inv_le_of_near_one (t * t) (htn.trans_lt hr1)
  have hpos : 0 < 1 - r := by linarith
  have hpos3 : 0 < 1 - 3 * r := by linarith
  have hine : ‖(((t * t)⁻¹ : Aˣ) : A)‖ ≤ (1 - r)⁻¹ := by
    apply hi.trans
    simpa only [one_div] using
      (one_div_le_one_div_of_le hpos (sub_le_sub_left htn 1))
  have hieq : ((t⁻¹ : Aˣ) : A) = (((t * t)⁻¹ : Aˣ) : A) * (t : A) := by
    simp only [mul_inv_rev, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have hit : ‖((t⁻¹ : Aˣ) : A)‖ ≤ (1 - 3 * r)⁻¹ := by
    rw [hieq]
    calc
      _ ≤ ‖(((t * t)⁻¹ : Aˣ) : A)‖ * ‖(t : A)‖ := norm_mul_le _ _
      _ ≤ (1 - r)⁻¹ * (1 + r) :=
        mul_le_mul hine (by rwa [ht]) (norm_nonneg _) (inv_nonneg.mpr hpos.le)
      _ = (1 + r) / (1 - r) := by ring
      _ ≤ 1 / (1 - 3 * r) := (div_le_div_iff₀ hpos hpos3).mpr (by nlinarith)
      _ = (1 - 3 * r)⁻¹ := one_div _
  obtain ⟨u, hu, hun⟩ := exists_polar_unitary_of_norm_bounds t (by positivity : 0 ≤ 3 * r)
    (by linarith) (by rw [ht]; linarith) hit
  exact ⟨u, polar_unitary_selfAdjoint t (by rwa [ht]) u hu, by simpa only [ht] using hun⟩

end

end KadisonKastler

end OAI
