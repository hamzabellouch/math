import OAI.Analysis.KadisonKastler.Polar

namespace OAI

/-! # Quantitative polar smoothing from bounds on an operator and its inverse -/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_polar_unitary_of_norm_bounds [Nontrivial A] (t : Aˣ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (ht : ‖(t : A)‖ ≤ 1 + r)
    (hti : ‖((t⁻¹ : Aˣ) : A)‖ ≤ (1 - r)⁻¹) :
    ∃ u : unitary A, (u : A) * CFC.abs (t : A) = (t : A) ∧ ‖(u : A) - (t : A)‖ ≤ r := by
  obtain ⟨u, hu⟩ := exists_unitary_mul_abs t
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  have hdecomp : (u : A) * (s : A) = (t : A) := by rwa [hs]
  have hinveq : ((s⁻¹ : Aˣ) : A) = ((t⁻¹ : Aˣ) : A) * (u : A) := by
    calc
      ((s⁻¹ : Aˣ) : A) =
          (((t⁻¹ : Aˣ) : A) * (t : A)) * ((s⁻¹ : Aˣ) : A) := by simp
      _ = (((t⁻¹ : Aˣ) : A) * ((u : A) * (s : A))) * ((s⁻¹ : Aˣ) : A) := by rw [hdecomp]
      _ = ((t⁻¹ : Aˣ) : A) * (u : A) := by
        simp only [mul_assoc, Units.mul_inv, mul_one]
  have hsinv : ‖((s⁻¹ : Aˣ) : A)‖ ≤ (1 - r)⁻¹ := by
    rw [hinveq, CStarRing.norm_mul_coe_unitary]
    exact hti
  have hsbound : ‖(s : A) - 1‖ ≤ r := norm_positive_unit_sub_one_le s
    (by rw [hs]; exact CFC.abs_nonneg _) hr hr1 (by simpa only [hs, CFC.norm_abs] using ht) hsinv
  refine ⟨u, hu, ?_⟩
  have hdiff : (u : A) - (t : A) = (u : A) * (1 - CFC.abs (t : A)) := by
    rw [mul_sub, mul_one, hu]
  rw [hdiff, CStarRing.norm_coe_unitary_mul, norm_sub_rev, ← hs]
  exact hsbound

theorem exists_polar_unitary_near_approximate_inverse [Nontrivial A]
    (t : Aˣ) (c : A) {r η : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ht : ‖(t : A)‖ ≤ 1 + r) (hti : ‖((t⁻¹ : Aˣ) : A)‖ ≤ (1 - r)⁻¹)
    (hc : ‖(t : A) * c - 1‖ ≤ η) :
    ∃ u : unitary A, ‖(u : A) - (t : A)‖ ≤ r ∧
      ‖star (u : A) - c‖ ≤ ‖((t⁻¹ : Aˣ) : A)‖ * (r + η) := by
  obtain ⟨u, _, hu⟩ := exists_polar_unitary_of_norm_bounds t hr hr1 ht hti
  refine ⟨u, hu, ?_⟩
  have heq : star (u : A) - c =
      ((t⁻¹ : Aˣ) : A) * ((t : A) - u) * star (u : A) +
      ((t⁻¹ : Aˣ) : A) * (1 - (t : A) * c) := by
    rw [mul_sub, sub_mul, mul_sub, mul_one, ← mul_assoc,
      Units.inv_mul, one_mul, mul_assoc, Unitary.mul_star_self_of_mem u.property]
    simp only [mul_one, one_mul]
    abel
  rw [heq]
  calc
    _ ≤ ‖((t⁻¹ : Aˣ) : A) * ((t : A) - u) * star (u : A)‖ +
      ‖((t⁻¹ : Aˣ) : A) * (1 - (t : A) * c)‖ := norm_add_le _ _
    _ = ‖((t⁻¹ : Aˣ) : A) * ((t : A) - u)‖ +
      ‖((t⁻¹ : Aˣ) : A) * (1 - (t : A) * c)‖ := by
      rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
    _ ≤ ‖((t⁻¹ : Aˣ) : A)‖ * ‖(t : A) - u‖ +
      ‖((t⁻¹ : Aˣ) : A)‖ * ‖1 - (t : A) * c‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖((t⁻¹ : Aˣ) : A)‖ * r + ‖((t⁻¹ : Aˣ) : A)‖ * η := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hu) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hc) (norm_nonneg _)
    _ = _ := by ring

end

end KadisonKastler

end OAI
