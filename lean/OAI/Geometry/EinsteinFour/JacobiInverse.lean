import OAI.Geometry.EinsteinFour.JacobiPositivity
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

/-! Quantitative inverse control for the normalized Jacobi matrices. -/

namespace PositiveEinsteinFour.Jacobi

noncomputable section

theorem inverse_perturbation_bound
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [Nontrivial R]
    (u : Rˣ) (A : R) {K : ℝ} (hK : 0 < K) (hu : ‖((u⁻¹ : Rˣ) : R)‖ ≤ K)
    (herror : ‖A - (u : R)‖ ≤ 1 / (2 * K)) :
    IsUnit A ∧ ‖Ring.inverse A‖ ≤ 2 * K ∧
      ‖Ring.inverse A - ((u⁻¹ : Rˣ) : R)‖ ≤ 2 * K ^ 2 * ‖A - (u : R)‖ := by
  have heK : ‖A - (u : R)‖ * K ≤ 1 / 2 := by
    calc
      _ ≤ (1 / (2 * K)) * K := mul_le_mul_of_nonneg_right herror hK.le
      _ = _ := by field_simp
  have heI : ‖A - (u : R)‖ * ‖((u⁻¹ : Rˣ) : R)‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hu (norm_nonneg _)).trans heK
  have hnear : ‖A - (u : R)‖ < ‖((u⁻¹ : Rˣ) : R)‖⁻¹ :=
    by
      rw [← one_div]
      exact (lt_div_iff₀ (Units.norm_pos u⁻¹)).mpr (by linarith)
  let v := u.ofNearby A hnear
  have hv : (v : R) = A := rfl
  have huu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := by simp
  have hvv : ((v⁻¹ : Rˣ) : R) * (v : R) = 1 := by simp
  have hid : ((v⁻¹ : Rˣ) : R) = ((u⁻¹ : Rˣ) : R) +
      ((v⁻¹ : Rˣ) : R) * ((u : R) - (v : R)) * ((u⁻¹ : Rˣ) : R) := by
    calc
      _ = ((u⁻¹ : Rˣ) : R) +
          (((v⁻¹ : Rˣ) : R) - ((u⁻¹ : Rˣ) : R)) := by abel
      _ = _ := by
        rw [mul_sub, sub_mul, mul_assoc ((v⁻¹ : Rˣ) : R) (u : R),
          huu, mul_one, hvv, one_mul]
  have hprod : ‖((v⁻¹ : Rˣ) : R) * ((u : R) - (v : R)) * ((u⁻¹ : Rˣ) : R)‖ ≤
      ‖((v⁻¹ : Rˣ) : R)‖ * ‖A - (u : R)‖ * ‖((u⁻¹ : Rˣ) : R)‖ := by
    calc
      _ ≤ (‖((v⁻¹ : Rˣ) : R)‖ * ‖(u : R) - (v : R)‖) * ‖((u⁻¹ : Rˣ) : R)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = _ := by rw [hv, norm_sub_rev]
  have hbound : ‖((v⁻¹ : Rˣ) : R)‖ ≤ 2 * K := by
    have hn : ‖((v⁻¹ : Rˣ) : R)‖ ≤ ‖((u⁻¹ : Rˣ) : R)‖ +
        ‖((v⁻¹ : Rˣ) : R)‖ * ‖A - (u : R)‖ * ‖((u⁻¹ : Rˣ) : R)‖ := by
      calc
        _ = ‖((u⁻¹ : Rˣ) : R) +
            ((v⁻¹ : Rˣ) : R) * ((u : R) - (v : R)) * ((u⁻¹ : Rˣ) : R)‖ := congrArg norm hid
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add_right hprod _)
    have hm := mul_le_mul_of_nonneg_left heI (norm_nonneg (((v⁻¹ : Rˣ) : R)))
    nlinarith [norm_nonneg (((v⁻¹ : Rˣ) : R))]
  have hdiff : ‖((v⁻¹ : Rˣ) : R) - ((u⁻¹ : Rˣ) : R)‖ ≤
      2 * K ^ 2 * ‖A - (u : R)‖ := by
    have hd : ((v⁻¹ : Rˣ) : R) - ((u⁻¹ : Rˣ) : R) =
        ((v⁻¹ : Rˣ) : R) * ((u : R) - (v : R)) * ((u⁻¹ : Rˣ) : R) := by
      exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hid)
    rw [hd]
    calc
      _ ≤ ‖((v⁻¹ : Rˣ) : R)‖ * ‖A - (u : R)‖ * ‖((u⁻¹ : Rˣ) : R)‖ := hprod
      _ ≤ (2 * K) * ‖A - (u : R)‖ * K := by gcongr
      _ = _ := by ring
  have hinv : Ring.inverse A = ((v⁻¹ : Rˣ) : R) := by
    rw [← hv, Ring.inverse_unit]
  refine ⟨hv ▸ v.isUnit, ?_, ?_⟩
  · simpa only [hinv] using hbound
  · simpa only [hinv] using hdiff

/-- The inverse bounds can be chosen once on a compact preconjugate
interval, including the continuously normalized initial endpoint. -/
theorem uniform_inverse_neighborhood
    {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [Nontrivial R]
    {B : ℝ → R} {t : ℝ}
    (hB : ContinuousOn B (Set.Icc 0 t)) (hunit : ∀ s ∈ Set.Icc 0 t, IsUnit (B s)) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ∈ Set.Icc 0 t, ∀ A : R,
      ‖A - B s‖ ≤ 1 / (2 * K) →
      IsUnit A ∧ ‖Ring.inverse A‖ ≤ 2 * K ∧
        ‖Ring.inverse A - Ring.inverse (B s)‖ ≤ 2 * K ^ 2 * ‖A - B s‖ := by
  have hi : ContinuousOn (fun s => Ring.inverse (B s)) (Set.Icc 0 t) := by
    intro s hs
    have hinv : ContinuousAt (Ring.inverse : R → R) (B s) := by
      simpa using (NormedRing.inverse_continuousAt (hunit s hs).unit)
    exact hinv.comp_continuousWithinAt (hB s hs)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hi
  let K := max C 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  refine ⟨K, hK, ?_⟩
  intro s hs A hA
  have hb : ‖(((hunit s hs).unit⁻¹ : Rˣ) : R)‖ ≤ K := by
    have huinv : (((hunit s hs).unit⁻¹ : Rˣ) : R) = Ring.inverse (B s) := by
      exact (Ring.inverse_of_isUnit (hunit s hs)).symm
    rw [huinv]
    exact (hC s hs).trans (le_max_left C 1)
  simpa only [IsUnit.unit_spec, ← Ring.inverse_unit] using
    inverse_perturbation_bound (hunit s hs).unit A hK hb
      (by simpa only [IsUnit.unit_spec] using hA)

end

end PositiveEinsteinFour.Jacobi

end OAI
