import OAI.Analysis.LipschitzHilbert.Phase.DominantCoefficient

namespace OAI

/-!
# Homogeneous fourth-moment bounds

The normalized combinatorial fourth-moment estimate is homogeneous of
degree three in the `ℓ^(4/3)` coefficient masses. These lemmas restore
the arbitrary coefficient normalization used in §7.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

theorem resonanceSum_smul (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) {s : ℝ} (hs : 0 ≤ s) :
    resonanceSum frequency gap (fun i => s * x i) = s ^ 3 * resonanceSum frequency gap x := by
  unfold resonanceSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rcases q with ⟨i, j, k, l⟩
  rw [geometricTerm_eq_rpow (fun i => mul_nonneg hs (hx i)), geometricTerm_eq_rpow hx]
  split_ifs
  · have heq : s * x i * (s * x j) * (s * x k) * (s * x l) =
        s ^ 4 * (x i * x j * x k * x l) := by ring
    rw [heq, Real.mul_rpow (pow_nonneg hs _)
      (mul_nonneg (mul_nonneg (mul_nonneg (hx i) (hx j)) (hx k)) (hx l))]
    congr 1
    rw [← Real.rpow_natCast s 4, ← Real.rpow_mul hs]
    norm_num
  · simp

theorem resonanceSum_le_mass_cube {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    resonanceSum frequency gap x ≤ (∑ i, x i) ^ 3 := by
  let M := ∑ i, x i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => hx i
  by_cases hzero : M = 0
  · have hxzero (i : ι) : x i = 0 := by
      have hi : x i ≤ M := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      exact le_antisymm (hi.trans hzero.le) (hx i)
    have hQ : resonanceSum frequency gap x = 0 := by
      unfold resonanceSum
      apply Finset.sum_eq_zero
      intro q _
      rw [geometricTerm_eq_rpow hx]
      simp [hxzero]
    change resonanceSum frequency gap x ≤ M ^ 3
    rw [hzero, hQ]
    norm_num
  · let y := fun i => x i / M
    have hy : ∀ i, 0 ≤ y i := fun i => div_nonneg (hx i) hM
    have hsum : ∑ i, y i = 1 := by
      dsimp [y]
      rw [← Finset.sum_div, div_self hzero]
    have hscale : (fun i => M * y i) = x := by
      funext i
      dsimp [y]
      field_simp [hzero]
    have hQ := resonanceSum_le_one hgap hsep y hy hsum
    have hhom := resonanceSum_smul frequency gap y hy hM
    rw [hscale] at hhom
    rw [hhom]
    exact mul_le_of_le_one_right (pow_nonneg hM _) hQ

theorem fourth_moment_le_mass_cube (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (∑ i, coefficientMass a i) ^ 3 :=
  (fourth_moment_le_resonanceSum ν frequency a (coefficientMass a) hν
    (coefficientMass_nonneg a) (fun i => (coefficientMass_rpow a i).symm)).trans
    (resonanceSum_le_mass_cube hgap hsep (coefficientMass a) (coefficientMass_nonneg a))

theorem resonanceSum_quantile_gap_mass_cube {frequency : ι → ℝ} {gap κ : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    (hκ : 0 < κ) (hκ1 : κ < 1) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hatom : ∀ i, x i ≤ (1 - κ) * ∑ j, x j) :
    resonanceSum frequency gap x ≤
      (1 - κ ^ 4 * (1 - κ / 2) ^ 2 / 4096) * (∑ i, x i) ^ 3 := by
  let M := ∑ i, x i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => hx i
  by_cases hzero : M = 0
  · have hQ : resonanceSum frequency gap x ≤ M ^ 3 :=
      resonanceSum_le_mass_cube hgap hsep x hx
    change resonanceSum frequency gap x ≤ (1 - κ ^ 4 * (1 - κ / 2) ^ 2 / 4096) * M ^ 3
    rw [hzero] at hQ ⊢
    simpa using hQ
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    let y := fun i => x i / M
    have hy : ∀ i, 0 ≤ y i := fun i => div_nonneg (hx i) hM
    have hsum : ∑ i, y i = 1 := by
      dsimp [y]
      rw [← Finset.sum_div, div_self hzero]
    have hyatom (i : ι) : y i ≤ 1 - κ := (div_le_iff₀ hMpos).2 (hatom i)
    have hscale : (fun i => M * y i) = x := by
      funext i
      dsimp [y]
      field_simp [hzero]
    have hQ := quantile_gap hgap hsep hκ hκ1 y hy hsum hyatom
    have hhom := resonanceSum_smul frequency gap y hy hM
    rw [hscale] at hhom
    rw [hhom]
    exact (mul_le_mul_of_nonneg_left hQ (pow_nonneg hM _)).trans_eq (mul_comm _ _)

theorem fourth_moment_quantile_gap_mass_cube (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap κ : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hκ : 0 < κ) (hκ1 : κ < 1)
    (hatom : ∀ i, coefficientMass a i ≤ (1 - κ) * ∑ j, coefficientMass a j) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (1 - κ ^ 4 * (1 - κ / 2) ^ 2 / 4096) * (∑ i, coefficientMass a i) ^ 3 :=
  (fourth_moment_le_resonanceSum ν frequency a (coefficientMass a) hν
    (coefficientMass_nonneg a) (fun i => (coefficientMass_rpow a i).symm)).trans
    (resonanceSum_quantile_gap_mass_cube hgap hsep hκ hκ1 (coefficientMass a)
      (coefficientMass_nonneg a) hatom)

theorem fourth_moment_quantile_gap_mass_cube_simplified
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap κ : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hκ : 0 < κ) (hκ1 : κ < 1)
    (hatom : ∀ i, coefficientMass a i ≤ (1 - κ) * ∑ j, coefficientMass a j) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (1 - κ ^ 4 / 16384) * (∑ i, coefficientMass a i) ^ 3 := by
  refine (fourth_moment_quantile_gap_mass_cube ν frequency a hgap hsep hν hκ hκ1 hatom).trans ?_
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg
    (Finset.sum_nonneg fun i _ => coefficientMass_nonneg a i) _)
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by linarith : (1 : ℝ) / 2 ≤ 1 - κ / 2) 2
  nlinarith [mul_nonneg (pow_nonneg hκ.le 4) (sub_nonneg.mpr hs)]

/-- Application of the dominant estimate to an actual finite Fourier remainder.
The two coefficient inequalities are supplied by the exponent-comparison step. -/
theorem finiteFourier_dominant_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap b r : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hzero : ∀ i, gap / 4 ≤ |frequency i|)
    (hb : 0 ≤ b) (hsmall : b ≤ 1 / 64) (hr : 0 < r) (hrupper : r ≤ 3 / 2)
    (hsecond : ∑ i, ‖a i‖ ^ 2 ≤ b ^ 2)
    (hfourth : (∑ i, coefficientMass a i) ^ 3 ≤ 2 * b ^ 4) :
    (∫ t, ‖1 + finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (1 + b ^ r) ^ (4 / r) := by
  apply dominant_fourth_moment_bound (continuous_finiteFourierSum frequency a).aestronglyMeasurable
    (Finset.sum_nonneg fun i _ => norm_nonneg (a i)) (finiteFourierSum_bound frequency a)
    (integral_finiteFourierSum_eq_zero ν frequency a hν hzero) hb hsmall hr hrupper
  · rw [integral_finiteFourierSum_second ν frequency a hgap hsep hν]
    exact hsecond
  · exact (fourth_moment_le_mass_cube ν frequency a hgap hsep hν).trans hfourth

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
