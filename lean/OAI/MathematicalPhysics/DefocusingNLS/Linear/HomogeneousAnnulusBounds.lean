import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousAnnulusScaling

namespace OAI

/-! # Uniform Schwartz estimates for normalized annular profile pieces -/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousAnnulusPiece (a R : ℝ) (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    𝓢(E, ℂ) :=
  (hκ.mul_right (f' := normalizedPhysicalProfile a R Q)).toSchwartzMap
    (κ.smooth'.mul (normalizedPhysicalProfile_contDiff a R Q hQ))

@[simp] theorem homogeneousAnnulusPiece_apply (a R : ℝ) (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (x : E) :
    homogeneousAnnulusPiece a R κ hκ Q hQ x =
      κ x * ((R ^ (2 * a) : ℝ) • Q (R • x)) := rfl

theorem homogeneousAnnulusPiece_rescale (a R : ℝ) (hR : 0 < R) (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (y : E) :
    (R ^ (-2 * a) : ℝ) * homogeneousAnnulusPiece a R κ hκ Q hQ (R⁻¹ • y) =
      κ (R⁻¹ • y) * Q y := by
  have hy : R • (R⁻¹ • y) = y := by rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hc : R ^ (-2 * a) * R ^ (2 * a) = 1 := by
    rw [← Real.rpow_add hR]
    have he : -2 * a + 2 * a = 0 := by ring
    rw [he, Real.rpow_zero]
  rw [homogeneousAnnulusPiece_apply, hy]
  change (↑(R ^ (-2 * a)) : ℂ) * (κ (R⁻¹ • y) *
    ((↑(R ^ (2 * a)) : ℂ) * Q y)) = _
  calc
    _ = ((↑(R ^ (-2 * a)) : ℂ) * (↑(R ^ (2 * a)) : ℂ)) *
        (κ (R⁻¹ • y) * Q y) := by ring
    _ = _ := by rw [← Complex.ofReal_mul, hc]; simp

noncomputable def homogeneousAnnulusCutoffConstant (κ : 𝓢(E, ℂ)) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i κ

theorem homogeneousAnnulusCutoffConstant_nonneg (κ : 𝓢(E, ℂ)) (N : ℕ) :
    0 ≤ homogeneousAnnulusCutoffConstant κ N := by
  unfold homogeneousAnnulusCutoffConstant
  positivity

noncomputable def homogeneousAnnulusJetConstant (a : ℝ) (κ : 𝓢(E, ℂ)) (N : ℕ) : ℝ :=
  3 ^ N * homogeneousAnnulusCutoffConstant κ N * (1 / 2 : ℝ) ^ (-2 * a - (N : ℝ))

theorem homogeneousAnnulusJetConstant_nonneg (a : ℝ) (κ : 𝓢(E, ℂ)) (N : ℕ) :
    0 ≤ homogeneousAnnulusJetConstant a κ N := by
  unfold homogeneousAnnulusJetConstant
  exact mul_nonneg (mul_nonneg (by positivity)
    (homogeneousAnnulusCutoffConstant_nonneg κ N)) (Real.rpow_nonneg (by norm_num) _)

theorem homogeneousAnnulusPiece_jet_bound (a R D : ℝ) (ha : 0 < a)
    (hR : 0 < R) (hD : 0 ≤ D) (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ))
    (hκann : ∀ x ∈ tsupport (κ : E → ℂ), (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (N : ℕ)
    (hsymbol : ∀ n ≤ N, ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ)))
    (n : ℕ) (hn : n ≤ N) (x : E) :
    (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n
      (homogeneousAnnulusPiece a R κ hκ Q hQ) x‖ ≤
      homogeneousAnnulusJetConstant a κ N * D := by
  let B := D * (1 / 2 : ℝ) ^ (-2 * a - (N : ℝ))
  have hB : 0 ≤ B := mul_nonneg hD (Real.rpow_nonneg (by norm_num) _)
  by_cases hx : x ∈ tsupport (κ : E → ℂ)
  · have hxann := hκann x hx
    have hxs : x ≠ 0 := norm_pos_iff.mp (by linarith [hxann.1])
    have hj (j : ℕ) (hjN : j ≤ N) :
        ‖iteratedFDeriv ℝ j (normalizedPhysicalProfile a R Q) x‖ ≤ B := by
      apply normalizedPhysicalProfile_annulus_bound a R D ha hR hD Q hQ N j hjN x hxann.1
      exact hsymbol j hjN (R • x) (smul_ne_zero hR.ne' hxs)
    have hprod : ‖iteratedFDeriv ℝ n
        (homogeneousAnnulusPiece a R κ hκ Q hQ) x‖ ≤
        (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i κ) * B := by
      change ‖iteratedFDeriv ℝ n
        (fun y => κ y * normalizedPhysicalProfile a R Q y) x‖ ≤ _
      refine (norm_iteratedFDeriv_mul_le κ.smooth'
        (normalizedPhysicalProfile_contDiff a R Q hQ) x (by simp)).trans ?_
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _hi
      have hiN : n - i ≤ N := (Nat.sub_le n i).trans hn
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ κ i x)
          (Nat.cast_nonneg _))
        (hj (n - i) hiN) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))
    have hsum : (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i κ) ≤
        homogeneousAnnulusCutoffConstant κ N := by
      unfold homogeneousAnnulusCutoffConstant
      exact Finset.single_le_sum
        (f := fun j : ℕ => ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i κ)
        (fun j _ => by positivity)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    have hweight : (1 + ‖x‖) ^ N ≤ (3 : ℝ) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith [hxann.2]) _
    calc
      _ ≤ 3 ^ N * (homogeneousAnnulusCutoffConstant κ N * B) :=
        mul_le_mul hweight (hprod.trans (mul_le_mul_of_nonneg_right hsum hB))
          (norm_nonneg _) (by positivity)
      _ = _ := by unfold homogeneousAnnulusJetConstant B; ring
  · have hzero : iteratedFDeriv ℝ n
        (homogeneousAnnulusPiece a R κ hκ Q hQ) x = 0 := by
      by_contra hne
      have hm : x ∈ tsupport (fun y => κ y * normalizedPhysicalProfile a R Q y) :=
        support_iteratedFDeriv_subset n hne
      exact hx (tsupport_mul_subset_left hm)
    rw [hzero, norm_zero, mul_zero]
    exact mul_nonneg (homogeneousAnnulusJetConstant_nonneg a κ N) hD

end DefocusingNLS

end OAI
