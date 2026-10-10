import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevNonlinearity

namespace OAI

/-! # Uniform polynomial bounds on Sobolev balls -/

namespace DefocusingNLS

/-- The bilinear difference estimate in the Sobolev algebra. -/
theorem norm_sobolevProduct_sub_le (k : ℝ) (hk : 6 < k)
    (u v u' v' : FourierL2) :
    ‖sobolevProduct k hk u v - sobolevProduct k hk u' v'‖ ≤
      ‖sobolevBilinearProduct k hk‖ *
        (‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖) := by
  let B := sobolevBilinearProduct k hk
  have heq : B u v - B u' v' = B (u - u') v + B u' (v - v') := by
    simp only [map_sub, sub_apply]
    abel
  change ‖B u v - B u' v'‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖B (u - u') v‖ + ‖B u' (v - v')‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖u - u'‖ * ‖v‖ + ‖B‖ * ‖u'‖ * ‖v - v'‖ :=
      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ = _ := by ring

/-- Polynomial bounds are uniform on every norm ball, including in infinite dimension. -/
theorem exists_sobolevOddPower_ball_bounds (k : ℝ) (hk : 6 < k) (m : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧
      (∀ f : FourierL2, ‖f‖ ≤ R → ‖sobolevOddPower k hk m f‖ ≤ A) ∧
      (∀ f g : FourierL2, ‖f‖ ≤ R → ‖g‖ ≤ R →
        ‖sobolevOddPower k hk m f - sobolevOddPower k hk m g‖ ≤ K * ‖f - g‖) := by
  let C := ‖sobolevBilinearProduct k hk‖
  have hC : 0 ≤ C := norm_nonneg (sobolevBilinearProduct k hk)
  have hprod (u v : FourierL2) : ‖sobolevProduct k hk u v‖ ≤ C * ‖u‖ * ‖v‖ :=
    (sobolevBilinearProduct k hk).le_opNorm₂ u v
  have hconj (f g : FourierL2) :
      ‖fourierConjugate f - fourierConjugate g‖ = ‖f - g‖ := by
    change ‖sobolevConjugation f - sobolevConjugation g‖ = _
    rw [← map_sub, sobolevConjugation_apply, fourierConjugate_norm]
  induction m with
  | zero =>
    exact ⟨R, 1, hR, by positivity, (by simp [sobolevOddPower]),
      (by intros; simp [sobolevOddPower])⟩
  | succ m ih =>
    obtain ⟨A, K, hA, hK, hbound, hlip⟩ := ih
    let M : FourierL2 → FourierL2 := fun f =>
      sobolevProduct k hk (sobolevOddPower k hk m f) (fourierConjugate f)
    let B := C * A * R
    let L := C * (K * R + A)
    have hB : 0 ≤ B := by positivity
    have hL : 0 ≤ L := by positivity
    have hMbound (f : FourierL2) (hf : ‖f‖ ≤ R) : ‖M f‖ ≤ B := by
      calc
        _ ≤ C * ‖sobolevOddPower k hk m f‖ * ‖fourierConjugate f‖ := hprod _ _
        _ ≤ B := by
          simp only [fourierConjugate_norm]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hbound f hf) hC) hf
            (norm_nonneg f) (mul_nonneg hC hA)
    have hMlip (f g : FourierL2) (hf : ‖f‖ ≤ R) (hg : ‖g‖ ≤ R) :
        ‖M f - M g‖ ≤ L * ‖f - g‖ := by
      calc
        _ ≤ C * (‖sobolevOddPower k hk m f - sobolevOddPower k hk m g‖ *
            ‖fourierConjugate f‖ + ‖sobolevOddPower k hk m g‖ *
              ‖fourierConjugate f - fourierConjugate g‖) :=
          norm_sobolevProduct_sub_le k hk _ _ _ _
        _ ≤ C * ((K * ‖f - g‖) * R + A * ‖f - g‖) := by
          rw [fourierConjugate_norm, hconj]
          gcongr
          · exact hlip f g hf hg
          · exact hbound g hg
        _ = L * ‖f - g‖ := by dsimp [L]; ring
    refine ⟨C * B * R, C * (L * R + B), by positivity, by positivity, ?_, ?_⟩
    · intro f hf
      change ‖sobolevProduct k hk (M f) f‖ ≤ _
      exact (hprod _ _).trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (hMbound f hf) hC) hf (norm_nonneg f)
        (mul_nonneg hC hB))
    · intro f g hf hg
      change ‖sobolevProduct k hk (M f) f - sobolevProduct k hk (M g) g‖ ≤ _
      calc
        _ ≤ C * (‖M f - M g‖ * ‖f‖ + ‖M g‖ * ‖f - g‖) :=
          norm_sobolevProduct_sub_le k hk _ _ _ _
        _ ≤ C * ((L * ‖f - g‖) * R + B * ‖f - g‖) := by
          gcongr
          · exact hMlip f g hf hg
          · exact hMbound g hg
        _ = _ := by ring

end DefocusingNLS

end OAI
