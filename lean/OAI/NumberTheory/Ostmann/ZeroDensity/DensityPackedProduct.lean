import OAI.NumberTheory.Ostmann.ZeroDensity.DensityCubicIntegrability

namespace OAI

/-! # The fourth-power bound for the actual detector product -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators Classical

 theorem density_packed_product_fourth :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ X → 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∀ {ι : Type} (S : Finset ι) (c : ι → PrimitiveComplexCharacter) (t : ι → ℝ),
      (∀ i ∈ S, (c i).modulus ≤ Q) → (∀ i ∈ S, |t i| ≤ T) →
      (∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∑ i ∈ S, ∫ v, densityCubicWeight (v - t i) *
        ‖(c i).L (densityVerticalPoint (1 / 2) v)‖ *
        ‖densityMollifier X (c i).character (densityVerticalPoint (1 / 2) v)‖) ^ 4 ≤
          C * S.card * ((Q : ℝ) ^ 2 * T) * ((X : ℝ) + (Q : ℝ) ^ 2 * T) ^ 2 *
            (Real.log ((Q : ℝ) * T)) ^ 6 * (1 + Real.log X) ^ 2 := by
  obtain ⟨C4, hC4, hfourth⟩ := density_packed_fourth_moment
  obtain ⟨C2, hC2, hsecond⟩ := density_packed_mollifier_mean
  let W0 := 1 + ∫ v, densityCubicWeight v
  have hW0 : 0 < W0 := by
    have hn : 0 ≤ ∫ v : ℝ, densityCubicWeight v :=
      integral_nonneg (fun v => densityCubicWeight_nonneg v)
    dsimp [W0]
    linarith
  refine ⟨W0 * C4 * C2 ^ 2, by positivity, ?_⟩
  intro X Q hX hQ T hT ι S c t hc ht hs
  obtain ⟨hi4, hb4⟩ := hfourth Q hQ T hT S c t hc ht hs
  obtain ⟨hiM, hbM⟩ := hsecond X Q hX hQ T hT S c t hc ht hs
  let f := fun i v => ‖(c i).L (densityVerticalPoint (1 / 2) v)‖
  let g := fun i v => ‖densityMollifier X (c i).character (densityVerticalPoint (1 / 2) v)‖
  let w := fun i v => densityCubicWeight (v - t i)
  have hfc (i : ι) : Continuous (f i) := by
    have hl : Continuous (c i).L := continuous_iff_continuousAt.mpr (fun z => ((c i).L_analytic z).continuousAt)
    exact (hl.comp (by unfold densityVerticalPoint; fun_prop)).norm
  have hgc (i : ι) : Continuous (g i) := by
    have hm : Continuous (densityMollifier X (c i).character) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      simpa only [zero_add] using (densityMollifier_shift_analytic (c i) X 0 z).continuousAt
    exact (hm.comp (by unfold densityVerticalPoint; fun_prop)).norm
  have hmixed (i : ι) (hi : i ∈ S) := density_cubic_mixed_integrable (f i) (g i)
    (hfc i) (hgc i) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (t i) (hi4 i hi) (hiM i hi)
  have hpow := density_finite_product_fourth S w f g
    (fun _ _ _ => densityCubicWeight_nonneg _)
    (fun i _ => densityCubicWeight_shift_integrable (t i))
    (fun i hi => (hmixed i hi).1) hi4 hiM (fun i hi => (hmixed i hi).2)
  have hweight : (∑ i ∈ S, ∫ v, w i v) ≤ (S.card : ℝ) * W0 := by
    dsimp [w]
    simp_rw [densityCubicWeight_shift_integral]
    simp only [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    dsimp [W0]
    linarith
  have hf4non : 0 ≤ ∑ i ∈ S, ∫ v, w i v * f i v ^ 4 :=
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun v => mul_nonneg (densityCubicWeight_nonneg _) (by positivity)))
  have hmnon : 0 ≤ ∑ i ∈ S, ∫ v, w i v * g i v ^ 2 :=
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun v => mul_nonneg (densityCubicWeight_nonneg _) (sq_nonneg _)))
  have hWnon : 0 ≤ (S.card : ℝ) * W0 := by positivity
  have hWM := mul_le_mul hweight hb4 hf4non hWnon
  have hMsq := pow_le_pow_left₀ hmnon hbM 2
  apply hpow.trans
  calc
    _ ≤ ((S.card : ℝ) * W0) *
        (C4 * ((Q : ℝ) ^ 2 * T) * (Real.log ((Q : ℝ) * T)) ^ 6) *
        (C2 * ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log X)) ^ 2 :=
      mul_le_mul hWM hMsq (sq_nonneg _) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
