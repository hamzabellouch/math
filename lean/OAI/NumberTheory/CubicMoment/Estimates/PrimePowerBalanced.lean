import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerMoments

namespace OAI

/-! The balanced second moment for sparse higher-prime-power errors. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

private lemma balancedPrimePower_power {Y θ C E m₂ m₄ : ℝ}
    (hY : 1 ≤ Y) (hθ : 0 < θ) (hC : 0 < C) (hE : 0 ≤ E) (hm₂ : 0 ≤ m₂)
    (hCS : m₂^2 ≤ (324*Y^(2/3+θ/8))*m₄)
    (hfourth : m₄ ≤ 2*C*Y^(4-15*θ/8)*E^2) :
    m₂ ≤ Real.sqrt (648*C)*Y^(7/3-θ/2)*E := by
  have hY0 : 0 < Y := by linarith
  have hp : Y^(2/3+θ/8)*Y^(4-15*θ/8) = Y^(14/3-7*θ/4) := by
    rw [← Real.rpow_add hY0]
    congr 1
    ring
  have hs : m₂^2 ≤ 648*C*Y^(14/3-θ)*E^2 := by
    calc
      _ ≤ (324*Y^(2/3+θ/8))*(2*C*Y^(4-15*θ/8)*E^2) :=
        hCS.trans (mul_le_mul_of_nonneg_left hfourth (by positivity))
      _ = 648*C*(Y^(2/3+θ/8)*Y^(4-15*θ/8))*E^2 := by ring
      _ = 648*C*Y^(14/3-7*θ/4)*E^2 := by rw [hp]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg E)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  apply (sq_le_sq₀ hm₂ (by positivity)).mp
  have hp₂ : (Y^(7/3-θ/2))^2 = Y^(14/3-θ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
    congr 1
    ring
  have he : (Real.sqrt (648*C)*Y^(7/3-θ/2)*E)^2 = 648*C*Y^(14/3-θ)*E^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),hp₂]
  exact hs.trans_eq he.symm

/-- The sparse coefficient energy and the bounded number of prime bases
suffice for the actual balanced mixed-character second moment. -/
theorem boundedPrimeSupport_balanced_sparse_moment
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ℕ) {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y E : ℝ), 1 ≤ Y → 0 ≤ E →
      ∀ B : Finset Eisenstein,
      (∀ b ∈ B, primary b ∧ norm b ≤ Y ∧ (idealExponentOf b).support.card ≤ k) →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧
        norm p.1 ≤ Y^(1/3+θ/16) ∧ norm p.2 ≤ Y^(1/3+θ/16)) →
      ∀ v : Eisenstein → ℂ, (∑ b ∈ B, ‖v b‖^2) ≤ E*Y^(1-θ) →
      (∑ p ∈ P, ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^2) ≤
        C*Y^(7/3-θ/2)*E := by
  obtain ⟨C,hC,hfourth⟩ := boundedPrimeSupport_fourth_moment hHuxley k
    (show 0 < θ/16 by positivity)
  refine ⟨Real.sqrt (648*C),Real.sqrt_pos.mpr (by positivity),?_⟩
  intro Y E hY hE B hB P hP v hv
  have hY0 : 0 < Y := by linarith
  have hq : 2/3+θ/8 ≤ 1 := by linarith
  have hQ : 1 ≤ Y^(2/3+θ/8) := Real.one_le_rpow hY (by positivity)
  have hpair : ∀ p ∈ P, PrimarySquarefreePair p ∧
      norm (pairConductor p) ≤ Y^(2/3+θ/8) := by
    intro p hp
    refine ⟨(hP p hp).1,?_⟩
    unfold pairConductor
    rw [norm_mul_eq]
    have h := mul_le_mul (hP p hp).2.1 (hP p hp).2.2 (norm_nonneg _) (by positivity)
    convert h using 1
    rw [← Real.rpow_add hY0]
    congr 1
    ring
  have hcard : (P.card:ℝ) ≤ 324*Y^(2/3+θ/8) := by
    have h := balanced_pair_card P (by positivity : 0 ≤ Y^(1/3+θ/16))
      (fun p hp => ⟨(hP p hp).1.1,(hP p hp).1.2.1,(hP p hp).2⟩)
    have hp : (Y^(1/3+θ/16))^2 = Y^(2/3+θ/8) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
      congr 1
      ring
    exact h.trans_eq (by rw [hp])
  let f (p : Eisenstein × Eisenstein) := ∑ b ∈ B, v b*mixedCubic p.1 p.2 b
  have hCS : (∑ p ∈ P, ‖f p‖^2)^2 ≤
      (324*Y^(2/3+θ/8))*∑ p ∈ P, ‖f p‖^4 :=
    (second_moment_sq_le_card_fourth P f).trans (mul_le_mul_of_nonneg_right hcard
      (Finset.sum_nonneg (fun _ _ => pow_nonneg (_root_.norm_nonneg _) _)))
  have hf := hfourth (Y^(2/3+θ/8)) Y hQ hY P B hpair hB v
  have hw : (Y^(2/3+θ/8))^(θ/16) ≤ Y^(θ/16) := by
    rw [← Real.rpow_mul hY0.le]
    exact Real.rpow_le_rpow_of_exponent_le hY (by nlinarith)
  have hl : (Y^(2/3+θ/8))^2 ≤ Y^2 := by
    have hbase : Y^(2/3+θ/8) ≤ Y := by
      nth_rw 2 [← Real.rpow_one Y]
      exact Real.rpow_le_rpow_of_exponent_le hY hq
    exact pow_le_pow_left₀ (by positivity) hbase 2
  have he : (Y^(1-θ))^2 = Y^(2-2*θ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
    congr 1
    ring
  have hp : Y^(θ/16)*Y^(2:ℝ)*Y^(θ/16)*Y^(2-2*θ) = Y^(4-15*θ/8) := by
    rw [← Real.rpow_add hY0,← Real.rpow_add hY0,← Real.rpow_add hY0]
    congr 1
    ring
  have hfour : (∑ p ∈ P, ‖f p‖^4) ≤ 2*C*Y^(4-15*θ/8)*E^2 := by
    calc
      _ ≤ C*Y^(θ/16)*(2*Y^2)*Y^(θ/16)*(E*Y^(1-θ))^2 := by
        apply hf.trans
        gcongr
        linarith
      _ = 2*C*(Y^(θ/16)*Y^(2:ℝ)*Y^(θ/16)*Y^(2-2*θ))*E^2 := by
        rw [mul_pow,he,← Real.rpow_two Y]
        ring
      _ = _ := by rw [hp]
  exact balancedPrimePower_power hY hθ hC hE
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hCS hfour

/-- The actual sparse higher-prime-power support satisfies the balanced
second-moment saving, even when the underlying prime is small. -/
theorem primePower_balanced_second_moment (hHuxley : HuxleyAdditiveLargeSieve)
    (k : ℕ) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y A : ℝ), 1 ≤ Y → 0 ≤ A →
      ∀ B : Finset Eisenstein,
      (∀ b ∈ B, primary b ∧ (idealExponentOf b).support.card ≤ k) →
      B ⊆ largePrimePowerSupport Y c →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧
        norm p.1 ≤ Y^(1/3+c/128) ∧ norm p.2 ≤ Y^(1/3+c/128)) →
      ∀ v : Eisenstein → ℂ, (∀ b ∈ B, ‖v b‖ ≤ A) →
      (∑ p ∈ P, ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^2) ≤
        C*A^2*Y^(7/3-c/16) := by
  classical
  obtain ⟨C,hC,hbound⟩ := boundedPrimeSupport_balanced_sparse_moment hHuxley k
    (show 0 < c/8 by positivity) (show c/8 ≤ 1 by linarith)
  obtain ⟨K,hK,hcard⟩ := largePrimePowerSupport_card_bound
  have h₁ : c/8/16 = c/128 := by ring
  have h₂ : c/8/2 = c/16 := by ring
  simp only [h₁,h₂] at hbound
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro Y A hY hA B hB hsub P hP v hv
  have hY0 : 0 < Y := by linarith
  have hBs : ∀ b ∈ B, primary b ∧ norm b ≤ Y ∧ (idealExponentOf b).support.card ≤ k := by
    intro b hb
    have hball := mem_nonzeroNormBall.mp (Finset.mem_filter.mp (hsub hb)).1
    exact ⟨(hB b hb).1,hball.1,(hB b hb).2⟩
  have hE : (∑ b ∈ B, ‖v b‖^2) ≤ (K*A^2)*Y^(1-c/8) := by
    calc
      _ ≤ ∑ _b ∈ B, A^2 := Finset.sum_le_sum
        (fun b hb => pow_le_pow_left₀ (_root_.norm_nonneg _) (hv b hb) 2)
      _ = (B.card:ℝ)*A^2 := by simp
      _ ≤ ((largePrimePowerSupport Y c).card:ℝ)*A^2 :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub)) (sq_nonneg A)
      _ ≤ (K*Y^(1-c/8))*A^2 := mul_le_mul_of_nonneg_right (hcard Y c hY0) (sq_nonneg A)
      _ = _ := by ring
  exact (hbound Y (K*A^2) hY (by positivity) B hBs P hP v hE).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
