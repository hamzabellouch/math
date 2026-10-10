import OAI.NumberTheory.CubicMoment.Estimates.SparseFourthMoment

namespace OAI

/-! The repeated-prime discrepancy is negligible in the balanced
exceptional family. Both its fourth moment and the number of rows are
derived from the actual finite supports. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma balanced_pair_card (P : Finset (Eisenstein × Eisenstein)) {L : ℝ}
    (hL : 0 ≤ L) (hP : ∀ p ∈ P, primary p.1 ∧ primary p.2 ∧
      norm p.1 ≤ L ∧ norm p.2 ≤ L) : (P.card:ℝ) ≤ 324*L^2 := by
  have hsub : P ⊆ (nonzeroNormBall L).product (nonzeroNormBall L) := by
    intro p hp
    obtain ⟨hp₁,hp₂,hN₁,hN₂⟩ := hP p hp
    exact Finset.mem_product.mpr ⟨mem_nonzeroNormBall.mpr ⟨hN₁,primary_ne_zero hp₁⟩,
      mem_nonzeroNormBall.mpr ⟨hN₂,primary_ne_zero hp₂⟩⟩
  calc
    (P.card:ℝ) ≤ ((nonzeroNormBall L).card:ℝ)^2 := by
      have h := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
      simpa only [Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul,pow_two] using h
    _ ≤ (18*L)^2 := pow_le_pow_left₀ (by positivity) (nonzeroNormBall_card_le hL) 2
    _ = _ := by ring

private lemma balanced_error_power_step {Y c C A m₂ m₄ : ℝ}
    (hY : 1 ≤ Y) (hc : 0 < c) (hc₁ : c ≤ 1) (hC : 0 < C)
    (hm₂ : 0 ≤ m₂)
    (hCS : m₂^2 ≤ (324*Y^(2/3+2*(c/16)))*m₄)
    (hfourth : m₄ ≤ C*Y^(c/8)*(Y^(2*(2/3+2*(c/16)))+Y^2)*Y^(2-c)*A^4) :
    m₂ ≤ Real.sqrt (648*C)*Y^(7/3-c/4)*A^2 := by
  have hY0 : 0 < Y := by linarith
  have hshort : Y^(2*(2/3+2*(c/16))) ≤ Y^2 := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  have hsq : m₂^2 ≤ 648*C*Y^(14/3-c/2)*A^4 := by
    calc
      _ ≤ (324*Y^(2/3+2*(c/16)))*
          (C*Y^(c/8)*(Y^(2*(2/3+2*(c/16)))+Y^2)*Y^(2-c)*A^4) :=
        hCS.trans (mul_le_mul_of_nonneg_left hfourth (by positivity))
      _ ≤ (324*Y^(2/3+2*(c/16)))*(C*Y^(c/8)*(2*Y^2)*Y^(2-c)*A^4) := by
        gcongr
        linarith
      _ = 648*C*Y^(14/3-3*c/4)*A^4 := by
        rw [← Real.rpow_two]
        have hp : Y^(2/3+2*(c/16))*Y^(c/8)*Y^(2:ℝ)*Y^(2-c) = Y^(14/3-3*c/4) := by
          rw [← Real.rpow_add hY0,← Real.rpow_add hY0,← Real.rpow_add hY0]
          congr 1
          ring
        calc
          _ = 648*C*(Y^(2/3+2*(c/16))*Y^(c/8)*Y^(2:ℝ)*Y^(2-c))*A^4 := by ring
          _ = _ := by rw [hp]
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hY (by linarith)) (by positivity))
          (by positivity)
  apply (sq_le_sq₀ hm₂ (by positivity)).mp
  have hp : (Y^(7/3-c/4))^2 = Y^(14/3-c/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
    congr 1
    ring
  have he : (Real.sqrt (648*C)*Y^(7/3-c/4)*A^2)^2 = 648*C*Y^(14/3-c/2)*A^4 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),hp]
    ring
  exact hsq.trans_eq he.symm

theorem repeatedPrime_balanced_second_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ),
      1 ≤ Y → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ Y^c < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧
        norm p.1 ≤ Y^(1/3+c/16) ∧ norm p.2 ≤ Y^(1/3+c/16)) →
      ∀ (ℓ : ℤ) (u : ℝ) (ν : Eisenstein → ℂ),
      (∀ b ∈ orderedConvolutionSupport S, ‖ν b‖ ≤ 1) →
      (∑ p ∈ P, ‖∑ b ∈ orderedConvolutionSupport S,
        squarefreeConvolutionError S w b *
          (theta ℓ b * normTwist u b * ν b) * mixedCubic p.1 p.2 b‖^2) ≤
        C*Y^(7/3-c/4)*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  obtain ⟨C,hC,hfourth⟩ := primeConvolutionError_twisted_fourth_moment
    (ι := ι) hHuxley (show 0 < c/8 by positivity)
  refine ⟨Real.sqrt (648*C),Real.sqrt_pos.mpr (by positivity),?_⟩
  intro S w M Y hY hM hS hprod hw P hP ℓ u ν hν
  have hY0 : 0 < Y := by linarith
  let q : ℝ := 2/3+2*(c/16)
  have hQ : 1 ≤ Y^q := Real.one_le_rpow hY (by dsimp [q]; positivity)
  have hpair : ∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Y^q := by
    intro p hp
    refine ⟨(hP p hp).1,?_⟩
    unfold pairConductor
    rw [norm_mul_eq]
    have h := mul_le_mul (hP p hp).2.1 (hP p hp).2.2 (norm_nonneg _) (by positivity)
    convert h using 1
    rw [← Real.rpow_add hY0]
    congr 1
    dsimp [q]
    ring
  have hcard : (P.card:ℝ) ≤ 324*Y^q := by
    have h := balanced_pair_card P (by positivity : 0 ≤ Y^(1/3+c/16))
      (fun p hp => ⟨(hP p hp).1.1,(hP p hp).1.2.1,(hP p hp).2⟩)
    have hp : (Y^(1/3+c/16))^2 = Y^q := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
      congr 1
      dsimp [q]
      ring
    exact h.trans_eq (by rw [hp])
  let f (p : Eisenstein × Eisenstein) := ∑ b ∈ orderedConvolutionSupport S,
    squarefreeConvolutionError S w b * (theta ℓ b * normTwist u b * ν b) * mixedCubic p.1 p.2 b
  have hCS : (∑ p ∈ P, ‖f p‖^2)^2 ≤ (324*Y^q)*∑ p ∈ P, ‖f p‖^4 :=
    (second_moment_sq_le_card_fourth P f).trans (mul_le_mul_of_nonneg_right hcard
      (Finset.sum_nonneg (fun _ _ => pow_nonneg (_root_.norm_nonneg _) _)))
  have hf := hfourth S w M Y c (Y^q) hY hQ hM hS hprod hw P hpair ℓ u ν hν
  have hfour : (∑ p ∈ P, ‖f p‖^4) ≤ C*Y^(c/8)*(Y^(2*q)+Y^2)*Y^(2-c)*
      (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^4 := by
    have hq : q ≤ 1 := by dsimp [q]; linarith
    have hweight : (Y^q)^(c/8) ≤ Y^(c/8) := by
      rw [← Real.rpow_mul hY0.le]
      apply Real.rpow_le_rpow_of_exponent_le hY
      nlinarith
    have hp : (Y^q)^2 = Y^(2*q) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
      congr 1
      ring
    rw [hp] at hf
    exact hf.trans (by gcongr)
  exact balanced_error_power_step hY hc hc₁ hC
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hCS hfour

end CubicFirstMoment

end

end OAI
