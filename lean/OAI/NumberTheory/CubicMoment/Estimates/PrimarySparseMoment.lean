import OAI.NumberTheory.CubicMoment.Estimates.IdealDivisorPower
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerBalanced

namespace OAI

/-! Sparse coefficient energy in the balanced conductor region. The pair
multiplicity is bounded using actual primary divisors, with no restriction
on the number of prime bases. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_pair_fiber_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Finset Eisenstein) (Y : ℝ), 1 ≤ Y →
      (∀ b ∈ B, primary b ∧ norm b ≤ Y) → ∀ n ∈ productSupport B,
      (((B.product B).filter (fun z => z.1*z.2 = n)).card:ℝ) ≤ C*Y^ε := by
  obtain ⟨C,hC,hbound⟩ := primary_divisor_card_small_power
    (show 0 < ε/2 by positivity)
  refine ⟨C,hC,?_⟩
  intro B Y hY hB n hn
  obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp hn
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
  have hn0 : n ≠ 0 := by
    rw [← he]
    exact mul_ne_zero (primary_ne_zero (hB a ha).1) (primary_ne_zero (hB b hb).1)
  have hnN : norm n ≤ Y^2 := by
    rw [← he,norm_mul_eq,pow_two]
    exact mul_le_mul (hB a ha).2 (hB b hb).2 (norm_nonneg _) (by linarith)
  calc
    _ ≤ ((B.filter (fun a => a ∣ n)).card:ℝ) :=
      Nat.cast_le.mpr (primary_pair_fiber_le_divisors B (fun b hb => (hB b hb).1) n)
    _ ≤ C*norm n^(ε/2) := hbound B (fun b hb => (hB b hb).1) n hn0
    _ ≤ C*(Y^2)^(ε/2) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hnN (by positivity)) hC.le
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ Y)]
      congr 2
      ring

theorem primary_mixed_fourth_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q Y : ℝ), 1 ≤ Q → 1 ≤ Y →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (B : Finset Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ b ∈ B, primary b ∧ norm b ≤ Y) → ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^4) ≤
        C*Q^ε*(Q^2+Y^2)*Y^ε*(∑ b ∈ B, ‖v b‖^2)^2 := by
  obtain ⟨C,hC,hfourth⟩ := ordinary_mixed_fourth_moment hHuxley hε
  obtain ⟨K,hK,hfiber⟩ := primary_pair_fiber_power hε
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro Q Y hQ hY P B hP hB v
  exact (hfourth Q Y hQ hY P B hP
    (fun b hb => ⟨primary_ne_zero (hB b hb).1,(hB b hb).2⟩)
    (K*Y^ε) (hfiber B Y hY hB) v).trans_eq (by ring)

private lemma balancedPrimary_power {Y θ C E m₂ m₄ : ℝ}
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

/-- The sparse coefficient energy and the primary divisor bound
suffice for the actual balanced mixed-character second moment. -/
theorem primary_balanced_sparse_moment
    (hHuxley : HuxleyAdditiveLargeSieve) {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y E : ℝ), 1 ≤ Y → 0 ≤ E →
      ∀ B : Finset Eisenstein,
      (∀ b ∈ B, primary b ∧ norm b ≤ Y) →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧
        norm p.1 ≤ Y^(1/3+θ/16) ∧ norm p.2 ≤ Y^(1/3+θ/16)) →
      ∀ v : Eisenstein → ℂ, (∑ b ∈ B, ‖v b‖^2) ≤ E*Y^(1-θ) →
      (∑ p ∈ P, ‖∑ b ∈ B, v b*mixedCubic p.1 p.2 b‖^2) ≤
        C*Y^(7/3-θ/2)*E := by
  obtain ⟨C,hC,hfourth⟩ := primary_mixed_fourth_moment hHuxley
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
  exact balancedPrimary_power hY hθ hC hE
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hCS hfour

end CubicFirstMoment

end

end OAI
