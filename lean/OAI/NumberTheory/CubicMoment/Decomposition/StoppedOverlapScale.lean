import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBilinearOverlap

namespace OAI

/-! Quantitative overlap saving with the genuine active roughness threshold.
The outer energy and inner bounded coefficient have separate constants. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem bounded_active_model_overlap_log_saving (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) {A b z R M E : ℝ}
    (hA : 0 < A) (hb : 0 < b) (hz : 0 < z) (hR : 0 < R)
    (_hM : 0 ≤ M) (hE : 0 ≤ E) (k d : ℕ)
    (hP : ∀ a ∈ P, primary a ∧ A ≤ norm a ∧ norm a ≤ 2*A)
    (hB : ∀ a ∈ B, primary a ∧ Squarefree a ∧ b/2 ≤ norm a ∧ norm a ≤ b)
    (hα : (∑ a ∈ P, ‖α a‖^2) ≤ E*A*z^d)
    (hβ : ∀ a ∈ B, ‖β a‖ ≤ M)
    (hn : ∀ a ∈ B, β a ≠ 0 → ((primaryPrimeFactors a).card:ℝ) ≤ z/Real.log 2)
    (hrough : ∀ a ∈ B, β a ≠ 0 → ∀ p ∈ primaryPrimeFactors a, R ≤ norm p)
    (hthreshold : z^(d+1+2*k) ≤ R) :
    ‖modelOverlap P B α β u‖ ≤
      Real.sqrt (cStar^2*36*18*2*(36*M^2)*E/Real.log 2)*
        A^(5/6:ℝ)*b^(5/6:ℝ)/z^k := by
  let L := b/2
  have hL : 0 < L := by dsimp [L]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (B.card:ℝ) ≤ 36*L := by
    exact (primary_support_card_le B hb.le
      (fun a ha => ⟨(hB a ha).1,(hB a ha).2.2.2⟩)).trans_eq (by dsimp [L]; ring)
  have henergy : (∑ a ∈ B, ‖β a‖^2) ≤ (36*M^2)*L*z^0 := by
    calc
      _ ≤ ∑ _a ∈ B, M^2 := Finset.sum_le_sum (fun a ha =>
        pow_le_pow_left₀ (_root_.norm_nonneg _) (hβ a ha) 2)
      _ = (B.card:ℝ)*M^2 := by simp
      _ ≤ (36*L)*M^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg M)
      _ = _ := by simp only [pow_zero]; ring
  have hraw := active_modelOverlap_norm_sq_le P B α β u hA hL
    (show 0 ≤ 2*A by positivity) hR (show 0 ≤ z/Real.log 2 by positivity)
    (fun a ha => ⟨primary_ne_zero (hP a ha).1,(hP a ha).2⟩)
    (fun a ha => ⟨(hB a ha).1,(hB a ha).2.1,(hB a ha).2.2.1⟩) hn hrough
  let C := cStar^2*36*18*2*(36*M^2)*E/Real.log 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlog : z^(d+1)/R ≤ 1/z^(2*k) := by
    apply (div_le_div_of_nonneg_left (pow_nonneg hz.le _) (pow_pos hz _) hthreshold).trans_eq
    rw [pow_add z (d+1) (2*k)]
    field_simp
  have hsq : ‖modelOverlap P B α β u‖^2 ≤ C*A^(5/3:ℝ)*b^(5/3:ℝ)/z^(2*k) := by
    calc
      _ ≤ (cStar*A^(-1/6:ℝ)*L^(-1/6:ℝ))^2*
          ((36*L*(E*A*z^d))*((z/Real.log 2)*(18*(2*A)/R)*((36*M^2)*L*z^0))) := by
        apply hraw.trans
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul (mul_le_mul hcard hα (by positivity) (by positivity))
          (mul_le_mul_of_nonneg_left henergy (by positivity)) (by positivity) (by positivity)
      _ = C*A^(5/3:ℝ)*L^(5/3:ℝ)*(z^(d+1)/R) := by
        rw [model_overlap_scale hA hL]
        simp only [Nat.add_zero,pow_succ]
        dsimp [C]
        ring
      _ ≤ C*A^(5/3:ℝ)*L^(5/3:ℝ)*(1/z^(2*k)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ C*A^(5/3:ℝ)*b^(5/3:ℝ)*(1/z^(2*k)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow hL.le (by dsimp [L]; linarith) (by norm_num)
      _ = _ := by ring
  exact norm_le_bilinear_of_square hC hA hb hz k hsq

end CubicFirstMoment

end

end OAI
