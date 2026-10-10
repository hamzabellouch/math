import OAI.Analysis.LipschitzHilbert.Estimates.VariationSum
import OAI.Analysis.LipschitzHilbert.Estimates.VariationScalar

namespace OAI

/-! Perturbing finite variation by a short-scale sequence. -/

noncomputable section

namespace LipschitzHilbert

theorem cubicVariation_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → E) (N : ℕ) : cubicVariation (fun n => -F n) N = cubicVariation F N := by
  have heq : (fun n => -F n) = fun n => (-1 : ℝ) • F n := by funext n; simp
  rw [heq, cubicVariation, finiteCubicVariation_smul]
  norm_num [cubicVariation]

theorem cubicVariation_add_le {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (N : ℕ) : cubicVariation (fun n => F n + G n) N ≤
      cubicVariation F N + cubicVariation G N := finiteCubicVariation_add_rpow F G N

theorem abs_cubicVariation_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℕ → E) (N : ℕ) : |cubicVariation F N - cubicVariation G N| ≤
      cubicVariation (fun n => F n - G n) N := by
  have hFG : (fun n => G n + (F n - G n)) = F := by funext n; abel
  have hGF : (fun n => F n + (G n - F n)) = G := by funext n; abel
  have hneg : (fun n => G n - F n) = fun n => -(F n - G n) := by funext n; abel
  have h1 := cubicVariation_add_le G (fun n => F n - G n) N
  rw [hFG] at h1
  have h2 := cubicVariation_add_le F (fun n => G n - F n) N
  rw [hGF, hneg, cubicVariation_neg] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_cubicVariation_add_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S L : ℕ → E) (N : ℕ) :
    |cubicVariation (fun n => S n + L n) N - cubicVariation L N| ≤ cubicVariation S N := by
  have h := abs_cubicVariation_sub_le (fun n => S n + L n) L N
  simpa only [add_sub_cancel_right] using h

end LipschitzHilbert

end

end OAI
