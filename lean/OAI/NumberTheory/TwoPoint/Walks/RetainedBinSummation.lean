import OAI.NumberTheory.TwoPoint.Bounds.ActualRetainedBin
import OAI.NumberTheory.TwoPoint.Bounds.PaddingBinMassTotal

namespace OAI

/-! Sum the retained bin estimates and divide by the retained harmonic
mass. No extra factor is hidden in the mass normalization. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma retained_bin_sum_normalize (bins : Finset ℤ) (C : ℤ → ℂ)
    (S V S₀ L l R ε : ℝ) (hS : 0 < S) (hV : 0 < V) (hL : 0 < L)
    (hS₀ : S * V / 2 ≤ S₀)
    (hC : ∀ j ∈ bins, ‖C j‖ ≤ 3 * l ^ 2 * S * R / L + 3 * ε) :
    ‖∑ j ∈ bins, C j‖ / S₀ ≤
      (6 * bins.card * l ^ 2 * R) / (L * V) + (6 * bins.card * ε) / (S * V) := by
  have hp : 0 < S * V / 2 := by positivity
  have hs : ‖∑ j ∈ bins, C j‖ ≤ bins.card * (3 * l ^ 2 * S * R / L + 3 * ε) := by
    calc
      _ ≤ ∑ j ∈ bins, ‖C j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ bins, (3 * l ^ 2 * S * R / L + 3 * ε) := sum_le_sum hC
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  calc
    _ ≤ ‖∑ j ∈ bins, C j‖ / (S * V / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hp hS₀
    _ ≤ (bins.card * (3 * l ^ 2 * S * R / L + 3 * ε)) / (S * V / 2) :=
      div_le_div_of_nonneg_right hs hp.le
    _ = _ := by field_simp; ring

lemma retained_bin_sum_mass_lower (bins : Finset ℤ) (C : ℤ → ℂ)
    (S V S₀ L l R ε W : ℝ) (J : ℕ)
    (hS : 1 ≤ S) (hW : 1 ≤ W) (hV : W ^ J ≤ V) (hL : 0 < L)
    (hS₀ : S * V / 2 ≤ S₀) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hC : ∀ j ∈ bins, ‖C j‖ ≤ 3 * l ^ 2 * S * R / L + 3 * ε) :
    ‖∑ j ∈ bins, C j‖ / S₀ ≤
      (6 * bins.card * l ^ 2 / L) * (R / W ^ J) + 6 * bins.card * ε := by
  have hWp : 0 < W := by linarith
  have hVone : 1 ≤ V := (one_le_pow₀ hW).trans hV
  have hSV : 1 ≤ S * V := by nlinarith
  have hb := retained_bin_sum_normalize bins C S V S₀ L l R ε
    (by linarith) (by linarith) hL hS₀ hC
  apply hb.trans
  have hfirst : (6 * bins.card * l ^ 2 * R) / (L * V) ≤
      (6 * bins.card * l ^ 2 / L) * (R / W ^ J) := by
    calc
      _ ≤ (6 * bins.card * l ^ 2 * R) / (L * W ^ J) := by
        gcongr
      _ = _ := by ring
  have hsecond : (6 * bins.card * ε) / (S * V) ≤ 6 * bins.card * ε :=
    div_le_self (by positivity) hSV
  exact add_le_add hfirst hsecond

end TwoPointCorrelations

end OAI
