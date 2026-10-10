import OAI.Analysis.PureInfiniteness.CutSupport
import OAI.Analysis.WeakInfiniteness.MatrixCutToolkit

namespace OAI

/-! Exact return formulas for the nonunital spectral partition in KR02
Lemma 7.6. The square-root column stays supported after taking a fixed cut. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma cut_mul_sqrt_of_support {f g : A} (hf : IsSelfAdjoint f) (hg : 0 ≤ g)
    (hfg : f * g = g) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    MainGap.cut f δ * CFC.sqrt g = (1 - δ) • CFC.sqrt g := by
  apply cut_mul_of_mul_eq hf _ hδ0 hδ1
  exact left_identity_on_hereditary f g hg.isSelfAdjoint hfg
    (sqrt_mem_hereditary g g hg.isSelfAdjoint (self_mem_hereditary g hg) hg)

lemma supported_cut_return {f g : A} (hf : IsSelfAdjoint f) (hg : 0 ≤ g)
    (hfg : f * g = g) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    star (CFC.sqrt g) * MainGap.cut f δ * CFC.sqrt g = (1 - δ) • g := by
  rw [mul_assoc, cut_mul_sqrt_of_support hf hg hfg hδ0 hδ1, mul_smul_comm,
    (CFC.sqrt_nonneg g).star_eq, CFC.sqrt_mul_sqrt_self g hg]

lemma supported_weighted_cut_return {f g : A} (hf : IsSelfAdjoint f) (hg : 0 ≤ g)
    (hfg : f * g = g) (c : ℂ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    star (CFC.sqrt g) * (c • MainGap.cut f δ) * CFC.sqrt g =
      (1 - δ) • (c • g) := by
  rw [mul_smul_comm, smul_mul_assoc, supported_cut_return hf hg hfg hδ0 hδ1,
    smul_comm]

lemma spectral_cut_column_return {J : Type*} [Fintype J]
    (f g : J → A) (hf : ∀ j, IsSelfAdjoint (f j)) (hg : ∀ j, 0 ≤ g j)
    (hfg : ∀ j, f j * g j = g j) (c : J → ℂ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (∑ j, star (CFC.sqrt (g j)) * (c j • MainGap.cut (f j) δ) * CFC.sqrt (g j)) =
      (1 - δ) • ∑ j, c j • g j := by
  simp_rw [supported_weighted_cut_return (hf _) (hg _) (hfg _) _ hδ0 hδ1]
  exact (Finset.smul_sum ..).symm

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_scaled_reconstruction_error (a b : A) (ε δ : ℝ)
    (hε : ‖b - a‖ ≤ ε) (hδ : 0 ≤ δ) :
    ‖(1 - δ) • b - a‖ ≤ ε + δ * (‖a‖ + ε) := by
  have hb : ‖b‖ ≤ ‖a‖ + ε := by
    have h := norm_le_norm_sub_add b a
    linarith
  have he : (1 - δ) • b - a = (b - a) - δ • b := by
    rw [sub_smul, one_smul]
    abel
  rw [he]
  calc
    _ ≤ ‖b - a‖ + ‖δ • b‖ := norm_sub_le _ _
    _ = ‖b - a‖ + δ * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]
    _ ≤ _ := add_le_add hε (mul_le_mul_of_nonneg_left hb hδ)

end WeakPureInfiniteness

end

end OAI
