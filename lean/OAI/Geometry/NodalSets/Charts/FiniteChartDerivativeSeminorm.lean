import OAI.Geometry.NodalSets.Charts.FiniteChartDerivativeSize

namespace OAI

namespace Yau.Geometry
open Set
open scoped ContDiff
noncomputable section
variable {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma finiteChartDerivativeSize_zero (P : Finset I) {Q : Set E} (hQ : IsCompact Q) (J : ℕ) :
    finiteChartDerivativeSize P Q J (fun _ _ ↦ (0:F)) = 0 := by
  apply le_antisymm
  · exact finiteChartDerivativeSize_le P Q J _ le_rfl (by intros; simp)
  · exact finiteChartDerivativeSize_nonneg P hQ J _ (fun _ _ ↦ contDiff_const)

lemma finiteChartDerivativeSize_smul_le (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (r : ℝ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    finiteChartDerivativeSize P Q J (fun p x ↦ r • f p x) ≤ ‖r‖*finiteChartDerivativeSize P Q J f := by
  apply finiteChartDerivativeSize_le _ _ _ _
    (mul_nonneg (norm_nonneg r) (finiteChartDerivativeSize_nonneg P hQ J f hf))
  intro p hp i hi x hx
  rw [iteratedFDeriv_const_smul_apply'
    ((hf p hp).of_le (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_le_finiteChartDerivativeSize P hQ J f hf p hp i hi x hx) (norm_nonneg r)

lemma finiteChartDerivativeSize_smul (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (r : ℝ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    finiteChartDerivativeSize P Q J (fun p x ↦ r • f p x) = ‖r‖*finiteChartDerivativeSize P Q J f := by
  by_cases hr : r=0
  · subst r
    simpa using finiteChartDerivativeSize_zero (F := F) P hQ J
  · apply le_antisymm (finiteChartDerivativeSize_smul_le P hQ J r f hf)
    have h := finiteChartDerivativeSize_smul_le P hQ J r⁻¹ (fun p x ↦ r • f p x)
      (fun p hp ↦ (hf p hp).const_smul r)
    simp only [smul_smul,inv_mul_cancel₀ hr,one_smul] at h
    have hh := mul_le_mul_of_nonneg_left h (norm_nonneg r)
    simpa only [norm_inv,← mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hr),one_mul] using hh

lemma finiteChartDerivativeSize_mono_order (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    {J K : ℕ} (hJK : J ≤ K) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    finiteChartDerivativeSize P Q J f ≤ finiteChartDerivativeSize P Q K f := by
  apply finiteChartDerivativeSize_le _ _ _ _ (finiteChartDerivativeSize_nonneg P hQ K f hf)
  intro p hp i hi x hx
  exact norm_le_finiteChartDerivativeSize P hQ K f hf p hp i (hi.trans hJK) x hx

end
end Yau.Geometry

end OAI
