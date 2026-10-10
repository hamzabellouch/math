import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.OrderedAngularAssignmentsSublist

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set Metric
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
theorem angularDerivativeND_bound (T : V →L[ℝ] V) (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : V → ℂ) (A : ℝ) (s : ℕ), ContDiff ℝ ∞ b → 1 ≤ A →
      (∀ j ≤ m+1, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ C*A^(j+s)) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (angularDerivativeND T b) w‖ ≤ D*A^(j+(s+1)) := by
  obtain ⟨M,hM,hMb⟩ := compact_contDiffOn_derivative_bound isOpen_univ
    (isCompact_sphere (0:V) 1) (subset_univ _) T.contDiff.contDiffOn m
  refine ⟨2^m*C*M,by positivity,?_⟩
  intro b A s hb hA hderiv j hj w hw
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hh := norm_iteratedFDeriv_clm_apply (N := ∞) (n := j) (hb.fderiv_right (by simp)) T.contDiff w
    (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))
  change ‖iteratedFDeriv ℝ j (angularDerivativeND T b) w‖ ≤ _ at hh
  apply hh.trans
  have hsum : (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)) = 2^j := by
    exact_mod_cast Nat.sum_range_choose j
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i:ℝ) * (C*A^(j+(s+1))) * M := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := by simpa using Finset.mem_range.mp hi
      rw [norm_iteratedFDeriv_fderiv]
      gcongr
      · exact (hderiv (i+1) (by omega) w hw).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (by omega)) hC)
      · simpa only [iteratedFDerivWithin_univ] using
          hMb (j-i) (by omega) w (by simpa [mem_sphere,dist_zero_right] using hw)
    _ = 2^j*C*M*A^(j+(s+1)) := by rw [← Finset.sum_mul,← Finset.sum_mul,hsum]; ring
    _ ≤ 2^m*C*M*A^(j+(s+1)) := by gcongr; norm_num

omit [FiniteDimensional ℝ V] in
lemma sphere_derivative_const_mul_bound (c : ℂ) {b : V → ℂ} (hb : ContDiff ℝ ∞ b)
    {D A : ℝ} {s m : ℕ}
    (hbound : ∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ D*A^(j+s)) :
    ∀ j ≤ m, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (fun w => c*b w) w‖ ≤ (‖c‖*D)*A^(j+s) := by
  intro j hj w hw
  change ‖iteratedFDeriv ℝ j (fun w => c • b w) w‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((hb.of_le (show (j:ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt),norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hbound j hj w hw) (norm_nonneg c)

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
