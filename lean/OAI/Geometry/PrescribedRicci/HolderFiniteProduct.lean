import Mathlib
import OAI.Geometry.PrescribedRicci.InterpolationExponents
import OAI.Geometry.PrescribedRicci.LpPowerBounds

namespace OAI

/-! Holder Finite Product. -/

section

 
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical
namespace TameInterpolation
variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

lemma lpNorm_finite_prod {ι : Type*} (s : Finset ι) (f : ι → Y → ℝ) (p : ι → ℝ≥0∞)
    (hf : ∀ i ∈ s, MemLp (f i) (p i) μ) :
    lpNorm (fun x => ∏ i ∈ s, f i x) (∑ i ∈ s, (p i)⁻¹)⁻¹ μ ≤
      ∏ i ∈ s, lpNorm (f i) (p i) μ := by
  induction s using Finset.cons_induction with
  | empty =>
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [lpNorm_const, hμ]
  | cons i s hi ih =>
    have hfi : MemLp (f i) (p i) μ := hf i (Finset.mem_cons_self ..)
    have hfs : ∀ a ∈ s, MemLp (f a) (p a) μ := fun a ha => hf a (Finset.mem_cons_of_mem ha)
    have hprod := MemLp.fun_prod hfs
    let : ENNReal.HolderTriple (p i) (∑ a ∈ s, (p a)⁻¹)⁻¹ (∑ a ∈ Finset.cons i s hi, (p a)⁻¹)⁻¹ :=
      ⟨by simp only [inv_inv,Finset.sum_cons]⟩
    simp only [Finset.prod_cons]
    exact (lpNorm_mul_le hfi hprod).trans (mul_le_mul_of_nonneg_left (ih hfs) lpNorm_nonneg)

lemma exponent_sum_inverse {ι : Type*} (s : Finset ι) (j : ι → ℕ) (m : ℕ)
    (hm : 0 < m) (hs : ∑ i ∈ s, j i = m) :
    (∑ i ∈ s, (exponent m (j i))⁻¹)⁻¹ = 2 := by
  simp only [exponent,inv_inv]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),← Finset.sum_div,← Nat.cast_sum,hs]
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have he : (m:ℝ)/(2*(m:ℝ)) = 1/2 := by field_simp
  rw [he,← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 1/2)]
  norm_num
end TameInterpolation

end
end

end OAI
