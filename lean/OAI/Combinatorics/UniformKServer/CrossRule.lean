import Mathlib
import OAI.Combinatorics.UniformKServer.AllocationMovement

namespace OAI

                                
section

/-! The two actual hysteresis crossings in the star outputs. In contrast to
 comparing with an unused old rule, these bounds use only the states that
 actually existed. The coefficient of parent variation stays exactly one. -/
namespace UniformKServer.AllocationOutputs
noncomputable section
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem holes_two_nonneg (R : ℝ) (ω : ι → ℝ) (o : ι) (hω : ∀ i, 0 ≤ ω i) (i : ι) :
    0 ≤ holesTwo R ω o i := by
  unfold holesTwo
  split_ifs
  · exact le_max_right _ _
  · exact hω i

theorem holes_two_total (R : ℝ) (ω : ι → ℝ) (o : ι) :
    (∑ i, holesTwo R ω o i)=max R (sideTotal ω o) := by
  rw [←sum_erase_add _ _ (mem_univ o)]
  have he : (∑ i ∈ univ.erase o, holesTwo R ω o i)=sideTotal ω o := by
    apply sum_congr rfl
    intro i hi
    simp only [holesTwo,ite_eq_right (ne_of_mem_erase hi)]
  rw [he]
  simp only [holesTwo,ite_true]
  rcases le_total R (sideTotal ω o) with h|h
  · rw [max_eq_right (sub_nonpos.mpr h),max_eq_right h,add_zero]
  · rw [max_eq_left (sub_nonneg.mpr h),max_eq_left h]
    ring

omit [DecidableEq ι] in
theorem nonnegative_movement (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    variation a b ≤ (∑ i, a i)+(∑ i, b i) := by
  rw [variation,←sum_add_distrib]
  apply sum_le_sum
  intro i _
  exact abs_le.mpr ⟨by linarith [ha i,hb i], by linarith [ha i,hb i]⟩

theorem side_scalar_bound (D W : ℝ) (w : ι → ℝ) (o : ι)
    (hD : 0 ≤ D) (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i ≤ W) :
    0 ≤ sideTotal (fun i => D*w i) o ∧ sideTotal (fun i => D*w i) o ≤ D*W := by
  unfold sideTotal
  refine ⟨sum_nonneg (fun i _ => mul_nonneg hD (hw i)), ?_⟩
  have hsum : (∑ i ∈ univ.erase o, w i) ≤ ∑ i, w i :=
    sum_le_sum_of_subset_of_nonneg (erase_subset o univ) (fun i _ _ => hw i)
  rw [←mul_sum]
  exact mul_le_mul_of_nonneg_left (hsum.trans hW) hD

theorem rule_two_eq_holes (d w : ι → ℝ) (q D : ℝ) (o : ι)
    (h : 0 ≤ sideTotal (fun i => D*w i) o) :
    ruleTwo d w q D o = fun i => d i-holesTwo (excess d q) (fun i => D*w i) o i := by
  funext i
  linarith [rule_two_holes d w q D o i h]

/-- I-to-II: the new D suffices, even though no old side vector was output. -/
theorem downcross (d₀ d₁ α₀ w₁ : ι → ℝ) (q₀ q₁ D₁ L W : ℝ) (o : ι)
    (hα : ∀ i, 0 ≤ α₀ i) (hsum : ∑ i, α₀ i=1)
    (hD : 0 ≤ D₁) (hw : ∀ i, 0 ≤ w₁ i) (hW : ∑ i, w₁ i ≤ W)
    (hR : excess d₁ q₁ ≤ L*D₁) :
    variation (ruleOne d₀ α₀ q₀) (ruleTwo d₁ w₁ q₁ D₁ o) ≤
      |q₁-q₀|+2*variation d₀ d₁+(2*L+W)*D₁ := by
  obtain ⟨hside,hside'⟩ := side_scalar_bound D₁ W w₁ o hD hw hW
  have hω (i : ι) : 0 ≤ D₁*w₁ i := mul_nonneg hD (hw i)
  have hm := nonnegative_movement (fun i => excess d₀ q₀*α₀ i)
    (holesTwo (excess d₁ q₁) (fun i => D₁*w₁ i) o)
    (fun i => mul_nonneg (excess_nonneg _ _) (hα i)) (holes_two_nonneg _ _ _ hω)
  rw [←mul_sum,hsum,mul_one,holes_two_total] at hm
  have ht : max (excess d₁ q₁) (sideTotal (fun i => D₁*w₁ i) o) ≤ excess d₁ q₁+D₁*W := by
    apply max_le
    · linarith [hside.trans hside']
    · linarith [excess_nonneg d₁ q₁]
  have hRdiff : excess d₀ q₀ ≤ excess d₁ q₁+|excess d₁ q₁-excess d₀ q₀| := by
    linarith [neg_le_abs (excess d₁ q₁-excess d₀ q₀)]
  have he := excess_difference d₀ d₁ q₀ q₁
  have hret := outputs_from_holes d₀ d₁ (fun i => excess d₀ q₀*α₀ i)
    (holesTwo (excess d₁ q₁) (fun i => D₁*w₁ i) o)
  rw [rule_two_eq_holes _ _ _ _ _ hside]
  change variation (fun i => d₀ i-excess d₀ q₀*α₀ i)
    (fun i => d₁ i-holesTwo (excess d₁ q₁) (fun i => D₁*w₁ i) o i) ≤ _
  nlinarith

/-- II-to-I: the new S plus held-D variation suffices, without evaluating
 the old simplex state as though Rule I had been in force there. -/
theorem upcross (d₀ d₁ w₀ α₁ : ι → ℝ) (q₀ q₁ D₀ D₁ S₁ L W : ℝ) (o : ι)
    (hα : ∀ i, 0 ≤ α₁ i) (hsum : ∑ i, α₁ i=1)
    (hD₀ : 0 ≤ D₀) (hw : ∀ i, 0 ≤ w₀ i) (hW : ∑ i, w₀ i ≤ W)
    (hR : excess d₁ q₁ ≤ L*S₁) (hSD : D₁ ≤ S₁/2) :
    variation (ruleTwo d₀ w₀ q₀ D₀ o) (ruleOne d₁ α₁ q₁) ≤
      |q₁-q₀|+2*variation d₀ d₁+(2*L+W/2)*S₁+W*|D₁-D₀| := by
  obtain ⟨hside,hside'⟩ := side_scalar_bound D₀ W w₀ o hD₀ hw hW
  have hW₀ : 0 ≤ W := (sum_nonneg fun i _ => hw i).trans hW
  have hω (i : ι) : 0 ≤ D₀*w₀ i := mul_nonneg hD₀ (hw i)
  have hm := nonnegative_movement (holesTwo (excess d₀ q₀) (fun i => D₀*w₀ i) o)
    (fun i => excess d₁ q₁*α₁ i) (holes_two_nonneg _ _ _ hω)
    (fun i => mul_nonneg (excess_nonneg _ _) (hα i))
  rw [holes_two_total,←mul_sum,hsum,mul_one] at hm
  have ht : max (excess d₀ q₀) (sideTotal (fun i => D₀*w₀ i) o) ≤ excess d₀ q₀+D₀*W := by
    apply max_le
    · linarith [hside.trans hside']
    · linarith [excess_nonneg d₀ q₀]
  have hRdiff : excess d₀ q₀ ≤ excess d₁ q₁+|excess d₁ q₁-excess d₀ q₀| := by
    linarith [neg_le_abs (excess d₁ q₁-excess d₀ q₀)]
  have hDdiff : D₀ ≤ D₁+|D₁-D₀| := by linarith [neg_le_abs (D₁-D₀)]
  have hDnew := mul_le_mul_of_nonneg_right hSD hW₀
  have hDold := mul_le_mul_of_nonneg_right hDdiff hW₀
  have he := excess_difference d₀ d₁ q₀ q₁
  have hret := outputs_from_holes d₀ d₁ (holesTwo (excess d₀ q₀) (fun i => D₀*w₀ i) o)
    (fun i => excess d₁ q₁*α₁ i)
  rw [rule_two_eq_holes _ _ _ _ _ hside]
  change variation (fun i => d₀ i-holesTwo (excess d₀ q₀) (fun i => D₀*w₀ i) o i)
    (fun i => d₁ i-excess d₁ q₁*α₁ i) ≤ _
  nlinarith

end
end UniformKServer.AllocationOutputs

end

end OAI
