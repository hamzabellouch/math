import Mathlib

namespace OAI

/-! Higher Jet Commutator. -/

section

 

noncomputable section
open Set Finset
open scoped ContDiff
namespace HigherJet
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma bilinear_derivative_bound_on (B : F →L[ℝ] G →L[ℝ] H)
    {U : Set E} (hU : IsOpen U) {f : E → F} {g : E → G}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : E} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖*∑ i ∈ range (m+1), (m.choose i : ℝ)*‖iteratedFDeriv ℝ i f x‖*
        ‖iteratedFDeriv ℝ (m-i) g x‖ := by
  have hb := B.norm_iteratedFDerivWithin_le_of_bilinear hf hg hU.uniqueDiffOn hx
    (show (m:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hx] using hb

lemma frozen_derivative_norm {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f y-f x) x‖ =
      if m=0 then 0 else ‖iteratedFDeriv ℝ m f x‖ := by
  by_cases hm : m=0
  · subst m
    simp
  · rw [ite_eq_right hm]
    change ‖iteratedFDeriv ℝ m (f - fun _ => f x) x‖ = _
    rw [iteratedFDeriv_sub_apply (g := fun _ => f x)
      (hf.of_le (show (m:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) contDiffAt_const,
      iteratedFDeriv_const_of_ne hm,Pi.zero_apply,sub_zero]

lemma frozen_product_jet_bound (B : F →L[ℝ] G →L[ℝ] H)
    {U : Set E} (hU : IsOpen U) {a : E → F} {v : E → G}
    (ha : ContDiffOn ℝ ∞ a U) (hv : ContDiffOn ℝ ∞ v U)
    {x : E} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => B (a y-a x) (v y)) x‖ ≤
      ‖B‖*∑ i ∈ range (m+1), (m.choose i : ℝ)*
        (if i=0 then 0 else ‖iteratedFDeriv ℝ i a x‖)*
        ‖iteratedFDeriv ℝ (m-i) v x‖ := by
  have hb := bilinear_derivative_bound_on B hU (f := fun y => a y-a x) (ha.sub contDiffOn_const) hv hx m
  simpa only [frozen_derivative_norm (ha.contDiffAt (hU.mem_nhds hx))] using hb

 

lemma frozen_product_tame_bound (B : F →L[ℝ] G →L[ℝ] H)
    {U : Set E} (hU : IsOpen U) {a : E → F} {v : E → G}
    (ha : ContDiffOn ℝ ∞ a U) (hv : ContDiffOn ℝ ∞ v U)
    {x : E} (hx : x ∈ U) (m : ℕ) {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hproducts : ∀ i, 0 < i → i ≤ m →
      ‖iteratedFDeriv ℝ i a x‖*‖iteratedFDeriv ℝ (m-i) v x‖ ≤ C*T) :
    ‖iteratedFDeriv ℝ m (fun y => B (a y-a x) (v y)) x‖ ≤
      ‖B‖*(2:ℝ)^m*C*T := by
  apply (frozen_product_jet_bound B hU ha hv hx m).trans
  have hb : (∑ i ∈ range (m+1), (m.choose i : ℝ)*
      (if i=0 then 0 else ‖iteratedFDeriv ℝ i a x‖)*
        ‖iteratedFDeriv ℝ (m-i) v x‖) ≤
      ∑ i ∈ range (m+1), (m.choose i : ℝ)*(C*T) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hi0 : i=0
    · simp only [hi0,ite_true,mul_zero,zero_mul]
      positivity
    · rw [ite_eq_right hi0,mul_assoc]
      exact mul_le_mul_of_nonneg_left (hproducts i (Nat.pos_of_ne_zero hi0)
        (Nat.le_of_lt_succ (mem_range.mp hi))) (Nat.cast_nonneg _)
  have he : (∑ i ∈ range (m+1), (m.choose i : ℝ)*(C*T)) = 2^m*(C*T) := by
    rw [← Finset.sum_mul]
    congr 1
    exact_mod_cast Nat.sum_range_choose m
  exact (mul_le_mul_of_nonneg_left (hb.trans_eq he) (norm_nonneg B)).trans_eq (by ring)
end HigherJet

end
end

end OAI
