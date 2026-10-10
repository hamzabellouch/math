import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowFirstBound

namespace OAI

/-! A composition estimate that retains the highest derivative linearly.
This is the quantitative form needed in the higher variational equations. -/

noncomputable section
open ContinuousLinearMap
open scoped ContDiff
namespace ContinuumCoulomb

theorem flow_composition_highest_bound (f g : Position → Position)
    (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g)
    (k : ℕ) (hk : k ≤ 3) (x : Position) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hgB : ∀ j, 1 ≤ j → j ≤ k+1 → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ B)
    (hfD : ∀ j, 1 ≤ j → j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ D^j) :
    ‖iteratedFDeriv ℝ (k+1) (g ∘ f) x‖ ≤
      B * ‖iteratedFDeriv ℝ (k+1) f x‖ +
        (k:ℝ) * 2^k * (k.factorial:ℝ) * B * D^(k+1) := by
  have hgf : fderiv ℝ (g ∘ f) =
      (fun y => compL ℝ Position Position Position (fderiv ℝ g (f y)) (fderiv ℝ f y)) := by
    funext y
    exact fderiv_comp y (hg.differentiable (by norm_num) (f y))
      (hf.differentiable (by norm_num) y)
  have hg' : ContDiff ℝ 3 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hf' : ContDiff ℝ 3 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hb := (compL ℝ Position Position Position).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (hg'.comp (hf.of_le (by norm_num))) hf' x
    (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk)
    (norm_compL_le ℝ Position Position Position)
  rw [←norm_iteratedFDeriv_fderiv, hgf]
  apply hb.trans
  rw [Finset.sum_range_succ']
  have hzero : (k.choose 0:ℝ) * ‖iteratedFDeriv ℝ 0 (fderiv ℝ g ∘ f) x‖ *
      ‖iteratedFDeriv ℝ (k-0) (fderiv ℝ f) x‖ ≤
      B * ‖iteratedFDeriv ℝ (k+1) f x‖ := by
    simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,norm_iteratedFDeriv_zero,
      Function.comp_apply,Nat.sub_zero,norm_iteratedFDeriv_fderiv]
    exact mul_le_mul_of_nonneg_right (by
      simpa only [norm_iteratedFDeriv_one] using hgB 1 le_rfl (by omega)) (norm_nonneg _)
  have hrest : ∑ i ∈ Finset.range k,
      (k.choose (i+1):ℝ) * ‖iteratedFDeriv ℝ (i+1) (fderiv ℝ g ∘ f) x‖ *
        ‖iteratedFDeriv ℝ (k-(i+1)) (fderiv ℝ f) x‖ ≤
      (k:ℝ) * (2^k * (k.factorial:ℝ) * B * D^(k+1)) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range k, 2^k * (k.factorial:ℝ) * B * D^(k+1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i+1 ≤ k := Finset.mem_range.mp hi
        have hb' : ‖iteratedFDeriv ℝ (i+1) (fderiv ℝ g ∘ f) x‖ ≤
            ((i+1).factorial:ℝ) * B * D^(i+1) := by
          apply norm_iteratedFDeriv_comp_le hg' (hf.of_le (by norm_num))
            (show (i+1:ℕ) ≤ (3:WithTop ℕ∞) by exact_mod_cast hi'.trans hk) x
          · intro j hj
            rw [norm_iteratedFDeriv_fderiv]
            exact hgB (j+1) (by omega) (by omega)
          · intro j hj hj'
            exact hfD j hj (hj'.trans hi')
        have ha : ‖iteratedFDeriv ℝ (k-(i+1)) (fderiv ℝ f) x‖ ≤ D^(k-(i+1)+1) := by
          rw [norm_iteratedFDeriv_fderiv]
          exact hfD _ (by omega) (by omega)
        have hc : (k.choose (i+1):ℝ) ≤ 2^k := by exact_mod_cast Nat.choose_le_two_pow k (i+1)
        have hfac : ((i+1).factorial:ℝ) ≤ (k.factorial:ℝ) := by
          exact_mod_cast Nat.factorial_le hi'
        calc
          _ ≤ (2^k) * (((i+1).factorial:ℝ) * B * D^(i+1)) * D^(k-(i+1)+1) := by
            exact mul_le_mul (mul_le_mul hc hb' (norm_nonneg _) (by positivity)) ha
              (norm_nonneg _) (by positivity)
          _ ≤ (2^k) * ((k.factorial:ℝ) * B * D^(i+1)) * D^(k-(i+1)+1) := by gcongr
          _ = _ := by
            have he : i+1 + (k-(i+1)+1) = k+1 := by omega
            rw [mul_assoc (2^k),mul_assoc _ (D^(i+1)),←pow_add,he]
            ring
      _ = _ := by simp
  exact (add_le_add hrest hzero).trans_eq (by ring)

end ContinuumCoulomb

end

end OAI
