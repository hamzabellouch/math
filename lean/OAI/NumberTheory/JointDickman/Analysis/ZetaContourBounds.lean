import OAI.NumberTheory.JointDickman.Analysis.ZetaPoleBranch
import PrimeNumberTheoremAnd.ZetaBounds

namespace OAI

/-! # Bounds for zeta on the finite Perron contour -/
namespace JointDickman
open Set Complex

theorem zetaPole_compact_bound : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, ‖s‖ ≤ 6 → s ≠ 1 → ‖riemannZeta s‖ ≤ C/‖s-1‖ := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) 6).exists_bound_of_continuousOn
    zetaPoleFactor_differentiable.continuous.continuousOn
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun s hs hs1 => ?_⟩
  have hbound := hC s (by simpa only [Metric.mem_closedBall,dist_zero_right] using hs)
  rw [zetaPoleFactor_eq hs1,norm_mul] at hbound
  apply (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))).mpr
  calc
    _ = ‖s-1‖*‖riemannZeta s‖ := mul_comm _ _
    _ ≤ C := hbound
    _ ≤ max C 1 := le_max_left _ _

theorem zeta_fractional_power_high_bound : ∃ A C : ℝ,
    A ∈ Ioc 0 (1/2) ∧ 0 < C ∧
    ∀ (z σ t : ℝ), 0 ≤ z → z ≤ 1 → 3 < |t| → σ ∈ Icc (1-A/Real.log |t|) 2 →
      ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I)‖^z ≤ C*|t|^(1/2:ℝ) := by
  obtain ⟨A,hA,C,hC,hb⟩ := ZetaUpperBnd
  refine ⟨A,max 1 (2*C),hA,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro z σ t hz hz1 ht hσ
  have ht1 : 1 ≤ |t| := by linarith
  have hp : 1 ≤ |t|^(1/2:ℝ) := Real.one_le_rpow ht1 (by norm_num)
  by_cases hn : ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I)‖ ≤ 1
  · calc
      _ ≤ 1 := Real.rpow_le_one (norm_nonneg _) hn hz
      _ ≤ |t|^(1/2:ℝ) := hp
      _ ≤ max 1 (2*C)*|t|^(1/2:ℝ) := by
        exact le_mul_of_one_le_left (Real.rpow_nonneg (abs_nonneg _) _) (le_max_left _ _)
  · calc
      _ ≤ ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I)‖ := Real.rpow_le_self_of_one_le (le_of_not_ge hn) hz1
      _ ≤ C*Real.log |t| := hb σ t ht hσ
      _ ≤ C*(|t|^(1/2:ℝ)/(1/2)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div (abs_nonneg _) (by norm_num)) hC.le
      _ = (2*C)*|t|^(1/2:ℝ) := by ring
      _ ≤ max 1 (2*C)*|t|^(1/2:ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _)

theorem zeta_left_contour_bound : ∃ A C : ℝ,
    A ∈ Ioc 0 (1/2) ∧ 0 < C ∧
    ∀ (δ T : ℝ), 0 < δ → δ ≤ 1/4 → 4 ≤ T → δ ≤ A/Real.log T →
      ∀ t : ℝ, |t| ≤ T → ‖riemannZeta (((1-δ:ℝ):ℂ)+(t:ℂ)*I)‖ ≤ C/δ := by
  obtain ⟨A,hA,C₁,hC₁,hb⟩ := ZetaUpperBnd
  obtain ⟨C₀,hC₀,hcompact⟩ := zetaPole_compact_bound
  refine ⟨A,C₀+C₁,hA,add_pos hC₀ hC₁,?_⟩
  intro δ T hδ hδ4 hT hδA t htT
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hδlog : δ*Real.log T ≤ 1 := by
    have h := (le_div_iff₀ hlogT).mp hδA
    linarith [hA.2]
  by_cases ht : |t| ≤ 3
  · have hn : ‖(((1-δ:ℝ):ℂ)+(t:ℂ)*I)‖ ≤ 6 := by
      have h := Complex.norm_le_abs_re_add_abs_im (((1-δ:ℝ):ℂ)+(t:ℂ)*I)
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,
        sub_zero,add_zero,add_im,mul_im,mul_one,zero_add] at h
      rw [abs_of_nonneg (by linarith : 0 ≤ 1-δ)] at h
      linarith
    have hs : (((1-δ:ℝ):ℂ)+(t:ℂ)*I) ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
        sub_zero,add_zero,one_re] at hr
      linarith
    have hd : δ ≤ ‖(((1-δ:ℝ):ℂ)+(t:ℂ)*I)-1‖ := by
      have h := Complex.abs_re_le_norm ((((1-δ:ℝ):ℂ)+(t:ℂ)*I)-1)
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
        sub_zero,add_zero,one_re,sub_sub_cancel_left,abs_neg,abs_of_pos hδ] at h
      exact h
    calc
      _ ≤ C₀/‖(((1-δ:ℝ):ℂ)+(t:ℂ)*I)-1‖ := hcompact _ hn hs
      _ ≤ C₀/δ := div_le_div_of_nonneg_left hC₀.le hδ hd
      _ ≤ (C₀+C₁)/δ := div_le_div_of_nonneg_right (by linarith) hδ.le
  · have ht3 : 3 < |t| := lt_of_not_ge ht
    have hlogt : 0 < Real.log |t| := Real.log_pos (by linarith)
    have hlogs : Real.log |t| ≤ Real.log T := Real.log_le_log (by linarith) htT
    have hd : δ ≤ A/Real.log |t| := hδA.trans
      (div_le_div_of_nonneg_left hA.1.le hlogt hlogs)
    calc
      _ ≤ C₁*Real.log |t| := hb (1-δ) t ht3 ⟨by linarith,by linarith⟩
      _ ≤ C₁*Real.log T := mul_le_mul_of_nonneg_left hlogs hC₁.le
      _ ≤ C₁/δ := by
        apply (le_div_iff₀ hδ).mpr
        nlinarith
      _ ≤ (C₀+C₁)/δ := div_le_div_of_nonneg_right (by linarith) hδ.le

end JointDickman

end OAI
