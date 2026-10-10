import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

namespace OAI

/-! # Scalar dyadic selection for comparable positive displacements

The arithmetic is independent of dimension, angular energy and distance-set
estimates.
-/

namespace PlanarFalconer
open Set Metric

 theorem exists_displacement_depth {d : ℝ} (hd : 0 < d) :
    ∃ n : ℤ, (2:ℝ)^(-(n:ℝ)-1) < d ∧ d ≤ (2:ℝ)^(-(n:ℝ)) := by
  obtain ⟨m,hm⟩ := exists_mem_Ioc_zpow hd (by norm_num : (1:ℝ) < 2)
  refine ⟨-(m+1),?_,?_⟩
  · have he : -((-(m+1):ℤ):ℝ)-1 = (m:ℝ) := by push_cast; ring
    rw [he,Real.rpow_intCast]
    exact hm.1
  · have he : -((-(m+1):ℤ):ℝ) = ((m+1:ℤ):ℝ) := by push_cast; ring
    rw [he,Real.rpow_intCast]
    exact hm.2

 theorem comparable_displacement_depth {d₁ d₂ : ℝ} {a h : ℕ}
    (hupper : max d₁ d₂ ≤ 2*(2:ℝ)^(-(a:ℝ)))
    (hfar : 16*(2:ℝ)^(-(h:ℝ)) < max d₁ d₂)
    (hc₁ : max d₁ d₂ ≤ 2*d₁) (hc₂ : max d₁ d₂ ≤ 2*d₂) :
    ∃ b : ℕ, a+9 ≤ b ∧ b ≤ h+5 ∧
      (256*(2:ℝ)^(-(b:ℝ)) < d₁ ∧ d₁ ≤ 1024*(2:ℝ)^(-(b:ℝ))) ∧
      (256*(2:ℝ)^(-(b:ℝ)) < d₂ ∧ d₂ ≤ 1024*(2:ℝ)^(-(b:ℝ))) := by
  have hd : 0 < max d₁ d₂ := (by positivity : 0 < 16*(2:ℝ)^(-(h:ℝ))).trans hfar
  obtain ⟨n,hnlo,hnhi⟩ := exists_displacement_depth hd
  have haexp : (2:ℝ)^(-(n:ℝ)-1) < (2:ℝ)^(1-(a:ℝ)) := by
    have he : (2:ℝ)^(1-(a:ℝ)) = 2*(2:ℝ)^(-(a:ℝ)) := by
      rw [sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ) < 2),Real.rpow_one]
    rw [he]
    exact hnlo.trans_le hupper
  have haR := (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp haexp
  have hhExp : (2:ℝ)^(4-(h:ℝ)) < (2:ℝ)^(-(n:ℝ)) := by
    have he : (2:ℝ)^(4-(h:ℝ)) = 16*(2:ℝ)^(-(h:ℝ)) := by
      rw [sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      norm_num
    rw [he]
    exact hfar.trans_le hnhi
  have hhR := (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp hhExp
  have haZ : (a:ℤ)-2 < n := by exact_mod_cast (show (a:ℝ)-2 < (n:ℝ) by linarith)
  have hhZ : n < (h:ℤ)-4 := by exact_mod_cast (show (n:ℝ) < (h:ℝ)-4 by linarith)
  have hb0 : 0 ≤ n+10 := by omega
  let b := (n+10).toNat
  have hbZ : (b:ℤ) = n+10 := Int.toNat_of_nonneg hb0
  have hbR : (b:ℝ) = (n:ℝ)+10 := by exact_mod_cast hbZ
  have hpow : (2:ℝ)^(-(n:ℝ)) = 1024*(2:ℝ)^(-(b:ℝ)) := by
    rw [hbR,show -(n:ℝ) = 10+(-((n:ℝ)+10)) by ring,
      Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    norm_num
  have hhalf : (2:ℝ)^(-(n:ℝ)-1) = 512*(2:ℝ)^(-(b:ℝ)) := by
    rw [hbR,show -(n:ℝ)-1 = 9+(-((n:ℝ)+10)) by ring,
      Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    norm_num
  rw [hpow] at hnhi
  rw [hhalf] at hnlo
  refine ⟨b,?_,?_,?_,?_⟩
  · omega
  · omega
  · exact ⟨by linarith, (le_max_left _ _).trans hnhi⟩
  · exact ⟨by linarith, (le_max_right _ _).trans hnhi⟩

end PlanarFalconer

end OAI
