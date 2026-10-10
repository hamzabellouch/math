import OAI.MeasureTheory.Falconer.Recursion.ProfileGeometryBudget

namespace OAI

/-! Convert the common geometric constants to powers with explicit exponents.
The chord error remains proportional to its own interval length. -/
namespace Falconer

theorem profile_geometry_power_budget {N K i j B : ℕ} (hi : i ≤ K) (hj : j ≤ K)
    {t A W u v w : ℝ} (ht : 0 ≤ t) (ht2 : t ≤ 2) (hA : 0 ≤ A) (hW : 1 ≤ W)
    (hWu : W ≤ (2:ℝ)^(u*(N:ℝ)))
    (hKv : (2:ℝ)^(6*K) ≤ (2:ℝ)^(v*(N:ℝ)))
    (hBw : 100000*(2:ℝ)^(2*B) ≤ (2:ℝ)^(w*(N:ℝ))) :
    (max 1 ((49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^t)*4^t)*
      (W*(2:ℝ)^(2*i+2*j))))*4^t ≤ (2:ℝ)^((u+v+w)*(N:ℝ)+A) ∧
    25*(49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A))) ≤ (2:ℝ)^((u+v+w)*(N:ℝ)+A) := by
  have hcost : 100000*W*(2:ℝ)^(6*K)*(2:ℝ)^A*(2:ℝ)^(2*B) ≤
      (2:ℝ)^((u+v+w)*(N:ℝ)+A) := by
    calc
      _ = (100000*(2:ℝ)^(2*B))*W*(2:ℝ)^(6*K)*(2:ℝ)^A := by ring
      _ ≤ (2:ℝ)^(w*(N:ℝ))*(2:ℝ)^(u*(N:ℝ))*(2:ℝ)^(v*(N:ℝ))*(2:ℝ)^A := by gcongr
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
  obtain ⟨hpoint,hcover⟩ := profile_geometry_costs hi hj ht ht2 hA hW
  exact ⟨hpoint.trans hcost,hcover.trans hcost⟩

theorem profile_normal_power_cost {N : ℕ} {q r A : ℝ}
    (hpoly : 640*((N:ℝ)+3) ≤ (2:ℝ)^(r*(N:ℝ))) :
    640*((2:ℝ)^(q*(N:ℝ)+A))^3*((N:ℝ)+3) ≤
      (2:ℝ)^((3*q+r)*(N:ℝ)+3*A) := by
  calc
    _ = (640*((N:ℝ)+3))*((2:ℝ)^(q*(N:ℝ)+A))^3 := by ring
    _ ≤ (2:ℝ)^(r*(N:ℝ))*((2:ℝ)^(q*(N:ℝ)+A))^3 :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      norm_num
      ring

theorem dyadic_power_below_normal_factor (D : ℕ) {s loss C : ℝ} (hC : 0 < C)
    (hcost : C ≤ (2:ℝ)^loss) :
    (2:ℝ)^(s*(D:ℝ)-loss) ≤ (1/(2:ℝ)^D)^(-s)/C := by
  rw [dyadic_inverse_power_eq,neg_neg,Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
  exact div_le_div_of_nonneg_left (by positivity) hC hcost

end Falconer

end OAI
