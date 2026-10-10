import OAI.MeasureTheory.Falconer.Estimates.GeometricRegularFiber
import OAI.MeasureTheory.Falconer.Geometry.ProjectionPowerBudget

namespace OAI

/-! Explicit polynomial loss for the regular fiber selected from coarse pencils. -/
namespace Falconer

theorem planarCriticalConstant_upper (N : ℕ) {t : ℝ} (ht : t ≤ 2) :
    planarCriticalConstant N t ≤ 21*((N:ℝ)+1) := by
  have h2 : (2:ℝ)^t ≤ 4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht
      _ = 4 := by norm_num
  unfold planarCriticalConstant
  calc
    _ ≤ 1+4*(1+(N:ℝ)*4) := by gcongr
    _ ≤ _ := by have := Nat.cast_nonneg (α := ℝ) N; linarith

theorem regular_fiber_constant_eq (N : ℕ) (s t K M m L : ℝ)
    (P : Finset (Space 2)) (hm : m ≠ 0) (hP : (P.card:ℝ) ≠ 0) :
    4*pencilEnergyCutoff N s t K M m P*(4*L/(m*(P.card:ℝ)))^2*(2:ℝ)^(t-s) =
      1024*(K*(80*(1/(2:ℝ)^N))^s*M)^2*(L/m^2)^2*
        (1+2*K*planarCriticalConstant N t)*(1+K*planarPotentialConstant s t)*
        (2:ℝ)^(t-s) := by
  unfold pencilEnergyCutoff pencilEnergyBudget pencilMomentBudget
  field_simp
  ring

theorem regular_fiber_constant_upper (N : ℕ) {κ s t K M m L D : ℝ}
    (hκ : 0 < κ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : t ≤ 2) (hgap : κ ≤ t-s)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hm : 0 < m) (hL : 0 ≤ L)
    (hD : 1 ≤ D) (hKD : K ≤ D)
    (hMD : M ≤ D/(1/(2:ℝ)^N)^s)
    (hmD : 1/(D*(1/(2:ℝ)^N)^s) ≤ m)
    (hLD : L ≤ D/((1/(2:ℝ)^N)^s)^2)
    (P : Finset (Space 2)) (hP : P.Nonempty) :
    4*pencilEnergyCutoff N s t K M m P*(4*L/(m*(P.card:ℝ)))^2*(2:ℝ)^(t-s) ≤
      (1127219200*(1+projectionGapConstant κ))*((N:ℝ)+1)*D^12 := by
  have hst : s < t := by linarith only [hκ,hgap]
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  have hδs : 0 < (1/(2:ℝ)^N)^s := Real.rpow_pos_of_pos hδ _
  have h80 : (80:ℝ)^s ≤ 80 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 80) hs1
  have hA : K*(80*(1/(2:ℝ)^N))^s*M ≤ 80*D^2 := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hδ.le]
    calc
      _ ≤ D*(80*(1/(2:ℝ)^N)^s)*(D/(1/(2:ℝ)^N)^s) := by gcongr
      _ = _ := by field_simp
  have hB : L/m^2 ≤ D^3 := by
    calc
      _ ≤ (D/((1/(2:ℝ)^N)^s)^2)/(1/(D*(1/(2:ℝ)^N)^s))^2 := by
        gcongr
      _ = _ := by field_simp
  have hcrit0 : 0 ≤ planarCriticalConstant N t := by
    unfold planarCriticalConstant
    positivity
  have hpot0 : 0 ≤ planarPotentialConstant s t := (planarPotentialConstant_pos hst).le
  have hcrit : 1+2*K*planarCriticalConstant N t ≤ 43*D*((N:ℝ)+1) := by
    calc
      _ ≤ 1+2*D*(21*((N:ℝ)+1)) := by
        gcongr
        exact planarCriticalConstant_upper N ht
      _ ≤ _ := by
        have hh : 1 ≤ D*((N:ℝ)+1) := by
          calc
            1 ≤ D := hD
            _ ≤ D*((N:ℝ)+1) := by nlinarith only [mul_nonneg hD0.le (Nat.cast_nonneg (α := ℝ) N)]
        nlinarith only [hh]
  have hH : 0 < projectionGapConstant κ := projectionGapConstant_pos hκ
  have hpot : 1+K*planarPotentialConstant s t ≤ (1+projectionGapConstant κ)*D := by
    calc
      _ ≤ 1+D*projectionGapConstant κ := by
        gcongr
        exact planarPotentialConstant_gap hκ hs1 hgap
      _ ≤ _ := by nlinarith only [hD]
  have h2 : (2:ℝ)^(t-s) ≤ 4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by linarith only [ht,hs])
      _ = 4 := by norm_num
  rw [regular_fiber_constant_eq N s t K M m L P (ne_of_gt hm)
    (ne_of_gt (Nat.cast_pos.mpr hP.card_pos))]
  calc
    _ ≤ 1024*(80*D^2)^2*(D^3)^2*(43*D*((N:ℝ)+1))*
        ((1+projectionGapConstant κ)*D)*4 := by
      gcongr
    _ = _ := by ring

end Falconer

end OAI
