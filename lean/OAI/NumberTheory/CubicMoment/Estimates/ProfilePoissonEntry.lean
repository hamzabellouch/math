import OAI.NumberTheory.CubicMoment.Estimates.PoissonProfileBudget
import OAI.NumberTheory.CubicMoment.Estimates.PoissonEntryDecay

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
open Set
namespace CubicFirstMoment.ProfileControl

theorem poisson_entry_decay (P : PoissonProfileBudget) (m : ℕ) (hm : m ≤ 47)
    (A L D J : ℝ) (hA : 0 < A) (hL : 0 < L) (hLD : L ≤ D) (hJ : 0 ≤ J)
    (a b h : Eisenstein) (ha : primary a) (hb : primary b)
    (hLa : L ≤ norm a) (haD : norm a ≤ D) (hLb : L ≤ norm b) (hbD : norm b ≤ D)
    (hJh : J ≤ norm h) :
    ‖(A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a P.V A h‖ ≤
      (A/(9*L))*P.cost/(1+A*J/(27*D^2))^m := by
  let C := P.cost
  have hC : 0 < C := P.cost_pos
  have hdecay := P.radial_le hm
  have hD : 0 < D := hL.trans_le hLD
  have hh0 : 0 ≤ norm h := norm_nonneg h
  have hN : 0 < norm (b*a) := norm_pos_of_ne_zero (mul_ne_zero (primary_ne_zero hb) (primary_ne_zero ha))
  have hupper : norm (b*a) ≤ D^2 := by
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul hbD haD (norm_nonneg a) hD.le
  have hlower : L^2 ≤ norm (b*a) := by
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul hLb hLa hL.le (norm_nonneg b)
  have hsqrt : L ≤ Real.sqrt (norm (b*a)) := (Real.le_sqrt hL.le hN.le).mpr hlower
  have harg : A*J/(27*D^2) ≤ A*norm h/(27*norm (b*a)) := by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hJh hA.le) (by positivity)).trans
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have ht : 0 ≤ A*norm h/(27*norm (b*a)) := by positivity
  have hdec := hdecay _ ht
  have hrad : ‖radialDualProfile P.V (A*norm h/(27*norm (b*a)))‖ ≤ C/(1+A*J/(27*D^2))^m := by
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+A*J/(27*D^2)) m)).mpr
    have hh := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity)
        (add_le_add (le_rfl : (1:ℝ) ≤ 1) harg) m)
      (_root_.norm_nonneg (radialDualProfile P.V (A*norm h/(27*norm (b*a)))))
    nlinarith
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (A/(9*L))*(C/(1+A*J/(27*D^2))^m) :=
      mul_le_mul (div_le_div_of_nonneg_left hA.le (by positivity) (by nlinarith))
        ((gramDualTerm_norm_le_radial ha hb P.V hA.le h).trans hrad)
        (_root_.norm_nonneg _) (by positivity)
    _ = _ := by ring

end CubicFirstMoment.ProfileControl

end

end OAI
