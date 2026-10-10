import OAI.Analysis.AncientFlat.Regularity.LowerJet

namespace OAI
noncomputable section
namespace ParabolicInterpolation
lemma small_scale_power (n : ℕ) (hn : 1≤n) (d q α : ℝ)
    (hd : 0≤d) (hq : 0<q) (hdq : d≤q) (hα : 0≤α) (hα1 : α≤1) :
    d^n≤q^n/q^α*d^α := by
  have hratio : 0≤d/q := div_nonneg hd hq.le
  have hr1 : d/q≤1 := (div_le_one hq).mpr hdq
  have hp := Real.rpow_le_rpow_of_exponent_ge' hratio hr1 hα
    (hα1.trans (by exact_mod_cast hn : (1:ℝ)≤(n:ℝ)))
  rw [Real.rpow_natCast,div_pow] at hp
  calc
    d^n=q^n*(d^n/q^n) := by field_simp
    _≤q^n*(d/q)^α := mul_le_mul_of_nonneg_left hp (pow_nonneg hq.le _)
    _=q^n/q^α*d^α := by rw [Real.div_rpow hd hq.le]; ring
lemma le_scaled_holder_of_two_bounds (D B d q α : ℝ)
    (hB : 0≤B) (hd : 0≤d) (hq : 0<q) (hα : 0≤α) (hα1 : α≤1)
    (hDb : D≤2*B) (hDl : D≤B/q*d) :
    D≤2*B/q^α*d^α := by
  have hqa : 0<q^α := Real.rpow_pos_of_pos hq _
  by_cases hdq : d≤q
  · have hp := small_scale_power 1 le_rfl d q α hd hq hdq hα hα1
    simp only [pow_one] at hp
    calc
      D≤B/q*d := hDl
      _≤B/q*(q/q^α*d^α) := mul_le_mul_of_nonneg_left hp (by positivity)
      _=B/q^α*d^α := by field_simp
      _≤2*B/q^α*d^α := by gcongr; linarith
  · have hp : q^α≤d^α := Real.rpow_le_rpow hq.le (le_of_not_ge hdq) hα
    calc
      D≤2*B := hDb
      _=(2*B/q^α)*q^α := by field_simp
      _≤(2*B/q^α)*d^α := mul_le_mul_of_nonneg_left hp (by positivity)
end ParabolicInterpolation

end

end OAI
