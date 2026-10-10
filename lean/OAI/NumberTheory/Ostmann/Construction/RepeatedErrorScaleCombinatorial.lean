import OAI.NumberTheory.Ostmann.Construction.RepeatedErrorScalePolynomial

namespace OAI

noncomputable section
namespace Ostmann.Construction.RepeatedErrorScale
open Filter

def tupleSize (k : ℕ) (L : ℝ) : ℕ := 2*Conclusion.bulkSize k L+4*k+8

theorem combinatorial_bound_eventually {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,
      (5000/L)^(2*Conclusion.bulkSize k L)*(tupleSize k L:ℝ)^(tupleSize k L)≤
        Real.exp ((29+2*Real.log (Conclusion.bulkScale k))*(Conclusion.bulkSize k L:ℝ)) := by
  let r : ℕ := 4*k+8
  filter_upwards [fixed_power_eventually hk r,
    (Conclusion.bulkSize_tendsto_atTop hk).eventually_ge_atTop (r:ℝ),
    eventually_ge_atTop (1:ℝ)] with L hpoly hm hL
  let m := Conclusion.bulkSize k L
  have hLpos : 0<L := by linarith
  have hz : 0<Conclusion.bulkScale k := by unfold Conclusion.bulkScale; positivity
  have hupper : (m:ℝ)≤Conclusion.bulkScale k*L :=
    (Conclusion.bulkSize_bounds k hLpos.le).2
  have hn : tupleSize k L=2*m+r := by dsimp [tupleSize,m,r]; omega
  have hnle : (tupleSize k L:ℝ)≤3*(m:ℝ) := by
    rw [hn]
    push_cast
    change (r:ℝ)≤(m:ℝ) at hm
    linarith
  have hbase : (5000/L)*(3*(m:ℝ))≤15000*Conclusion.bulkScale k := by
    have he : (5000/L)*(3*(m:ℝ))=15000*(m:ℝ)/L := by ring
    rw [he]
    apply (div_le_iff₀ hLpos).mpr
    nlinarith
  have hbaseexp : (5000/L)*(3*(m:ℝ))≤Real.exp (14+Real.log (Conclusion.bulkScale k)) := by
    apply hbase.trans
    rw [Real.exp_add,Real.exp_log hz]
    exact mul_le_mul_of_nonneg_right fifteen_thousand_le_exp hz.le
  calc
    _ ≤ (5000/L)^(2*m)*(3*(m:ℝ))^(tupleSize k L) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hnle _) (by positivity)
    _ = ((5000/L)*(3*(m:ℝ)))^(2*m)*(3*(m:ℝ))^r := by
      rw [hn,pow_add,mul_pow (5000/L) (3*(m:ℝ)) (2*m)]
      ring
    _ ≤ ((5000/L)*(3*(m:ℝ)))^(2*m)*Real.exp (m:ℝ) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ ≤ (Real.exp (14+Real.log (Conclusion.bulkScale k)))^(2*m)*Real.exp (m:ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbaseexp _) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      dsimp only [m]
      push_cast
      ring

end Ostmann.Construction.RepeatedErrorScale

end

end OAI
