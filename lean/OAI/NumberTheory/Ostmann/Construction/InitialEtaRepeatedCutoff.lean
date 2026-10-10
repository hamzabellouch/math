import OAI.NumberTheory.Ostmann.Construction.InitialEtaMinPrime
import OAI.NumberTheory.Ostmann.Construction.LevelZeroFrequencySupport
import OAI.NumberTheory.Ostmann.Construction.RepeatedPeriod

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialEta

theorem repeated_tuple_cutoff_of_log_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀i,(p i).Prime) (hn : ¬Function.Injective p)
    {X R Δ W : ℝ} (hX : 0<X) (hR : 0<R) (hmin : ∀i,R≤(p i:ℝ))
    (hlog : Real.log (∏i,p i:ℕ)≤Real.log X+Δ+W)
    (hinflation : Real.exp (Δ+W)<R) :
    ((∏q:↥(tupleDistinctPrimes p),(q:ℕ):ℕ):ℝ)/4<X := by
  have hM : 0<((∏i,p i:ℕ):ℝ) := by
    exact_mod_cast Finset.prod_pos (fun i (_ : i∈Finset.univ) => (hp i).pos)
  have hQ := repeated_distinct_product_le_div p (fun i => (hp i).one_le) hn hR hmin
  rw [← Nat.cast_prod] at hQ
  have hMx : ((∏i,p i:ℕ):ℝ)≤X*Real.exp (Δ+W) := by
    have h := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hM] at h
    calc
      _ ≤ Real.exp (Real.log X+Δ+W) := h
      _ = X*Real.exp (Δ+W) := by rw [add_assoc,Real.exp_add,Real.exp_log hX]
  have hMX : ((∏i,p i:ℕ):ℝ)<X*R :=
    hMx.trans_lt (mul_lt_mul_of_pos_left hinflation hX)
  have hQT : ((∏q:↥(tupleDistinctPrimes p),(q:ℕ):ℕ):ℝ)<X :=
    hQ.trans_lt ((div_lt_iff₀ hR).mpr (by nlinarith))
  have hnonneg : 0≤((∏q:↥(tupleDistinctPrimes p),(q:ℕ):ℕ):ℝ) := Nat.cast_nonneg _
  linarith

end Ostmann.Construction.InitialEta

end

end OAI
