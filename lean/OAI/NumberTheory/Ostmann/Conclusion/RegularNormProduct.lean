import OAI.NumberTheory.Ostmann.Conclusion.RegularNormGeneral

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open scoped BigOperators

theorem regular_prime_product_totient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i,p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) :
    (∏ i,p i).totient = ∏ i,(p i-1) := by
  have hc := Fintype.card_congr (Supply.crtUnitsEquiv p hcop).toEquiv
  rw [ZMod.card_units_eq_totient,Fintype.card_pi] at hc
  simp only [ZMod.card_units_eq_totient] at hc
  rw [hc]
  exact Finset.prod_congr rfl (fun i _ => Nat.totient_prime (Fact.out : (p i).Prime))

theorem regular_prime_product_ratio_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i,p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (hsum : (∑ i,1/((p i : ℝ)-1))≤Real.log 2) :
    ((∏ i,p i : ℕ) : ℝ)/(∏ i,p i).totient≤2 := by
  rw [regular_prime_product_totient p hcop]
  have hid : ((∏ i,p i : ℕ) : ℝ)/((∏ i,(p i-1) : ℕ) : ℝ)=
      ∏ i,((p i : ℝ)/((p i : ℝ)-1)) := by
    simp only [Nat.cast_prod,Finset.prod_div_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub (Fact.out : (p i).Prime).one_le]
    norm_num
  rw [hid]
  exact (prime_ratio_product_le_exp p (fun i => (Fact.out : (p i).Prime).two_le)).trans
    ((Real.exp_le_exp.mpr hsum).trans_eq (Real.exp_log (by norm_num)))

theorem regular_prime_product_le_exp {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀i,0<p i) {H : ℝ} (hlog : ∀i,Real.log (p i : ℝ)≤H) :
    ((∏i,p i : ℕ) : ℝ)≤Real.exp ((Fintype.card ι : ℝ)*H) := by
  have hsum : ∑i,Real.log (p i : ℝ)≤(Fintype.card ι : ℝ)*H := by
    exact (Finset.sum_le_sum (fun i _ => hlog i)).trans_eq (by simp)
  have hprod := Real.exp_le_exp.mpr hsum
  rw [Real.exp_sum] at hprod
  have he : ∀i,Real.exp (Real.log (p i : ℝ))=(p i : ℝ) :=
    fun i => Real.exp_log (by exact_mod_cast hp i)
  simpa only [he,Nat.cast_prod] using hprod

end Ostmann.Conclusion

end

end OAI
