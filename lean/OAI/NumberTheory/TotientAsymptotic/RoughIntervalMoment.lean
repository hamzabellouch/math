import OAI.NumberTheory.TotientAsymptotic.IntervalOmegaMoment
import OAI.NumberTheory.TotientAsymptotic.IntervalEulerBound
import OAI.NumberTheory.TotientAsymptotic.IntervalPrimeMass

namespace OAI

/-! Multiplicity-sensitive moments for the rough factors in a collision band. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma rough_interval_weight_norm {c U V : ℝ} (hc : 0 ≤ c) (hcU : 2*c ≤ U)
    {p : ℕ} (hp : p.Prime) : ‖intervalOmegaWeight c U V p‖ < 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (intervalOmegaWeight_nonneg hc U V p),
    intervalOmegaWeight_prime c U V hp]
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  apply (div_lt_one hp0).mpr
  split_ifs with h
  · linarith [h.1]
  · exact_mod_cast hp.one_lt

lemma rough_interval_euler_log {c p : ℝ} (hc : 0 ≤ c) (hp : 0 < p) (hcp : 2*c ≤ p) :
    Real.log ((1-c/p)⁻¹) ≤ c/p+2*c^2/p^2 := by
  have hx0 : 0 ≤ c/p := div_nonneg hc hp.le
  have hx : c/p ≤ 1/2 := (div_le_iff₀ hp).mpr (by linarith)
  have ht := Real.abs_log_sub_add_sum_range_le
    (show |c/p| < 1 by rw [abs_of_nonneg hx0]; linarith) 1
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.cast_zero,
    pow_one,div_one,abs_of_nonneg hx0] at ht
  have hq : (c/p)^2/(1-c/p) ≤ 2*c^2/p^2 := by
    calc
      _ ≤ (c/p)^2/(1/2) := div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)
      _ = _ := by ring
  rw [Real.log_inv]
  linarith [(abs_le.mp ht).1]

lemma rough_interval_reciprocal_moment {c U V : ℝ} (hc : 0 ≤ c) (hcU : 2*c ≤ U)
    (hU : 2 ≤ U) (hUV : U ≤ V) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q,0 < n ∧ ∀ p ∈ n.primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) :
    (∑ n ∈ Q,c^n.primeFactorsList.length/(n:ℝ)) ≤
      Real.exp (c*(∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),(p:ℝ)⁻¹)+
        2*c^2*(∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),((p:ℝ)^2)⁻¹)) := by
  classical
  let S := (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ))
  have hV0 : 0 ≤ V := by linarith
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime ∧ U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
    obtain ⟨hp,hU⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,hV⟩ := (primesUpTo_mem hV0).mp hp
    exact ⟨hp,hU,hV⟩
  have hweight (n : ℕ) (hn : n ∈ Q) :
      intervalOmegaWeight c U V n=c^n.primeFactorsList.length/(n:ℝ) := by
    have he : n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V)=n.primeFactorsList := by
      apply List.filter_eq_self.mpr
      intro p hp
      simpa only [decide_eq_true_eq] using (hQ n hn).2 p hp
    simp only [intervalOmegaWeight,MonoidHom.coe_mk,OneHom.coe_mk,omegaIn,he]
  have hm (n : ℕ) (hn : n ∈ Q) : n ∈ Nat.factoredNumbers S := by
    refine ⟨(hQ n hn).1.ne',?_⟩
    intro p hp
    obtain ⟨hUp,hpV⟩ := (hQ n hn).2 p hp
    exact Finset.mem_filter.mpr ⟨(primesUpTo_mem hV0).mpr
      ⟨Nat.prime_of_mem_primeFactorsList hp,hpV⟩,hUp⟩
  let e : {n // n ∈ Q} → Nat.factoredNumbers S := fun n => ⟨n.1,hm n.1 n.2⟩
  let T := Q.attach.image e
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers S => z.val) h
  have hsum : (∑ n ∈ Q,c^n.primeFactorsList.length/(n:ℝ)) =
      ∑ n ∈ T,intervalOmegaWeight c U V n := by
    dsimp only [T]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    change _ = ∑ n ∈ Q.attach,intervalOmegaWeight c U V n.val
    calc
      _ = ∑ n ∈ Q,intervalOmegaWeight c U V n :=
        Finset.sum_congr rfl (fun n hn => (hweight n hn).symm)
      _ = _ := (Finset.sum_attach Q _).symm
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f:=intervalOmegaWeight c U V) (fun {_} hp => rough_interval_weight_norm hc hcU hp) S
  have hfilter : S.filter Nat.Prime=S := Finset.filter_true_of_mem (fun p hp => (hS p hp).1)
  have hfac (p : ℕ) (hp : p ∈ S) : 0 < (1-c/(p:ℝ))⁻¹ := by
    have hp0 : (0:ℝ) < p := by exact_mod_cast (hS p hp).1.pos
    apply inv_pos.mpr
    have hh : c/(p:ℝ) < 1 := (div_lt_one hp0).mpr (by have := (hS p hp).2.1; linarith)
    linarith
  have hprod : (∏ p ∈ S,(1-c/(p:ℝ))⁻¹) ≤
      Real.exp (c*(∑ p ∈ S,(p:ℝ)⁻¹)+2*c^2*(∑ p ∈ S,((p:ℝ)^2)⁻¹)) := by
    apply (Real.log_le_iff_le_exp (Finset.prod_pos hfac)).mp
    rw [Real.log_prod (fun p hp => (hfac p hp).ne'),Finset.mul_sum,Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hh := rough_interval_euler_log hc
      (show (0:ℝ) < p by exact_mod_cast (hS p hp).1.pos)
      (hcU.trans (hS p hp).2.1.le)
    convert hh using 1
    ring
  calc
    _ = ∑ n ∈ T,intervalOmegaWeight c U V n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S,intervalOmegaWeight c U V n :=
      hs.1.of_norm.sum_le_tsum T (fun n _ => intervalOmegaWeight_nonneg hc U V n)
    _ = ∏ p ∈ S with p.Prime,(1-intervalOmegaWeight c U V p)⁻¹ := hs.2.tsum_eq
    _ = ∏ p ∈ S,(1-c/(p:ℝ))⁻¹ := by
      rw [hfilter]
      apply Finset.prod_congr rfl
      intro p hp
      simp only [intervalOmegaWeight_prime c U V (hS p hp).1,(hS p hp).2,and_self,ite_true]
    _ ≤ _ := hprod

end TotientAsymptotic

end

end OAI
