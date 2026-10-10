import OAI.NumberTheory.TotientAsymptotic.CandidateArithmetic

namespace OAI

/-! Bounded totient ratio for the actual finite geometric candidate family. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_reverse_geometric_sum {n m : ℕ} (hn : n ≤ m) :
    (∑ i : Fin n,rho^(m-i.val)) ≤ (1-rho)⁻¹ := by
  let s := Finset.univ.image (fun i : Fin n => m-i.val)
  have hinj : Function.Injective (fun i : Fin n => m-i.val) := by
    intro i j hij
    dsimp only at hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  have he : (∑ i : Fin n,rho^(m-i.val))=∑ k ∈ s,rho^k := by
    dsimp only [s]
    rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
  rw [he]
  simpa only [tsum_geometric_of_lt_one rho_pos.le rho_lt_one,one_div] using
    (summable_geometric_of_lt_one rho_pos.le rho_lt_one).sum_le_tsum s
      (fun _ _ => pow_nonneg rho_pos.le _)

lemma finite_geometric_prime_reciprocals {n m : ℕ} (hn : n ≤ m) {c : ℝ} (hc : 0 < c)
    (p : Fin n → ℕ) (hp : ∀ i,(p i).Prime)
    (hmin : ∀ i,c*(rho^(m-i.val))⁻¹ ≤ primePrefixCoord p i) :
    (∑ i : Fin n,(p i:ℝ)⁻¹) ≤ (1-rho)⁻¹/c := by
  have hpoint (i : Fin n) : (p i:ℝ)⁻¹ ≤ rho^(m-i.val)/c := by
    have hp1 : (1:ℝ) ≤ p i := by exact_mod_cast (hp i).one_le
    have hcoord : primePrefixCoord p i ≤ p i :=
      (Real.log_le_self (Real.log_nonneg hp1)).trans (Real.log_le_self (Nat.cast_nonneg _))
    have hlarge := (hmin i).trans hcoord
    have hh := inv_anti₀ (mul_pos hc (inv_pos.mpr (pow_pos rho_pos _))) hlarge
    simpa only [mul_inv_rev,inv_inv,div_eq_mul_inv,mul_comm] using hh
  calc
    _ ≤ ∑ i : Fin n,rho^(m-i.val)/c := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (∑ i : Fin n,rho^(m-i.val))/c := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (finite_reverse_geometric_sum hn) hc.le

lemma prime_factor_ratio_exp {p : ℕ} (hp : p.Prime) :
    (p:ℝ)/(p-1) ≤ Real.exp (2/(p:ℝ)) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by linarith only [hp2]
  have hp1 : (0:ℝ) < p-1 := by linarith only [hp2]
  have hfrac : 1/(p-1) ≤ 2/(p:ℝ) := by
    apply (div_le_div_iff₀ hp1 hp0).mpr
    linarith only [hp2]
  have he : (p:ℝ)/(p-1)=1+1/(p-1) := by field_simp; ring
  rw [he]
  have hh := Real.add_one_le_exp (2/(p:ℝ))
  linarith only [hfrac,hh]

theorem finite_candidate_ratio_bound {n m : ℕ} (hn : n ≤ m) {c : ℝ} (hc : 0 < c)
    (p : Fin n → ℕ) (hp : ∀ i,(p i).Prime) (horder : StrictAnti p)
    (hmin : ∀ i,c*(rho^(m-i.val))⁻¹ ≤ primePrefixCoord p i)
    {q : ℕ} (hq : q.Prime) (hqp : ∀ i,p i < q) :
    ((q*(∏ i,p i):ℕ):ℝ)/(q*(∏ i,p i)).totient ≤
      Real.exp (1+2*((1-rho)⁻¹/c)) := by
  have hr := finite_geometric_prime_reciprocals hn hc p hp hmin
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hqinv : (q:ℝ)⁻¹ ≤ 1/2 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<2) hq2
  have hratio : ((q*(∏ i,p i):ℕ):ℝ)/(q*(∏ i,p i)).totient =
      (q:ℝ)/(q-1)*(∏ i : Fin n,(p i:ℝ)/(p i-1)) := by
    rw [candidate_prime_extension_totient hp hq hqp,ppt_totient_primeProduct p hp horder.injective]
    simp only [Nat.cast_mul,Nat.cast_prod,shiftedProduct,Nat.cast_sub (hq.one_le),Nat.cast_one]
    have he : (∏ i : Fin n,((p i-1:ℕ):ℝ)) = ∏ i : Fin n,((p i:ℝ)-1) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Nat.cast_sub (hp i).one_le,Nat.cast_one]
    rw [he]
    rw [Finset.prod_div_distrib]
    exact mul_div_mul_comm _ _ _ _
  rw [hratio]
  have htail : (∏ i : Fin n,(p i:ℝ)/(p i-1)) ≤
      Real.exp (2*∑ i : Fin n,(p i:ℝ)⁻¹) := by
    calc
      _ ≤ ∏ i : Fin n,Real.exp (2/(p i:ℝ)) := by
        apply Finset.prod_le_prod₀
        · intro i _
          have hh : (1:ℝ) < p i := by exact_mod_cast (hp i).one_lt
          exact div_nonneg (Nat.cast_nonneg _) (by linarith only [hh])
        · intro i _
          exact prime_factor_ratio_exp (hp i)
      _ = _ := by rw [←Real.exp_sum,Finset.mul_sum]; congr 1
  calc
    _ ≤ Real.exp (2/(q:ℝ))*Real.exp (2*∑ i : Fin n,(p i:ℝ)⁻¹) :=
      mul_le_mul (prime_factor_ratio_exp hq) htail
        (Finset.prod_nonneg (fun i _ => div_nonneg (Nat.cast_nonneg _)
          (sub_nonneg.mpr (by exact_mod_cast (hp i).one_le)))) (Real.exp_pos _).le
    _ = Real.exp (2*((q:ℝ)⁻¹+∑ i : Fin n,(p i:ℝ)⁻¹)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hr,hqinv])

end TotientAsymptotic

end

end OAI
