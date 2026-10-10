import OAI.NumberTheory.Ostmann.QuadraticCenter.CommonCenter
import OAI.NumberTheory.Ostmann.QuadraticCenter.LiftProductCount

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem reduced_common_center_from_product_witnesses
    {P E : Finset ℕ} (hP : ∀ p ∈ P,Nat.Prime p) {k : ℕ}
    (hE : E ⊆ primeProductSamples P k) (t : ℕ → ℤ)
    (A H Z lo cutoff mass : ℕ) (hA : 0 < A) (hAZ : A < Z)
    (hlarge : ∀ p ∈ P,Z ≤ p) (hk : 0 < k) (hlo : lo ≤ k) (hmass : 0 < mass)
    (hlift : ∀ q ∈ E,∃ a : ℕ,1 ≤ a ∧ a ≤ A ∧
      (boundedSubsetLifts q.primeFactors a t H).Nonempty)
    (hbudget : mass + cutoff^(k-lo)*(P.card^lo*(2*H/Z^lo+1)) ≤
      k.factorial*E.card/A)
    (hspacing : 2*H < Z^(k+1)) (hgap : 2*k*P.card ≤ cutoff^2) :
    ∃ h : ℤ,∃ m : ℕ,∃ P₀ : Finset ℕ,
      0 < m ∧ m ≤ A ∧ IsCoprime h (m:ℤ) ∧ h.natAbs ≤ H ∧
      P₀ ⊆ P ∧ cutoff ≤ P₀.card ∧
      (mass:ℝ) ≤ 2*(P.card:ℝ)*(P₀.card:ℝ)^(k-1) ∧
      ∀ p ∈ P₀,(p:ℤ) ∣ h-(m:ℤ)*t p := by
  classical
  obtain ⟨a,ha,haA,hhigh⟩ := exists_fixed_multiplier_lift_moment hP hE A H hA t hlift
  let I : Finset ℤ := Finset.Icc (-(H:ℤ)) H
  have hZ : 0 < Z := by omega
  have hdiv : k.factorial*E.card/A ≤
      ∑ n ∈ I,(matchingPrimes P a n t).card.descFactorial k := by
    have hfloor := Nat.div_mul_le_self (k.factorial*E.card) A
    change k.factorial*E.card ≤ A*(∑ n ∈ I,(matchingPrimes P a n t).card.descFactorial k) at hhigh
    nlinarith
  have hlow := sum_matching_descFactorial_le hP (a:ℤ) t H lo Z hZ hlarge
  have hmoment : mass + cutoff^(k-lo)*
      (∑ n ∈ I,(matchingPrimes P a n t).card.descFactorial lo) ≤
      ∑ n ∈ I,(matchingPrimes P a n t).card.descFactorial k :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlow) mass).trans (hbudget.trans hdiv)
  have hnat (n : I) : n.val.natAbs ≤ H := by
    have hn := Finset.mem_Icc.mp n.property
    have hh : |n.val| ≤ (H:ℤ) := abs_le.mpr hn
    have hh' : (n.val.natAbs:ℤ) ≤ (H:ℤ) := by simpa only [Int.natCast_natAbs] using hh
    exact_mod_cast hh'
  have hinter (n m : I) : (n.val-m.val).natAbs < Z^(k+1) := by
    have hn := Finset.mem_Icc.mp n.property
    have hm := Finset.mem_Icc.mp m.property
    have hh : |n.val-m.val| ≤ ((2*H:ℕ):ℤ) := abs_le.mpr ⟨by omega,by omega⟩
    have hh' : ((n.val-m.val).natAbs:ℤ) ≤ ((2*H:ℕ):ℤ) := by
      simpa only [Int.natCast_natAbs] using hh
    exact (by exact_mod_cast hh' : (n.val-m.val).natAbs ≤ 2*H).trans_lt hspacing
  obtain ⟨h,m,P₀,hm,hmA,hcop,hh,hsub,hcut,hsize,hcenter⟩ :=
    reduced_common_center_from_lift_moments P hP a ha t (fun n : I => n.val)
      Subtype.val_injective (k-1) lo cutoff k mass Z H (haA.trans_lt hAZ) hlarge hnat
      (by omega) hmass (by
        simp only [Nat.sub_add_cancel hk,Finset.sum_coe_sort I
          (fun n : ℤ => (matchingPrimes P a n t).card.descFactorial lo),
          Finset.sum_coe_sort I (fun n : ℤ => (matchingPrimes P a n t).card.descFactorial k)]
        exact hmoment)
      (fun n m _ => hinter n m) hgap
  exact ⟨h,m,P₀,hm,hmA.trans haA,hcop,hh,hsub,hcut,hsize,hcenter⟩

end Ostmann.QuadraticCenter

end

end OAI
