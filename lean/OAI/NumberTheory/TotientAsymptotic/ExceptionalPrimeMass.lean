import OAI.NumberTheory.TotientAsymptotic.PrimeMassSplit

namespace OAI

/-! A finite union bound for one exceptional prime in a bounded tuple. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma bounded_prime_tuple_mass {n : ℕ} (T : Finset ℕ) (Q : Finset (Fin n → ℕ))
    (hQ : ∀ p ∈ Q,∀ i,p i ∈ T) :
    (∑ p ∈ Q,reciprocalShiftWeight p) ≤
      (∑ r ∈ T,((r-1:ℕ):ℝ)⁻¹)^n := by
  classical
  have hsub : Q ⊆ Fintype.piFinset (fun _ : Fin n => T) := by
    intro p hp
    exact Fintype.mem_piFinset.mpr (hQ p hp)
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => reciprocalShiftWeight_nonneg p)).trans_eq
  rw [prime_pi_mass]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem exceptional_prime_tuple_mass {n : ℕ} (T U : Finset ℕ)
    (Q : Finset (Fin n → ℕ))
    (hQ : ∀ p ∈ Q,(∀ i,p i ∈ T) ∧ ∃ i,p i ∈ U) :
    (∑ p ∈ Q,reciprocalShiftWeight p) ≤
      (n:ℝ)*(∑ r ∈ U,((r-1:ℕ):ℝ)⁻¹)*
        (∑ r ∈ T,((r-1:ℕ):ℝ)⁻¹)^(n-1) := by
  classical
  let F (i : Fin n) := Q.filter (fun p => p i ∈ U)
  have hsum : (∑ p ∈ Q,reciprocalShiftWeight p) ≤
      ∑ i : Fin n,∑ p ∈ F i,reciprocalShiftWeight p := by
    simp only [F,Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨i,hi⟩ := (hQ p hp).2
    have hh := Finset.single_le_sum
      (s:=Finset.univ) (f:=fun j : Fin n => if p j ∈ U then reciprocalShiftWeight p else 0)
      (fun j _ => by split_ifs; exact reciprocalShiftWeight_nonneg p; exact le_rfl)
      (Finset.mem_univ i)
    simpa only [ite_eq_left hi] using hh
  have hbound (i : Fin n) :
      (∑ p ∈ F i,reciprocalShiftWeight p) ≤
        (∑ r ∈ U,((r-1:ℕ):ℝ)⁻¹)*
          (∑ r ∈ T,((r-1:ℕ):ℝ)⁻¹)^(n-1) := by
    let W : Fin n → Finset ℕ := Function.update (fun _ => T) i U
    have hsub : F i ⊆ Fintype.piFinset W := by
      intro p hp
      obtain ⟨hp,hi⟩ := Finset.mem_filter.mp hp
      apply Fintype.mem_piFinset.mpr
      intro j
      by_cases he : j=i
      · subst j
        simpa only [W,Function.update_self] using hi
      · simpa only [W,Function.update_of_ne he] using (hQ p hp).1 j
    calc
      _ ≤ ∑ p ∈ Fintype.piFinset W,reciprocalShiftWeight p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ => reciprocalShiftWeight_nonneg p)
      _ = ∏ j : Fin n,∑ r ∈ W j,((r-1:ℕ):ℝ)⁻¹ := prime_pi_mass W
      _ = ∏ j : Fin n,Function.update (fun _ => ∑ r ∈ T,((r-1:ℕ):ℝ)⁻¹)
          i (∑ r ∈ U,((r-1:ℕ):ℝ)⁻¹) j := by
        apply Finset.prod_congr rfl
        intro j _
        by_cases he : j=i <;> simp only [W,Function.update_apply,he,ite_true,ite_false]
      _ = _ := by
        rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
        simp only [Finset.prod_const,Finset.card_sdiff,Finset.inter_univ,
          Finset.card_singleton,Finset.card_univ,Fintype.card_fin]
  apply hsum.trans
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hbound i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hh

end TotientAsymptotic

end

end OAI
