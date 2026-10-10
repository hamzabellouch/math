import OAI.NumberTheory.TotientAsymptotic.PrimeIntervalMass

namespace OAI

/-! A telescoping bound for replacing 1/p by 1/(p-1). -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma shifted_reciprocal_error (S : Finset ℕ) {a : ℝ} (ha : 2≤a)
    (hS : ∀ p ∈ S, a≤(p : ℝ)) :
    |(∑ p ∈ S, (p-1 : ℝ)⁻¹)-(∑ p ∈ S, (p : ℝ)⁻¹)| ≤ 2/a := by
  classical
  by_cases hne : S.Nonempty
  · let L := ⌈a⌉₊
    let M := S.sup id
    have hLa : a≤(L : ℝ) := Nat.le_ceil a
    have hL : 2≤L := by exact_mod_cast (ha.trans hLa)
    have hsub : S⊆Finset.Icc L M := by
      intro p hp
      exact Finset.mem_Icc.mpr ⟨(Nat.ceil_le).mpr (hS p hp),Finset.le_sup (f := id) hp⟩
    have hLM : L≤M := by
      obtain ⟨p,hp⟩ := hne
      exact (Finset.mem_Icc.mp (hsub hp)).1.trans (Finset.mem_Icc.mp (hsub hp)).2
    have hn (n : ℕ) (hn : n∈Finset.Icc L M) : (1 : ℝ)<n := by
      exact_mod_cast (show 1<n by have := (Finset.mem_Icc.mp hn).1; omega)
    have ht : (∑ n ∈ Finset.Icc L M, (((n : ℝ)-1)⁻¹-(n : ℝ)⁻¹))=
        ((L : ℝ)-1)⁻¹-(M : ℝ)⁻¹ := by
      have hh := Finset.sum_Icc_sub hLM (fun n : ℕ => ((n : ℝ)-1)⁻¹)
      simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hh
      simpa only [← Finset.sum_neg_distrib,neg_sub] using congrArg Neg.neg hh
    have hnon (n : ℕ) (hn' : n∈Finset.Icc L M) :
        0≤((n : ℝ)-1)⁻¹-(n : ℝ)⁻¹ := by
      apply sub_nonneg.mpr
      exact inv_anti₀ (by linarith [hn n hn']) (by linarith)
    have hnonS : 0≤∑ p ∈ S, (((p : ℝ)-1)⁻¹-(p : ℝ)⁻¹) :=
      Finset.sum_nonneg (fun p hp => hnon p (hsub hp))
    rw [← Finset.sum_sub_distrib,abs_of_nonneg hnonS]
    calc
      _ ≤ ∑ n ∈ Finset.Icc L M, (((n : ℝ)-1)⁻¹-(n : ℝ)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hnon n hn)
      _ = ((L : ℝ)-1)⁻¹-(M : ℝ)⁻¹ := ht
      _ ≤ ((L : ℝ)-1)⁻¹ := sub_le_self _ (by positivity)
      _ ≤ 2/a := by
        rw [inv_eq_one_div]
        apply (div_le_div_iff₀ (by linarith : (0 : ℝ)<L-1) (by linarith : 0<a)).mpr
        nlinarith
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty,sub_self,abs_zero]
    positivity

end TotientAsymptotic

end

end OAI
