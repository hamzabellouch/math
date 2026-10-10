import OAI.NumberTheory.Ostmann.Construction.PivotFrequencyReindex

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template

theorem positive_pivot_frequency_reindex_of_ne_zero (N : ℤ) (hN : N ≠ 0)
    (R : Finset ℕ) (hR : ∀ P ∈ R, 0 < P) (T : Finset ℤ) (F : ℤ → ℂ)
    (hcut : ∀ P ∈ R, ∀ s : ℤ, N=s*(P:ℤ) → F (P:ℤ) ≠ 0 → s ∈ T) :
    (∑ P ∈ R, if (P:ℤ) ∣ N then F (P:ℤ) else 0)=
      ∑ s ∈ T, if s ≠ 0 ∧ 0 < N/s ∧ (N/s).toNat ∈ R ∧ s*(N/s)=N
        then F (N/s) else 0 := by
  classical
  have he := Construction.pivot_frequency_reindex N hN 1 (by norm_num) R hR T
    (fun P => F (P:ℤ)) (fun P hP s hs hf =>
      hcut P hP s (by simpa only [Nat.cast_one,mul_one] using hs) hf)
  simp only [Construction.reversalPivot,Nat.cast_one,mul_one,one_mul] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hold : (N/s).toNat ∈ R ∧ N=s*((N/s).toNat:ℤ)
  · have hp := hR _ hold.1
    have hpos : 0 < N/s := by omega
    have hcast : ((N/s).toNat:ℤ)=N/s := Int.toNat_of_nonneg hpos.le
    have hs0 : s ≠ 0 := by
      intro hz
      have hh := hold.2
      rw [hz,zero_mul] at hh
      exact hN hh
    have hnew : s ≠ 0 ∧ 0 < N/s ∧ (N/s).toNat ∈ R ∧ s*(N/s)=N :=
      ⟨hs0,hpos,hold.1,by simpa only [hcast] using hold.2.symm⟩
    rw [ite_eq_left hold,ite_eq_left hnew,hcast]
  · have hnew : ¬(s ≠ 0 ∧ 0 < N/s ∧ (N/s).toNat ∈ R ∧ s*(N/s)=N) := by
      rintro ⟨hs0,hpos,hmem,heq⟩
      apply hold
      exact ⟨hmem,by simpa only [Int.toNat_of_nonneg hpos.le] using heq.symm⟩
    simp only [hold,hnew,ite_false]

theorem positive_pivot_frequency_reindex (N : ℤ)
    (R : Finset ℕ) (hR : ∀ P ∈ R, 0 < P) (T : Finset ℤ) (F : ℤ → ℂ)
    (hcut : ∀ P ∈ R, ∀ s : ℤ, N ≠ 0 → N=s*(P:ℤ) → F (P:ℤ) ≠ 0 → s ∈ T) :
    (∑ P ∈ R, if (P:ℤ) ∣ N ∧ N ≠ 0 then F (P:ℤ) else 0)=
      ∑ s ∈ T, if s ≠ 0 ∧ 0 < N/s ∧ (N/s).toNat ∈ R ∧ s*(N/s)=N
        then F (N/s) else 0 := by
  classical
  by_cases hN : N=0
  · simp [hN]
  · simpa only [hN,ne_eq,not_false_eq_true,and_true] using
      positive_pivot_frequency_reindex_of_ne_zero N hN R hR T F (fun P hP s => hcut P hP s hN)

theorem positive_pivot_frequency_reindex_with_diagonal (N : ℤ)
    (R : Finset ℕ) (hR : ∀ P ∈ R, 0 < P) (T : Finset ℤ) (F : ℤ → ℂ)
    (hcut : ∀ P ∈ R, ∀ s : ℤ, N ≠ 0 → N=s*(P:ℤ) → F (P:ℤ) ≠ 0 → s ∈ T) :
    (∑ P ∈ R, if (P:ℤ) ∣ N then F (P:ℤ) else 0)=
      (if N=0 then ∑ P ∈ R,F (P:ℤ) else 0)+
      ∑ s ∈ T, if s ≠ 0 ∧ 0 < N/s ∧ (N/s).toNat ∈ R ∧ s*(N/s)=N
        then F (N/s) else 0 := by
  classical
  by_cases hN : N=0
  · simp [hN]
  · simpa only [hN,ite_false,zero_add] using
      positive_pivot_frequency_reindex_of_ne_zero N hN R hR T F (fun P hP s => hcut P hP s hN)

end Ostmann.Characters.Template

end

end OAI
