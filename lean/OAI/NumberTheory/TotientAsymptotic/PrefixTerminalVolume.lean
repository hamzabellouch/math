import OAI.NumberTheory.TotientAsymptotic.SimplexVolume

namespace OAI

/-! The terminal slice of a prefix region is another prefix region. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefixLinear_last (N : ℕ) (u : Fin (N+1) → ℝ) :
    prefixLinear (N+1) u (Fin.last N)=u (Fin.last N) := by
  rw [prefixLinear_apply]
  have hz : (∑ j : Fin (N+1),
      if Fin.last N < j then a (j.val-(Fin.last N).val)*u j else 0)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (by have := j.isLt; simp only [Fin.lt_def,Fin.val_last]; omega)]
  rw [hz,sub_zero]

lemma weighted_sum_update_last (N : ℕ) (C : Fin (N+1) → ℝ) (t : ℝ) :
    (∑ i : Fin (N+1),g (i.val+1)*Function.update C (Fin.last N) t i)=
      (∑ i : Fin (N+1),g (i.val+1)*C i)+g (N+1)*(t-C (Fin.last N)) := by
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  have hs : (∑ i : Fin N,g (i.castSucc.val+1)*
      Function.update C (Fin.last N) t i.castSucc)=
      ∑ i : Fin N,g (i.castSucc.val+1)*C i.castSucc := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Function.update_of_ne (Fin.castSucc_ne_last i)]
  rw [hs,Function.update_self]
  simp only [Fin.val_last]
  ring

lemma prefixRegion_terminal_inter (N : ℕ) (B C₀ : ℝ)
    (C : Fin (N+1) → ℝ) {t : ℝ} (ht : C (Fin.last N) ≤ t) :
    prefixRegion (N+1) B C₀ C ∩ {u | t ≤ u (Fin.last N)}=
      prefixRegion (N+1) B C₀ (Function.update C (Fin.last N) t) := by
  ext u
  constructor
  · rintro ⟨⟨hu,hbudget⟩,hterminal⟩
    refine ⟨fun i => ?_,hbudget⟩
    by_cases hi : i=Fin.last N
    · subst i
      rw [Function.update_self,prefixLinear_last]
      exact hterminal
    · rw [Function.update_of_ne hi]
      exact hu i
  · rintro ⟨hu,hbudget⟩
    have hterminal : t ≤ u (Fin.last N) := by
      have hh := hu (Fin.last N)
      rwa [Function.update_self,prefixLinear_last] at hh
    refine ⟨⟨fun i => ?_,hbudget⟩,hterminal⟩
    by_cases hi : i=Fin.last N
    · subst i
      rw [prefixLinear_last]
      exact ht.trans hterminal
    · have hh := hu i
      rwa [Function.update_of_ne hi] at hh

/-- Exact cap volume, including the empty-cap case through the positive part. -/
theorem volume_prefixRegion_terminal (N : ℕ) (B C₀ : ℝ)
    (C : Fin (N+1) → ℝ) {t : ℝ} (ht : C (Fin.last N) ≤ t) :
    volume (prefixRegion (N+1) B C₀ C ∩ {u | t ≤ u (Fin.last N)})=
      ENNReal.ofReal
        ((max (B-C₀-(∑ i : Fin (N+1),g (i.val+1)*C i)-
            g (N+1)*(t-C (Fin.last N))) 0)^(N+1)/
          (((N+1).factorial:ℝ)*∏ i : Fin (N+1),g (i.val+1))) := by
  rw [prefixRegion_terminal_inter N B C₀ C ht,
    volume_prefixRegion_explicit (N+1) (by omega),weighted_sum_update_last]
  congr 1
  congr 2
  congr 1
  ring

end TotientAsymptotic

end

end OAI
