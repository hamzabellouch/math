import Mathlib
import OAI.NumberTheory.Ostmann.Construction.Reversal

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def reversalPivot (N : ℤ) (u : ℕ) (s : ℤ) : ℕ := (N/(s*(u:ℤ))).toNat

theorem reversalPivot_eq (N : ℤ) (u p : ℕ) (s : ℤ) (hu : 0<u) (hs : s≠0)
    (he : N=s*(u:ℤ)*(p:ℤ)) : reversalPivot N u s=p := by
  unfold reversalPivot
  rw [he,Int.mul_ediv_cancel_left _ (mul_ne_zero hs (by exact_mod_cast hu.ne')),Int.toNat_natCast]

theorem reversal_frequency_sum (N : ℤ) (u p : ℕ) (hu : 0<u) (hp : 0<p)
    (T : Finset ℤ) (F : ℂ)
    (hcut : ∀s,N=s*(u:ℤ)*(p:ℤ)→F≠0→s∈T) :
    (if (u:ℤ)*(p:ℤ)∣N then F else 0)=∑s∈T,if N=s*(u:ℤ)*(p:ℤ) then F else 0 := by
  classical
  by_cases hF : F=0
  · simp only [hF,ite_self,Finset.sum_const_zero]
  by_cases hd : (u:ℤ)*(p:ℤ)∣N
  · obtain ⟨s,he⟩ := hd
    have hs : N=s*(u:ℤ)*(p:ℤ) := by rw [he]; ring
    have hmem := hcut s hs hF
    rw [ite_eq_left ⟨s,he⟩,Finset.sum_eq_single s]
    · simp only [hs,ite_true]
    · intro t ht hts
      have hn : ¬N=t*(u:ℤ)*(p:ℤ) := by
        intro he'
        have hc : t=s := by
          apply mul_right_cancel₀ (by exact_mod_cast hu.ne' : (u:ℤ)≠0)
          apply mul_right_cancel₀ (by exact_mod_cast hp.ne' : (p:ℤ)≠0)
          exact he'.symm.trans hs
        exact hts hc
      simp only [hn,ite_false]
    · intro hn
      exact (hn hmem).elim
  · rw [ite_eq_right hd]
    symm
    apply Finset.sum_eq_zero
    intro s hs
    have hn : ¬N=s*(u:ℤ)*(p:ℤ) := by
      intro he
      apply hd
      refine ⟨s,?_⟩
      rw [he]
      ring
    simp only [hn,ite_false]

theorem reversal_pivot_sum (N : ℤ) (hN : N≠0) (u : ℕ) (hu : 0<u)
    (S : Finset ℕ) (F : ℕ→ℂ) (s : ℤ) :
    (∑p∈S,if N=s*(u:ℤ)*(p:ℤ) then F p else 0)=
      if reversalPivot N u s∈S ∧ N=s*(u:ℤ)*(reversalPivot N u s:ℤ)
      then F (reversalPivot N u s) else 0 := by
  classical
  by_cases hs : s=0
  · simp only [hs,zero_mul,hN,ite_false,Finset.sum_const_zero,and_false]
  have hterm (p : ℕ) :
      (if N=s*(u:ℤ)*(p:ℤ) then F p else 0)=
        if p=reversalPivot N u s then
          (if N=s*(u:ℤ)*(reversalPivot N u s:ℤ) then F (reversalPivot N u s) else 0) else 0 := by
    by_cases he : N=s*(u:ℤ)*(p:ℤ)
    · have hp := reversalPivot_eq N u p s hu hs he
      rw [hp]
      simp only [he,ite_true]
    · by_cases hp : p=reversalPivot N u s
      · simp only [hp,ite_true]
      · simp only [he,hp,ite_false]
  have hsum := Finset.sum_congr (s₁ := S) (s₂ := S) rfl (fun p _ => hterm p)
  rw [hsum,Finset.sum_ite_eq']
  by_cases hm : reversalPivot N u s∈S <;> simp [hm]

theorem pivot_frequency_reindex (N : ℤ) (hN : N≠0) (u : ℕ) (hu : 0<u)
    (S : Finset ℕ) (hS : ∀p∈S,0<p) (T : Finset ℤ) (F : ℕ→ℂ)
    (hcut : ∀p∈S,∀s,N=s*(u:ℤ)*(p:ℤ)→F p≠0→s∈T) :
    (∑p∈S,if (u:ℤ)*(p:ℤ)∣N then F p else 0)=
      ∑s∈T,if reversalPivot N u s∈S ∧ N=s*(u:ℤ)*(reversalPivot N u s:ℤ)
        then F (reversalPivot N u s) else 0 := by
  calc
    _ = ∑p∈S,∑s∈T,if N=s*(u:ℤ)*(p:ℤ) then F p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact reversal_frequency_sum N u p hu (hS p hp) T (F p) (hcut p hp)
    _ = ∑s∈T,∑p∈S,if N=s*(u:ℤ)*(p:ℤ) then F p else 0 := Finset.sum_comm
    _ = _ := by simp_rw [reversal_pivot_sum N hN u hu S F]

end Ostmann.Construction

end

end OAI
