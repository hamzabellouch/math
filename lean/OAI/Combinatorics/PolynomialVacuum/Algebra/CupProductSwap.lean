import OAI.Combinatorics.PolynomialVacuum.Algebra.CupDivisibility
import OAI.Combinatorics.PolynomialVacuum.Algebra.ExchangeDiscrepancy

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem adjacentSwap_lt {j i k : ℕ} (hik : i<k) (hne : (i,k)≠(j,j+1)) :
    Equiv.swap j (j+1) i < Equiv.swap j (j+1) k := by
  have hn : ¬ (i=j ∧ k=j+1) := by
    rintro ⟨rfl,rfl⟩; exact hne rfl
  simp only [Equiv.swap_apply_def]
  split_ifs <;> omega

theorem adjacentSwap_bound {m j i : ℕ} (hj : j+1 < m) :
    Equiv.swap j (j+1) i < m ↔ i < m := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> omega

noncomputable def exceptCupVandermonde (m j : ℕ) : MvPolynomial ℕ ℂ :=
  ∏ ab∈(cupPairs m).erase (j,j+1), cupFactor ab.1 ab.2

theorem rename_exceptCupVandermonde {m j : ℕ} (hj : j+1 < m) :
    rename (Equiv.swap j (j+1)) (exceptCupVandermonde m j)=exceptCupVandermonde m j := by
  simp only [exceptCupVandermonde,map_prod]
  apply Finset.prod_equiv (Equiv.prodCongr (Equiv.swap j (j+1)) (Equiv.swap j (j+1)))
  · rintro ⟨a,b⟩
    simp only [Equiv.prodCongr_apply,Prod.map_apply,Finset.mem_erase,mem_cupPairs]
    constructor
    · intro ⟨hne,hab,hbm⟩
      refine ⟨?_,adjacentSwap_lt hab hne,(adjacentSwap_bound hj).mpr hbm⟩
      intro he
      have ha := congrArg Prod.fst he
      have hb := congrArg Prod.snd he
      have ha' := congrArg (Equiv.swap j (j+1)) ha
      have hb' := congrArg (Equiv.swap j (j+1)) hb
      simp only [Equiv.swap_apply_self,Equiv.swap_apply_left,Equiv.swap_apply_right] at ha' hb'
      omega
    · intro ⟨hne,hab,hbm⟩
      have ht := adjacentSwap_lt hab hne
      simp only [Equiv.swap_apply_self] at ht
      refine ⟨?_,ht,(adjacentSwap_bound hj).mp hbm⟩
      intro he
      have ha : a=j := congrArg Prod.fst he
      have hb : b=j+1 := congrArg Prod.snd he
      rw [ha,hb,Equiv.swap_apply_left,Equiv.swap_apply_right] at hab
      omega
  · rintro ⟨a,b⟩ hab
    simp only [cupFactor,map_sub,map_mul,rename_X,rename_C,Equiv.prodCongr_apply,Prod.map_apply]

theorem cupVandermonde_factor {m j : ℕ} (hj : j+1 < m) :
    cupVandermonde m=cupFactor j (j+1)*exceptCupVandermonde m j := by
  exact (Finset.mul_prod_erase _ _ ((mem_cupPairs _ _ _).mpr ⟨by omega,hj⟩)).symm

theorem cupVandermonde_swap_polynomial {m j : ℕ} (hj : j+1 < m) :
    cupFactor j (j+1)*rename (Equiv.swap j (j+1)) (cupVandermonde m)=
      rename (Equiv.swap j (j+1)) (cupFactor j (j+1))*cupVandermonde m := by
  rw [cupVandermonde_factor hj,map_mul,rename_exceptCupVandermonde hj]
  ring

theorem eval_cupVandermonde_swap {m j : ℕ} (hj : j+1 < m) (Y : ℕ → ℂ) :
    (Y (j+1)-T*Y j)*eval (swapSite j Y) (cupVandermonde m)=
      (Y j-T*Y (j+1))*eval Y (cupVandermonde m) := by
  have he := congrArg (eval Y) (cupVandermonde_swap_polynomial hj)
  simpa only [map_mul,cupFactor,map_sub,eval_X,eval_C,eval_rename,swapSite,
    Function.comp_def,Equiv.swap_apply_left,Equiv.swap_apply_right] using he

end PolynomialVacuumAlgebra

end OAI
