import OAI.Combinatorics.SquareDifference.FunctionalSplit

namespace OAI

section

open Finset

namespace SquareDifference

lemma euler_step_bound {x : ℝ} (hx : 2≤x) :
    ((x-1)/x)*(1+1/x^3)≤x/(x+1) := by
  have hx0 : 0<x := by linarith
  have hx1 : 0<x+1 := by linarith
  have he : ((x-1)/x)*(1+1/x^3)=((x-1)*(x^3+1))/(x*x^3) := by
    field_simp
  rw [he]
  apply (div_le_div_iff₀ (mul_pos hx0 (pow_pos hx0 3)) hx1).mpr
  nlinarith [mul_nonneg (sq_nonneg x) (show 0≤x-1 by linarith)]

lemma euler_interval_bound (P L : ℕ) (hP : 2≤P) (hPL : P≤L) :
    (∏n∈Ico P L, (1+1/(n : ℝ)^3))≤
      ((P : ℝ)/(P-1))*(((L : ℝ)-1)/L) := by
  induction L, hPL using Nat.le_induction with
  | base =>
    simp only [Ico_self,prod_empty]
    have hP0 : (P : ℝ)≠0 := by exact_mod_cast (by omega : P≠0)
    have hP1 : (P : ℝ)-1≠0 := by
      have hpR : (2 : ℝ)≤P := by exact_mod_cast hP
      linarith
    field_simp
    norm_num
  | @succ L hPL ih =>
    rw [prod_Ico_succ_top hPL]
    have hL : (2 : ℝ)≤L := by exact_mod_cast hP.trans hPL
    have hC : 0≤(P : ℝ)/(P-1) := by
      have hpR : (2 : ℝ)≤P := by exact_mod_cast hP
      exact div_nonneg (by positivity) (by linarith)
    calc
      _ ≤ ((P : ℝ)/(P-1))*(((L : ℝ)-1)/L)*(1+1/(L : ℝ)^3) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ ((P : ℝ)/(P-1))*((L : ℝ)/(L+1)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (euler_step_bound hL) hC
      _ = _ := by push_cast; congr 1; ring

lemma euler_finite_bound (S : Finset ℕ) (hS : ∀n∈S, 5≤n) :
    (∏n∈S, (1+1/(n : ℝ)^3))≤5/4 := by
  let L := max 5 (S.sup id+1)
  have hSL : S⊆Ico 5 L := by
    intro n hn
    apply mem_Ico.mpr
    refine ⟨hS n hn,?_⟩
    exact lt_of_lt_of_le (Nat.lt_succ_of_le (le_sup (f:=id) hn)) (le_max_right _ _)
  have h1 : (∏n∈S, (1+1/(n : ℝ)^3))≤∏n∈Ico 5 L, (1+1/(n : ℝ)^3) := by
    apply prod_le_prod_of_subset_of_one_le₀ hSL
    · intro n hn; positivity
    · intro n hn _; linarith [one_div_nonneg.mpr (show 0≤(n : ℝ)^3 by positivity)]
  apply h1.trans
  apply (euler_interval_bound 5 L (by omega) (le_max_left _ _)).trans
  have hL : 0<(L : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0<5) (le_max_left _ _))
  norm_num
  have hq : ((L : ℝ)-1)/L≤1 := (div_le_one hL).mpr (by linarith)
  nlinarith

lemma weighted_exceptional_budget {I : Type*} [DecidableEq I]
    (S : Finset I) (p : I → ℕ) (hinj : Set.InjOn p (↑S : Set I))
    (hp : ∀i∈S, 5≤p i) (η : I → ℝ)
    (hη : ∀i∈S, 0≤η i) (hηp : ∀i∈S, η i≤1/(p i : ℝ)^3) :
    (∑B∈S.powerset.erase ∅, ∏i∈B, η i)≤1/4 := by
  classical
  have hprod : (∏i∈S, (1+η i))≤5/4 := by
    calc
      _ ≤ ∏i∈S, (1+1/(p i : ℝ)^3) := by
        apply prod_le_prod₀ (fun i hi => by linarith [hη i hi])
        intro i hi
        linarith [hηp i hi]
      _ = ∏n∈S.image p, (1+1/(n : ℝ)^3) := (prod_image (f:=fun n : ℕ => (1 : ℝ)+1/(n : ℝ)^3) hinj).symm
      _ ≤ 5/4 := euler_finite_bound (S.image p) (by
        intro n hn; obtain ⟨i,hi,rfl⟩ := mem_image.mp hn; exact hp i hi)
  have he : (∑B∈S.powerset.erase ∅, ∏i∈B, η i)+1=∏i∈S, (1+η i) := by
    rw [prod_one_add, ← sum_erase_add _ _ (empty_mem_powerset S)]
    simp only [prod_empty]
  linarith

end SquareDifference

end

end OAI
