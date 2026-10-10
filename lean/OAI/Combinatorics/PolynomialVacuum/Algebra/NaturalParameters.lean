import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalCup

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

theorem skipOne_mark_right {α : Type*} (i : ℕ) (X : ℕ → α) :
    skipOne (i+1) (swapSite i X)=skipOne i X := by
  funext k
  simp only [skipOne,swapSite,Function.comp_apply,Equiv.swap_apply_def]
  split_ifs <;> congr 1 <;> omega

theorem skipOne_swap_before {α : Type*} {i j : ℕ} (h : j+1 < i) (X : ℕ → α) :
    skipOne i (swapSite j X)=swapSite j (skipOne i X) := by
  funext k
  simp only [skipOne,swapSite,Function.comp_apply,Equiv.swap_apply_def]
  split_ifs <;> congr 1 <;> omega

theorem skipOne_swap_after {α : Type*} {i j : ℕ} (h : i < j) (X : ℕ → α) :
    skipOne i (swapSite j X)=swapSite (j-1) (skipOne i X) := by
  funext k
  simp only [skipOne,swapSite,Function.comp_apply,Equiv.swap_apply_def]
  split_ifs <;> congr 1 <;> omega

noncomputable def fusionPair (x y : ℂ) : ℂ := (y-t^5*x)*(y-t^6*x)
noncomputable def leftFusion (i : ℕ) (X : ℕ → ℂ) : ℂ :=
  ∏ k ∈ Finset.range i, fusionPair (X i) (X k)

theorem fusionPair_denominator (x y : ℂ) : fusionPair x y=exchangeDenominator (T*x) y := by
  simp only [fusionPair,exchangeDenominator,T]
  ring

theorem leftFusion_succ (i : ℕ) (X : ℕ → ℂ) :
    leftFusion (i+1) X=(∏ k ∈ Finset.range i, fusionPair (X (i+1)) (X k))*fusionPair (X (i+1)) (X i) := by
  exact Finset.prod_range_succ _ i

theorem leftFusion_swap_before {i j : ℕ} (h : j+1 < i) (X : ℕ → ℂ) :
    leftFusion i (swapSite j X)=leftFusion i X := by
  unfold leftFusion
  rw [swapSite_other (by omega : i≠j) (by omega : i≠j+1)]
  have hm (k : ℕ) (hk : k ∈ Finset.range i) : Equiv.swap j (j+1) k ∈ Finset.range i := by
    simp only [Finset.mem_range] at hk ⊢
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega
  apply Finset.prod_bij (fun k _ => Equiv.swap j (j+1) k) hm
  · intro a ha b hb hab
    exact (Equiv.swap j (j+1)).injective hab
  · intro k hk
    exact ⟨Equiv.swap j (j+1) k,hm k hk,by simp⟩
  · intro k hk
    rfl

theorem leftFusion_swap_after {i j : ℕ} (h : i < j) (X : ℕ → ℂ) :
    leftFusion i (swapSite j X)=leftFusion i X := by
  unfold leftFusion
  rw [swapSite_other (by omega : i≠j) (by omega : i≠j+1)]
  apply Finset.prod_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [swapSite_other (by omega : k≠j) (by omega : k≠j+1)]

theorem leftFusion_mark_right (i : ℕ) (X : ℕ → ℂ) :
    leftFusion (i+1) (swapSite i X)=leftFusion i X*fusionPair (X i) (X (i+1)) := by
  rw [leftFusion_succ]
  simp only [swapSite_right,swapSite_left]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [swapSite_other (by omega : k≠i) (by omega : k≠i+1)]

end PolynomialVacuumAlgebra

end OAI
