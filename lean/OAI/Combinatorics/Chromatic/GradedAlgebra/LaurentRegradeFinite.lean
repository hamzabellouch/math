import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.NonpRegradeFaithful
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentRegrade

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ) (B D : ℕ)
local instance laurentRegradeFiniteRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentRegradeFiniteAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentRegradeFiniteAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

lemma sum_range_eq_of_tails_zero {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (a b : ℕ) (ha : ∀n,a≤n → f n=0) (hb : ∀n,b≤n → f n=0) :
    ∑n∈Finset.range a,f n=∑n∈Finset.range b,f n := by
  have H (c : ℕ) (hc : c ≤ max a b) (h : ∀n,c≤n → f n=0) :
      ∑n∈Finset.range c,f n=∑n∈Finset.range (max a b),f n := by
    apply Finset.sum_subset (Finset.range_mono hc)
    intro n hn hnc
    exact h n (by simpa only [Finset.mem_range,not_lt] using hnc)
  exact (H a (le_max_left _ _) ha).trans (H b (le_max_right _ _) hb).symm

lemma laurentRegrade_off_diagonal {f : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (d : ℕ) (z : ℤ) (m : M)
    (hm : ¬(d=(δ m).toNat ∧ z=κ m)) :
    (coeff d (laurentRegrade v Ω δ κ B f hf)).coeff z m=0 := by
  rw [laurentRegrade_coeff,nonp_torus_eval_sum]
  apply Finset.sum_eq_zero
  intro n hn
  rw [laurentHomogenize_coeff,ite_eq_right hm]

lemma laurentRegrade_finite {f : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : RegradeBound v Ω δ D f) (d : ℕ) :
    coeff d (laurentRegrade v Ω δ κ B f hf)=
      coeff d (laurentHomogenize v Ω δ κ (coeff d (regrade v Ω δ D f))) := by
  apply HahnSeries.ext
  funext z
  ext m
  rw [laurentRegrade_coeff,nonp_torus_eval_sum,laurentHomogenize_coeff]
  by_cases h : d=(δ m).toNat ∧ z=κ m
  · rw [ite_eq_left h,regrade_coeff_eval,ite_eq_left h.1]
    simp_rw [laurentHomogenize_coeff,ite_eq_left h]
    apply sum_range_eq_of_tails_zero
    · intro n hn
      by_contra hm
      obtain ⟨hd,hk,he⟩:=hf n m hm
      have hD : δ m=(d:ℤ) := by rw [h.1,Int.toNat_of_nonneg hd]
      rw [hD,←h.2] at he
      omega
    · intro n hn
      by_contra hm
      have H:=(hg n m hm).2
      rw [←h.1] at H
      omega
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro n hn
    rw [laurentHomogenize_coeff,ite_eq_right h]

lemma laurentRegrade_finite_read {f : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : RegradeBound v Ω δ D f)
    (d : ℕ) (z : ℤ) (m : M) :
    (coeff d (laurentRegrade v Ω δ κ B f hf)).coeff z m=
      if z=κ m then coeff d (regrade v Ω δ D f) m else 0 := by
  rw [laurentRegrade_finite v Ω δ κ B D hf hg,laurentHomogenize_coeff]
  by_cases he : d=(δ m).toNat
  · simp only [he,true_and]
  · rw [regrade_coeff_eval,ite_eq_right he]
    simp
end
end ElementaryPositivity.QuantumTorus

end

end OAI
