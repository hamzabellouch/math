import Mathlib
import OAI.Combinatorics.KMedian.Rounding.ExactRounding
import OAI.Combinatorics.KMedian.Probability.Conditioning
import OAI.Combinatorics.KMedian.Process.CopyState

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type} [Fintype F] [DecidableEq F] {Δ : ℕ}

def embedSlots (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) : (Σ a, Fin (n a)) → Copy (F := F) Δ :=
  fun a => (a.1,⟨a.2.val,lt_of_lt_of_le a.2.isLt (hn a.1)⟩)

omit [Fintype F] [DecidableEq F] in
theorem embedSlots_injective (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) : Function.Injective (embedSlots n hn) := by
  rintro ⟨a,h⟩ ⟨b,k⟩ he
  have hab : a=b := congrArg Prod.fst he
  subst b
  have hhk : h=k := Fin.ext (congrArg (fun x : Copy (F := F) Δ => x.2.val) he)
  subst k
  rfl

def activeSlots (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) : Finset (Copy (F := F) Δ) :=
  univ.image (embedSlots n hn)

theorem activeSlots_mass (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) (g : ℝ) :
    mass g (activeSlots n hn)=∑ a, g*(n a:ℝ) := by
  rw [mass,activeSlots,card_image_of_injective _ (embedSlots_injective n hn),card_univ,Fintype.card_sigma]
  rw [Nat.cast_sum,mul_sum]
  simp only [Fintype.card_fin]

theorem assignment_copies (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) (r d : F → ℝ) {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (hr0 : ∀ a, 0 ≤ r a) (hr1 : ∀ a, r a ≤ g*(n a:ℝ)) (hsum : ∑ a, r a=1) :
    ∃ S : Finset (Copy (F := F) Δ), S ⊆ activeSlots n hn ∧ mass g S=1 ∧
      PhysicalPotential.cost g (fun a => d a.1) S ≤ ∑ a, r a*d a := by
  classical
  let p : (Σ a, Fin (n a)) → ℝ := fun a => r a.1/(g*(n a.1:ℝ))
  have hzero : ∀ a, n a=0 → r a=0 := by
    intro a ha
    apply le_antisymm _ (hr0 a)
    simpa only [ha,Nat.cast_zero,mul_zero] using hr1 a
  have hp0 : ∀ a, 0 ≤ p a := fun a => div_nonneg (hr0 a.1) (mul_nonneg hg.le (Nat.cast_nonneg _))
  have hp1 : ∀ a, p a ≤ 1 := by
    intro a
    have hn0 : 0 < (n a.1:ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt a.2.isLt)
    exact (div_le_one (mul_pos hg hn0)).mpr (hr1 a.1)
  have hcancel : ∀ a, (n a:ℝ)*(r a/(g*(n a:ℝ)))=r a/g := by
    intro a
    by_cases ha : n a=0
    · simp only [ha,hzero a ha,Nat.cast_zero,mul_zero,zero_div]
    · have hnz : (n a:ℝ) ≠ 0 := by exact_mod_cast ha
      field_simp
  have hps : ∑ a, p a=(Δ:ℝ) := by
    rw [Fintype.sum_sigma]
    simp only [p,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,hcancel]
    rw [← sum_div,hsum]
    exact (div_eq_iff hg.ne').mpr (by nlinarith only [hunit])
  obtain ⟨μ,hcard,hm,_⟩ := WeightedRounding.exact_law p Δ hp0 hp1 hps
  let cost := fun S : Finset (Σ a, Fin (n a)) => g*∑ a ∈ S, d a.1
  have hcost : μ.expect cost=∑ a, r a*d a := by
    have he : ∀ S, cost S=∑ a, (if a ∈ S then (1:ℝ) else 0)*(g*d a.1) := by
      intro S
      simp only [cost,ite_mul,one_mul,zero_mul,sum_ite_mem,univ_inter,mul_sum]
    change μ.expect (fun S => cost S)=_
    simp_rw [he]
    rw [FiniteLaw.expect_sum]
    have hm' : ∀ a, μ.expect (fun S => if a ∈ S then (1:ℝ) else 0)=p a := hm
    simp only [FiniteLaw.expect_mul_right,hm']
    rw [Fintype.sum_sigma]
    simp only [p,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    apply sum_congr rfl
    intro a _
    calc
      _ = ((n a:ℝ)*(r a/(g*(n a:ℝ))))*g*d a := by ring
      _ = _ := by rw [hcancel]; field_simp
  obtain ⟨S,hS,hC⟩ := μ.exists_support_le_expect cost
  refine ⟨S.image (embedSlots n hn),Finset.image_subset_image (subset_univ S),?_,?_⟩
  · rw [mass,card_image_of_injective _ (embedSlots_injective n hn),hcard S hS]
    exact hunit
  · rw [PhysicalPotential.cost,sum_image (fun a _ b _ he => embedSlots_injective n hn he)]
    change (∑ a ∈ S, g*d a.1) ≤ ∑ a, r a*d a
    rw [← mul_sum]
    exact hC.trans_eq hcost

end MetricKMedian.CopyState
end
end

end OAI
