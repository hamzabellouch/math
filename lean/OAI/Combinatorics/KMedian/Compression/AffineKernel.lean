import Mathlib
import OAI.Combinatorics.KMedian.Compression.AffineElimination
import OAI.Combinatorics.KMedian.Compression.FullIntegerKernel

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset
variable {Ω I : Type} [Fintype Ω] [Fintype I]

def support (μ : IntegerLaw Ω) : Finset Ω :=
  univ.filter (fun i => μ.numerator i ≠ 0)

@[simp] theorem mem_support (μ : IntegerLaw Ω) (i : Ω) :
    i ∈ μ.support ↔ μ.numerator i ≠ 0 := by simp [support]

theorem affine_kernel (μ : IntegerLaw Ω) (v : Ω → I → ℤ) (L : ℕ)
    (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) (hsize : Fintype.card I+1 < μ.support.card) :
    ∃ z : Ω → ℤ, (∃ i, z i ≠ 0) ∧ (∑ i, z i=0) ∧
      (∀ j, ∑ i, (z i:ℚ)*(v i j:ℚ)=0) ∧
      (∀ i, μ.numerator i=0 → z i=0) ∧
      ∀ i, |z i| ≤ (2:ℤ)^(2*(Fintype.card I+1)*(Fintype.card I+1+L)) := by
  classical
  let V : Matrix (Option I) ↥μ.support ℤ := fun j i => j.elim 1 (fun j => v i.val j)
  have hV : ∀ j i, |V j i| ≤ (2:ℤ)^L := by
    intro j i
    cases j with
    | none => simpa only [V,Option.elim_none,abs_one] using (one_le_pow₀ (by norm_num : (1:ℤ) ≤ 2))
    | some j => exact hv i.val j
  have hgt : Fintype.card (Option I) < Fintype.card ↥μ.support := by
    simpa only [Fintype.card_option,Fintype.card_coe] using hsize
  obtain ⟨zS,hne,hb,hker⟩ := Compression.full_integer_kernel V L hV hgt
  let z : Ω → ℤ := fun i => if h : i ∈ μ.support then zS ⟨i,h⟩ else 0
  have hzval : ∀ i : ↥μ.support, z i.val=zS i := by
    intro i
    simp only [z,dite_eq_left i.property]
  have hext (g : Ω → ℤ) : (∑ i, z i*g i)=∑ i : ↥μ.support, zS i*g i.val := by
    calc
      _ = ∑ i ∈ μ.support, z i*g i := by
        symm
        apply sum_subset (subset_univ _)
        intro i _ hi
        simp only [z,dite_eq_right hi,zero_mul]
      _ = _ := by
        rw [← sum_coe_sort]
        exact sum_congr rfl (fun i _ => by rw [hzval])
  refine ⟨z,?_,?_,?_,?_,?_⟩
  · obtain ⟨i,hi⟩ := hne
    exact ⟨i.val,by rwa [hzval]⟩
  · have hh := hker none
    change (∑ i, zS i*1)=0 at hh
    simpa only [mul_one] using (hext (fun _ => 1)).trans hh
  · intro j
    have hh := hker (some j)
    change (∑ i, zS i*v i.val j)=0 at hh
    have hh' := (hext (fun i => v i j)).trans hh
    exact_mod_cast hh'
  · intro i hi
    have hs : i ∉ μ.support := by simpa only [mem_support,not_not] using hi
    exact dite_eq_right hs
  · intro i
    by_cases hi : i ∈ μ.support
    · rw [show z i=zS ⟨i,hi⟩ from dite_eq_left hi]
      simpa only [Fintype.card_option] using hb ⟨i,hi⟩
    · rw [show z i=0 from dite_eq_right hi,abs_zero]
      positivity

end MetricKMedian.IntegerLaw

end OAI
