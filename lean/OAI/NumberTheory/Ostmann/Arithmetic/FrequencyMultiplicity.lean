import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.FrequencyMultiplicity
open scoped BigOperators

def reducedModulus (v w s : ℤ) : ℕ :=
  s.natAbs / Nat.gcd (Nat.gcd v.natAbs w.natAbs) s.natAbs

theorem frequency_eq_signed_divisor (v w s : ℤ) (hv : v ≠ 0) :
    ∃ d ∈ (Nat.gcd v.natAbs w.natAbs).divisors,
      s = ((reducedModulus v w s * d : ℕ):ℤ) ∨
      s = -((reducedModulus v w s * d : ℕ):ℤ) := by
  let g := Nat.gcd v.natAbs w.natAbs
  let d := g.gcd s.natAbs
  have hg : g ≠ 0 := ne_of_gt (Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hv))
  refine ⟨d,Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,hg⟩,?_⟩
  have heq : reducedModulus v w s * d = s.natAbs :=
    Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  rw [heq]
  exact Int.natAbs_eq s

theorem reduced_fiber_card (v w : ℤ) (hv : v ≠ 0) (S : Finset ℤ) (a : ℕ) :
    (S.filter fun s => reducedModulus v w s=a).card ≤
      2 * (Nat.gcd v.natAbs w.natAbs).divisors.card := by
  let D := (Nat.gcd v.natAbs w.natAbs).divisors
  let f : Bool × ℕ → ℤ := fun z => if z.1 then ((a*z.2:ℕ):ℤ) else -((a*z.2:ℕ):ℤ)
  have hsub : (S.filter fun s => reducedModulus v w s=a) ⊆
      (Finset.univ ×ˢ D).image f := by
    intro s hs
    obtain ⟨d,hd,hpos|hneg⟩ := frequency_eq_signed_divisor v w s hv
    · refine Finset.mem_image.mpr ⟨(true,d),Finset.mem_product.mpr ⟨by simp,hd⟩,?_⟩
      simp only [f,ite_true]
      rw [← (Finset.mem_filter.mp hs).2]
      exact hpos.symm
    · refine Finset.mem_image.mpr ⟨(false,d),Finset.mem_product.mpr ⟨by simp,hd⟩,?_⟩
      simp only [f,Bool.false_eq_true,ite_false]
      rw [← (Finset.mem_filter.mp hs).2]
      exact hneg.symm
  calc
    _ ≤ ((Finset.univ ×ˢ D).image f).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ ×ˢ D).card := Finset.card_image_le
    _ = _ := by simp [D]

end Ostmann.Arithmetic.FrequencyMultiplicity

end

end OAI
