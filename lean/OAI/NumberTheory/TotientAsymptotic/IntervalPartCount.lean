import OAI.NumberTheory.TotientAsymptotic.IntervalPartQuotient

namespace OAI

/-! Counting distinct values by their complete prime-interval parts. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem interval_part_count : ∃ C : ℝ,0 < C ∧ ∀ S X z : ℕ,
    2 ≤ S → S ≤ z → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ X ∧ z*partBetween n S z ≤ X) →
    (Q.card:ℝ) ≤ (C*X*Real.log S/Real.log z)*
      ∑ d ∈ Q.image (fun n => partBetween n S z),(d:ℝ)⁻¹ := by
  classical
  obtain ⟨C,hC,hbound⟩ := interval_part_fiber_bound
  refine ⟨C,hC,?_⟩
  intro S X z hS hSz Q hQ
  let f := fun n => partBetween n (S:ℝ) (z:ℝ)
  have hmap : ∀ n ∈ Q,f n ∈ Q.image f := fun n hn => Finset.mem_image.mpr ⟨n,hn,rfl⟩
  have hf (d : ℕ) (hd : d ∈ Q.image f) :
      ((Q.filter (fun n => f n=d)).card:ℝ) ≤
      (C*X*Real.log S/Real.log z)*(d:ℝ)⁻¹ := by
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hd
    have hm : 0 < f n := partBetween_pos n S z
    have hz : z ≤ X/f n := (Nat.le_div_iff_mul_le hm).mpr (hQ n hn).2.2
    have hb := hbound S X z (f n) hm hS hSz hz (Q.filter (fun r => f r=f n)) (by
      intro r hr
      obtain ⟨hr,he⟩ := Finset.mem_filter.mp hr
      exact ⟨(hQ r hr).1,(hQ r hr).2.1,he⟩)
    convert hb using 1; ring
  have he := Finset.sum_fiberwise_of_maps_to hmap (fun _ => (1:ℝ))
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at he
  calc
    _ = ∑ d ∈ Q.image f,((Q.filter (fun n => f n=d)).card:ℝ) := he.symm
    _ ≤ ∑ d ∈ Q.image f,(C*X*Real.log S/Real.log z)*(d:ℝ)⁻¹ := Finset.sum_le_sum hf
    _ = _ := by rw [← Finset.mul_sum]

end TotientAsymptotic

end

end OAI
