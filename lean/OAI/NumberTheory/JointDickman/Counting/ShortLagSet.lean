import OAI.NumberTheory.JointDickman.Counting.ArithmeticLagCorrelations

namespace OAI

/-! # The singular factor has bounded mean on both signs of the short lags -/

namespace JointDickman
open Finset

def nonzeroShortLags (H : ℕ) : Finset ℤ := (Icc (-(H : ℤ)) H).erase 0

theorem mem_nonzeroShortLags {H : ℕ} {j : ℤ} :
    j ∈ nonzeroShortLags H ↔ j ≠ 0 ∧ j.natAbs ≤ H := by
  simp only [nonzeroShortLags, mem_erase, mem_Icc]
  constructor
  · rintro ⟨hj,hl,hu⟩
    refine ⟨hj,?_⟩
    have h : |j| ≤ (H : ℤ) := abs_le.mpr ⟨hl,hu⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · rintro ⟨hj,h⟩
    have h' : |j| ≤ (H : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast h
    exact ⟨hj,(abs_le.mp h').1,(abs_le.mp h').2⟩

theorem nonzeroShortLags_eq (H : ℕ) :
    nonzeroShortLags H = (Ioc 0 H).image (fun n : ℕ => (n : ℤ)) ∪
      (Ioc 0 H).image (fun n : ℕ => -(n : ℤ)) := by
  ext j
  rw [mem_nonzeroShortLags, mem_union]
  constructor
  · rintro ⟨hj,hjH⟩
    have hn : j.natAbs ∈ Ioc 0 H := mem_Ioc.mpr ⟨Int.natAbs_pos.mpr hj,hjH⟩
    by_cases h : 0 ≤ j
    · exact Or.inl (mem_image.mpr ⟨j.natAbs,hn,by rw [Int.natCast_natAbs,abs_of_nonneg h]⟩)
    · exact Or.inr (mem_image.mpr ⟨j.natAbs,hn,by
        rw [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge h),neg_neg]⟩)
  · intro hj
    rcases hj with hj | hj
    · obtain ⟨n,hn,rfl⟩ := mem_image.mp hj
      simp only [Int.natAbs_natCast]
      exact ⟨by exact_mod_cast (mem_Ioc.mp hn).1.ne', (mem_Ioc.mp hn).2⟩
    · obtain ⟨n,hn,rfl⟩ := mem_image.mp hj
      simp only [Int.natAbs_neg,Int.natAbs_natCast,neg_ne_zero]
      exact ⟨by exact_mod_cast (mem_Ioc.mp hn).1.ne', (mem_Ioc.mp hn).2⟩

theorem sum_shortLag_natAbs (H : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ nonzeroShortLags H, f j.natAbs) = 2*∑ n ∈ Ioc 0 H, f n := by
  classical
  have hd : Disjoint ((Ioc 0 H).image (fun n : ℕ => (n : ℤ)))
      ((Ioc 0 H).image (fun n : ℕ => -(n : ℤ))) := by
    apply disjoint_left.mpr
    intro j hj hk
    obtain ⟨n,hn,hnj⟩ := mem_image.mp hj
    obtain ⟨m,hm,hmj⟩ := mem_image.mp hk
    have hn0 := (mem_Ioc.mp hn).1
    have hm0 := (mem_Ioc.mp hm).1
    omega
  rw [nonzeroShortLags_eq, sum_union hd, sum_image, sum_image]
  · simp only [Int.natAbs_natCast,Int.natAbs_neg]
    ring
  · intro a _ b _ hab
    exact Int.ofNat_inj.mp (neg_injective hab)
  · intro a _ b _ hab
    exact Int.ofNat_inj.mp hab

theorem shortLag_singular_sum (H : ℕ) :
    (∑ j ∈ nonzeroShortLags H, singularFactor 24 j.natAbs) ≤
      (2*Real.exp 24)*(H : ℝ) := by
  rw [sum_shortLag_natAbs]
  have h := singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) 1 H
  simp only [pow_one, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, mul_one] at h
  nlinarith

end JointDickman

end OAI
