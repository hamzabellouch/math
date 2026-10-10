import Mathlib
import OAI.RepresentationTheory.PartialPermutation.TrivialRepresentation

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
open scoped BigOperators MonoidAlgebra Classical

variable {G : Type*} [Group G] [Fintype G]
def nontrivialEnergy (f : G → ℝ) : ℝ :=
  ∑ c ∈ Finset.univ.erase (trivialIndex G), (irreducibleDegree c : ℝ) *
    hsNormSq (V := irreducibleSpace c)
      (complexFourier (V := irreducibleSpace c) (irreducibleRep c) (fun g => (f g : ℂ)))

theorem centered_plancherel (f : G → ℝ) :
    (Fintype.card G : ℝ) * ∑ g, (f g - (∑ h, f h) / Fintype.card G)^2 =
      nontrivialEnergy f := by
  have h := finite_group_plancherel
    (fun g => (f g : ℂ) - (∑ h, (f h : ℂ)) / Fintype.card G)
  have hz : complexFourier (irreducibleRep (trivialIndex G))
      (fun g => (f g : ℂ) - (∑ h, (f h : ℂ)) / Fintype.card G) = 0 := by
    rw [complexFourier_centered, ite_eq_left rfl, complexFourier_trivial, sub_self]
  have hj (c : IrreducibleIndex G) (hc : c ≠ trivialIndex G) :
      complexFourier (irreducibleRep c)
        (fun g => (f g : ℂ) - (∑ h, (f h : ℂ)) / Fintype.card G) =
      complexFourier (irreducibleRep c) (fun g => (f g : ℂ)) := by
    rw [complexFourier_centered, ite_eq_right hc, smul_zero, sub_zero]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (trivialIndex G)), hz] at h
  simp only [hsNormSq, map_zero, Complex.zero_re, mul_zero, add_zero] at h
  have hn (g : G) :
      ‖(f g : ℂ) - (∑ h, (f h : ℂ)) / Fintype.card G‖^2 =
        (f g - (∑ h, f h) / Fintype.card G)^2 := by
    rw [← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hn] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hj c (Finset.mem_erase.mp hc).1]
  rfl

lemma uniform_square_decomposition (f : G → ℝ) :
    (Fintype.card G : ℝ) * ∑ g, (f g - 1 / Fintype.card G)^2 =
      (1 - ∑ g, f g)^2 +
        (Fintype.card G : ℝ) * ∑ g, (f g - (∑ h, f h) / Fintype.card G)^2 := by
  have hN : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem deficit_plancherel (f : G → ℝ) :
    (∑ g, |f g - 1 / Fintype.card G|)^2 ≤ (1 - ∑ g, f g)^2 +
      nontrivialEnergy f := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset G)
    (fun _ => (1 : ℝ)) (fun g => |f g - 1 / Fintype.card G|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, sq_abs] at hcs
  rw [uniform_square_decomposition, centered_plancherel] at hcs
  exact hcs

theorem normalization_tv_le {X : Type*} [Fintype X] (f μ : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hdom : ∀ x, f x ≤ μ x) (hm : ∑ x, μ x = 1)
    (hz : 0 < ∑ x, f x) :
    (∑ x, |f x / (∑ y, f y) - μ x|) / 2 ≤ 1 - ∑ x, f x := by
  have hz1 : ∑ x, f x ≤ 1 := (Finset.sum_le_sum (fun x _ => hdom x)).trans_eq hm
  have hnorm (x : X) : |f x / (∑ y, f y) - f x| =
      f x / (∑ y, f y) - f x := by
    apply abs_of_nonneg
    exact sub_nonneg.mpr ((le_div_iff₀ hz).mpr (mul_le_of_le_one_right (hf x) hz1))
  have hdiff (x : X) : |f x - μ x| = μ x - f x := abs_sub_comm _ _ |>.trans
    (abs_of_nonneg (sub_nonneg.mpr (hdom x)))
  have htri (x : X) : |f x / (∑ y, f y) - μ x| ≤
      (f x / (∑ y, f y) - f x) + (μ x - f x) := by
    simpa only [hnorm, hdiff] using abs_sub_le (f x / (∑ y, f y)) (f x) (μ x)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset X)) (fun x _ => htri x)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, hm,
    div_self hz.ne'] at hs
  linarith

end
end PartialPermutation

end

end OAI
