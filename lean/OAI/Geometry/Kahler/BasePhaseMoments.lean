import OAI.Geometry.Kahler.BasePhaseReal

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma real_cast_eq_conj (z : ℂ) : (z.re:ℂ)=(z+star z)/2 := by
  apply Complex.ext <;> simp

lemma phase_real_moment (a : ℂ) (m : ℤ) (n : ℕ) (hm : 0 < m) :
    (∫ z : Circle, phaseChar n z*((a*phaseChar m z).re:ℂ) ∂circleMeasure) =
      if m=(n:ℤ) then star a/2 else 0 := by
  have he : ∀ z : Circle, phaseChar n z*((a*phaseChar m z).re:ℂ) =
      (a/2)*phaseChar ((n:ℤ)+m) z + (star a/2)*phaseChar ((n:ℤ)-m) z := by
    intro z
    rw [real_cast_eq_conj,star_mul,phaseChar_conj]
    rw [phaseChar_add,sub_eq_add_neg,phaseChar_add]
    ring
  simp_rw [he]
  rw [integral_add]
  · rw [integral_const_mul,integral_const_mul,circle_char_mean,circle_char_mean]
    have hplus : (n:ℤ)+m ≠ 0 := by omega
    rw [ite_eq_right hplus,mul_zero,zero_add]
    by_cases heq : m=(n:ℤ)
    · simp [heq]
    · have hminus : (n:ℤ)-m ≠ 0 := by omega
      simp [hminus,heq]
  · exact (compact_continuous_integrable (phaseChar_continuous _)).const_mul _
  · exact (compact_continuous_integrable (phaseChar_continuous _)).const_mul _

lemma phase_real_sum_moment (s : Finset ℤ) (a : ℤ → ℂ) (n : ℕ)
    (hs : ∀ m ∈ s, 0 < m) :
    (∫ z : Circle, phaseChar n z*((phaseSum s a z).re:ℂ) ∂circleMeasure) =
      ∑ m ∈ s, if m=(n:ℤ) then star (a m)/2 else 0 := by
  classical
  have he : ∀ z : Circle, phaseChar n z*((phaseSum s a z).re:ℂ) =
      ∑ m ∈ s, phaseChar n z*((a m*phaseChar m z).re:ℂ) := by
    intro z
    simp only [phaseSum,Complex.re_sum,Complex.ofReal_sum,Finset.mul_sum]
  simp_rw [he]
  rw [MeasureTheory.integral_finsetSum s (fun m hm => compact_continuous_integrable (by
    exact (phaseChar_continuous _).mul (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (continuous_const.mul (phaseChar_continuous _))))))]
  exact Finset.sum_congr rfl (fun m hm => phase_real_moment _ _ _ (hs m hm))

end PinchedHartogs.BaseConstruction

end

end OAI
