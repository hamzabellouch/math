import Mathlib
import OAI.Combinatorics.KMedian.Compression.AffineKernel
import OAI.Combinatorics.KMedian.Compression.ComputedPivot

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem eliminateAt_preserves {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) (z : Fin n → ℤ) (p : Fin n)
    (hp : 0 < z p) (hmin : ∀ i, 0 < z i → ratio μ z p ≤ ratio μ z i)
    (hzsum : ∑ i, z i=0) (hzmoment : ∀ j, ∑ i, (z i:ℚ)*v i j=0)
    (hzsupport : ∀ i, μ.numerator i=0 → z i=0) :
    let ν := eliminateAt μ z p hp hmin hzsum
    ν.numerator p=0 ∧ μ.numerator p ≠ 0 ∧
      (∀ i, μ.numerator i=0 → ν.numerator i=0) ∧
      ν.support ⊆ μ.support.erase p ∧
      ∀ j, (∑ i, ν.rational.weight i*v i j)=∑ i, μ.rational.weight i*v i j := by
  dsimp only
  have hz : (eliminateAt μ z p hp hmin hzsum).numerator p=0 := by
    rw [eliminateAt_numerator,sub_self]
  have hn : μ.numerator p ≠ 0 := by intro hp0; exact hp.ne' (hzsupport p hp0)
  have hs : ∀ i, μ.numerator i=0 → (eliminateAt μ z p hp hmin hzsum).numerator i=0 := by
    intro i hi
    rw [eliminateAt_numerator,hi,hzsupport i hi]
    ring
  refine ⟨hz,hn,hs,?_,?_⟩
  · intro i hi
    have hni := (mem_support _ i).mp hi
    apply mem_erase.mpr
    refine ⟨?_,(μ.mem_support i).mpr ?_⟩
    · intro he; subst i; exact hni hz
    · intro he; exact hni (hs i he)
  · intro j
    have hD : (μ.denominator:ℚ) ≠ 0 := by exact_mod_cast μ.denominator_pos.ne'
    have hpQ : (z p:ℚ) ≠ 0 := by exact_mod_cast hp.ne'
    change (∑ i, (((eliminateAt μ z p hp hmin hzsum).numerator i:ℚ)/
        ((μ.denominator*z p:ℤ):ℚ))*v i j)=_
    simp only [eliminateAt_numerator,Int.cast_mul,Int.cast_sub]
    have heq : ∀ i, (((μ.numerator i:ℚ)*(z p:ℚ)-(μ.numerator p:ℚ)*(z i:ℚ))/
        ((μ.denominator:ℚ)*(z p:ℚ)))*v i j=
        ((μ.numerator i:ℚ)*v i j)/(μ.denominator:ℚ)-
        ((μ.numerator p:ℚ)/(μ.denominator:ℚ)/(z p:ℚ))*((z i:ℚ)*v i j) := by
      intro i
      field_simp
    simp only [heq,sum_sub_distrib,← mul_sum,hzmoment,mul_zero,sub_zero]
    apply sum_congr rfl
    intro i _
    dsimp only [rational]
    ring

end MetricKMedian.IntegerLaw

end OAI
