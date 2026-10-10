import Mathlib
import OAI.Combinatorics.KMedian.Compression.RationalCompression

namespace OAI

namespace MetricKMedian
open Finset

structure IntegerLaw (Ω : Type) [Fintype Ω] where
  denominator : ℤ
  denominator_pos : 0 < denominator
  numerator : Ω → ℤ
  numerator_nonneg : ∀ i, 0 ≤ numerator i
  total : ∑ i, numerator i=denominator

namespace IntegerLaw
variable {Ω I : Type} [Fintype Ω] [Fintype I]

def rational (μ : IntegerLaw Ω) : RationalLaw Ω where
  weight i := (μ.numerator i:ℚ)/μ.denominator
  nonneg i := div_nonneg (by exact_mod_cast μ.numerator_nonneg i)
    (by exact_mod_cast μ.denominator_pos.le)
  total := by rw [← sum_div,← Int.cast_sum,μ.total]; exact div_self (by exact_mod_cast μ.denominator_pos.ne')

theorem numerator_le (μ : IntegerLaw Ω) (i : Ω) : μ.numerator i ≤ μ.denominator := by
  rw [← μ.total]
  exact single_le_sum (fun j _ => μ.numerator_nonneg j) (mem_univ i)

theorem positive_entry {z : Ω → ℤ} (hsum : ∑ i, z i=0) (hz : ∃ i, z i ≠ 0) :
    ∃ i, 0 < z i := by
  by_contra hn
  push Not at hn
  have he : ∀ i, z i=0 := by
    intro i
    have hsingle : z i ≤ 0 := hn i
    have hsum' : (∑ j, -z j)=0 := by rw [sum_neg_distrib,hsum,neg_zero]
    have hm : -z i ≤ 0 := by
      rw [← hsum']
      exact single_le_sum (fun j _ => neg_nonneg.mpr (hn j)) (mem_univ i)
    omega
  obtain ⟨i,hi⟩ := hz
  exact hi (he i)

omit [Fintype I] in

theorem eliminate (μ : IntegerLaw Ω) (feature : Ω → I → ℚ) (z : Ω → ℤ)
    (hzsum : ∑ i, z i=0)
    (hzmoment : ∀ j, ∑ i, (z i:ℚ)*feature i j=0)
    (hz : ∃ i, z i ≠ 0)
    (hzsupport : ∀ i, μ.numerator i=0 → z i=0) :
    ∃ (ν : IntegerLaw Ω) (pivot : Ω),
      0 < z pivot ∧
      ν.denominator=μ.denominator*z pivot ∧
      (∀ i, ν.numerator i=μ.numerator i*z pivot-μ.numerator pivot*z i) ∧
      ν.numerator pivot=0 ∧ μ.numerator pivot ≠ 0 ∧
      (∀ i, μ.numerator i=0 → ν.numerator i=0) ∧
      (∀ j, (∑ i, ν.rational.weight i*feature i j)=
        ∑ i, μ.rational.weight i*feature i j) := by
  classical
  let P := univ.filter (fun i => 0 < z i)
  have hP : P.Nonempty := by
    obtain ⟨i,hi⟩ := positive_entry hzsum hz
    exact ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩
  let ratio (i : Ω) : ℚ := (μ.numerator i:ℚ)/(z i:ℚ)
  obtain ⟨j,hj,he⟩ := mem_image.mp (min'_mem (P.image ratio) (hP.image _))
  have hjz : 0 < z j := (mem_filter.mp hj).2
  have hjzQ : (0:ℚ) < z j := by exact_mod_cast hjz
  have hrmin : ∀ i, 0 < z i → ratio j ≤ ratio i := by
    intro i hi
    rw [he]
    exact min'_le _ _ (mem_image_of_mem ratio (mem_filter.mpr ⟨mem_univ _,hi⟩))
  let b (i : Ω) := μ.numerator i*z j-μ.numerator j*z i
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    by_cases hzi : 0 < z i
    · have hqi : (0:ℚ) < z i := by exact_mod_cast hzi
      have hh := (div_le_div_iff₀ hjzQ hqi).mp (hrmin i hzi)
      have hhZ : μ.numerator j*z i ≤ μ.numerator i*z j := by exact_mod_cast hh
      exact sub_nonneg.mpr hhZ
    · have hle : z i ≤ 0 := le_of_not_gt hzi
      dsimp only [b]
      exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos (μ.numerator_nonneg j) hle).trans
        (mul_nonneg (μ.numerator_nonneg i) hjz.le))
  have htotal : ∑ i, b i=μ.denominator*z j := by
    simp only [b,sum_sub_distrib,← sum_mul,← mul_sum,μ.total,hzsum,mul_zero,sub_zero]
  let ν : IntegerLaw Ω := ⟨μ.denominator*z j,mul_pos μ.denominator_pos hjz,b,hb,htotal⟩
  refine ⟨ν,j,hjz,rfl,(fun _ => rfl),?_,?_,?_,?_⟩
  · dsimp only [ν,b]; ring
  · intro hj0
    exact hjz.ne' (hzsupport j hj0)
  · intro i hi
    dsimp only [ν,b]
    rw [hi,hzsupport i hi]
    ring
  · intro r
    have hzQ : (μ.denominator:ℚ) ≠ 0 := by exact_mod_cast μ.denominator_pos.ne'
    have hjQ : (z j:ℚ) ≠ 0 := hjzQ.ne'
    change (∑ i, ((b i:ℚ)/(↑(μ.denominator*z j):ℚ))*feature i r)=
      ∑ i, ((μ.numerator i:ℚ)/(μ.denominator:ℚ))*feature i r
    simp only [Int.cast_mul]
    have heq : ∀ i, ((b i:ℚ)/((μ.denominator:ℚ)*(z j:ℚ)))*feature i r=
        ((μ.numerator i:ℚ)*feature i r)/(μ.denominator:ℚ)-
        ((μ.numerator j:ℚ)/(μ.denominator:ℚ)/(z j:ℚ))*((z i:ℚ)*feature i r) := by
      intro i
      dsimp only [b]
      push_cast
      field_simp
    simp only [heq,sum_sub_distrib,← mul_sum,hzmoment,mul_zero,sub_zero]
    apply sum_congr rfl
    intro i _
    ring

theorem denominator_step_bound {D z : ℤ} {L Z : ℕ}
    (hD0 : 0 ≤ D) (hz0 : 0 ≤ z) (hD : D ≤ 2^L) (hz : z ≤ 2^Z) :
    D*z ≤ 2^(L+Z) := by
  rw [pow_add]
  exact mul_le_mul hD hz hz0 (hD0.trans hD)

end IntegerLaw
end MetricKMedian

end OAI
