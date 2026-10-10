import OAI.NumberTheory.TotientAsymptotic.SimplexVolume
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

/-! An exact terminal-coordinate slice of the standard simplex. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma simplex_terminal_translate {N : ℕ} (j : Fin N) {B t : ℝ} (ht : 0 ≤ t) :
    (fun v : Fin N → ℝ => v+(Pi.single j t : Fin N → ℝ)) ⁻¹'
      (standardSimplex N B ∩ {v | t ≤ v j}) = standardSimplex N (B-t) := by
  ext v
  have hsum : (∑ i : Fin N,(v+(Pi.single j t : Fin N → ℝ)) i)=(∑ i : Fin N,v i)+t := by
    simp only [Pi.add_apply,Finset.sum_add_distrib]
    simp
  constructor
  · intro hv
    have hcap : t ≤ v j+t := by simpa using hv.2
    refine ⟨?_,?_⟩
    · intro i
      by_cases hi : i=j
      · subst i
        linarith only [hcap]
      · have hh := hv.1.1 i
        simpa [Pi.single_apply,hi] using hh
    · have hh := hv.1.2
      rw [hsum] at hh
      linarith only [hh]
  · rintro ⟨hv,hs⟩
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i
      have hi : 0 ≤ (Pi.single j t : Fin N → ℝ) i := by
        by_cases hij : i=j
        · subst i
          simpa using ht
        · simp [hij]
      exact add_nonneg (hv i) hi
    · change (∑ i,(v+(Pi.single j t : Fin N → ℝ)) i) ≤ B
      rw [hsum]
      linarith only [hs]
    · have hj := hv j
      change t ≤ (v+(Pi.single j t : Fin N → ℝ)) j
      simpa using (show t ≤ v j+t by linarith only [hj])

lemma volume_simplex_terminal_cap {N : ℕ} (j : Fin N) {B t : ℝ}
    (ht : 0 ≤ t) (htB : t ≤ B) :
    volume (standardSimplex N B ∩ {v | t ≤ v j}) =
      ENNReal.ofReal ((B-t)^N/(N.factorial:ℝ)) := by
  have he := simplex_terminal_translate (B:=B) j ht
  have hm := measure_preimage_add_right (volume : Measure (Fin N → ℝ))
    ((Pi.single j t : Fin N → ℝ)) (standardSimplex N B ∩ {v | t ≤ v j})
  rw [he] at hm
  rw [← hm]
  exact volume_standardSimplex N (sub_nonneg.mpr htB)

lemma simplex_cap_power_bound {B t : ℝ} (hB : 0 < B) (_ht : 0 ≤ t)
    (htB : t ≤ B) (N : ℕ) :
    (B-t)^N ≤ Real.exp (-(N:ℝ)*t/B)*B^N := by
  have hbase : 1-t/B ≤ Real.exp (-t/B) := by
    simpa only [neg_div,sub_eq_add_neg,add_comm] using (Real.add_one_le_exp (-(t/B)))
  have hbase0 : 0 ≤ 1-t/B := by
    have hh := (div_le_one hB).mpr htB
    linarith only [hh]
  have hp := pow_le_pow_left₀ hbase0 hbase N
  have he : B-t=(1-t/B)*B := by field_simp
  rw [he,mul_pow]
  apply (mul_le_mul_of_nonneg_right hp (pow_nonneg hB.le N)).trans_eq
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-- The exponential bound also covers caps beyond the whole simplex. -/
lemma simplex_positive_part_power_bound {B t : ℝ} (hB : 0 < B) (ht : 0 ≤ t)
    {N : ℕ} (hN : 0 < N) :
    (max (B-t) 0)^N ≤ Real.exp (-(N:ℝ)*t/B)*B^N := by
  by_cases htB : t ≤ B
  · rw [max_eq_left (sub_nonneg.mpr htB)]
    exact simplex_cap_power_bound hB ht htB N
  · rw [max_eq_right (by linarith only [not_le.mp htB]),zero_pow hN.ne']
    positivity

lemma volume_simplex_terminal_cap_le {N : ℕ} (j : Fin N) {B t : ℝ}
    (hB : 0 < B) (ht : 0 ≤ t) (htB : t ≤ B) :
    (volume (standardSimplex N B ∩ {v | t ≤ v j})).toReal ≤
      Real.exp (-(N:ℝ)*t/B)*(volume (standardSimplex N B)).toReal := by
  rw [volume_simplex_terminal_cap j ht htB,volume_standardSimplex N hB.le,
    ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal (by positivity)]
  have hh := div_le_div_of_nonneg_right (simplex_cap_power_bound hB ht htB N)
    (Nat.cast_nonneg N.factorial)
  simpa only [mul_div_assoc] using hh

end TotientAsymptotic

end

end OAI
