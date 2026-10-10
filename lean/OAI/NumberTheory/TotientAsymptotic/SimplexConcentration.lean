import OAI.NumberTheory.TotientAsymptotic.SimplexFixedCaps

namespace OAI

/-! Uniform two-sided concentration of bounded linear forms on a simplex. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma volume_simplex_fixed_deviation (M K : ℝ) (hM : 1 ≤ M) (hK : 0 ≤ K)
    (N m : ℕ) (hm : 2 ≤ m) (hmN : m ≤ N) (B : ℝ) (hB : 0 < B)
    (w : Fin N → ℝ) (hw : ∀ j, 0 ≤ w j ∧ w j ≤ M)
    (hS : |(∑ j,w j)-(m:ℝ)| ≤ K) (hQ : (∑ j,(w j)^2) ≤ M*((m:ℝ)+K)) :
    (volume (standardSimplex N B ∩
      {v | (1/40:ℝ) < |(∑ j,w j*v j)/(B*((m:ℝ)-1)/(N:ℝ))-1|})).toReal ≤
      2*Real.exp (3*concentrationTilt M*(K+1))*
        Real.exp (-(concentrationTilt M/100)*(m-1:ℕ))*
          (volume (standardSimplex N B)).toReal := by
  let t := B*((m:ℝ)-1)/(N:ℝ)
  let S := standardSimplex N B
  let L := S ∩ {v | (∑ j,w j*v j) ≤ (39/40)*t}
  let U := S ∩ {v | (41/40)*t ≤ ∑ j,w j*v j}
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have ht : 0 < t := div_pos (mul_pos hB (by linarith)) hn
  have hsub : S ∩ {v | (1/40:ℝ) < |(∑ j,w j*v j)/t-1|} ⊆ L ∪ U := by
    rintro v ⟨hv,hbad⟩
    by_cases hl : (∑ j,w j*v j) ≤ (39/40)*t
    · exact Or.inl ⟨hv,hl⟩
    · refine Or.inr ⟨hv,?_⟩
      by_contra hu
      have hlo : 39/40 < (∑ j,w j*v j)/t := (lt_div_iff₀ ht).mpr (lt_of_not_ge hl)
      have hup : (∑ j,w j*v j)/t < 41/40 := (div_lt_iff₀ ht).mpr (lt_of_not_ge hu)
      have habs : |(∑ j,w j*v j)/t-1| ≤ (1/40:ℝ) := abs_le.mpr ⟨by linarith,by linarith⟩
      exact (not_lt_of_ge habs) hbad
  have hfin : volume S ≠ ⊤ := by
    dsimp [S]
    rw [volume_standardSimplex N hB.le]
    exact ENNReal.ofReal_ne_top
  have hL : volume L ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hU : volume U ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hh : volume (S ∩ {v | (1/40:ℝ) < |(∑ j,w j*v j)/t-1|}) ≤ volume L+volume U :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hL,hU⟩) hh
  rw [ENNReal.toReal_add hL hU] at hr
  have hcaps := simplex_fixed_caps M K hM hK N m hm hmN B hB w hw hS hQ
  apply hr.trans
  calc
    _ ≤ 2*(Real.exp (3*concentrationTilt M*(K+1)-
        (concentrationTilt M/100)*((m:ℝ)-1))*(volume S).toReal) := by
      have hl : (volume L).toReal ≤ Real.exp (3*concentrationTilt M*(K+1)-
        (concentrationTilt M/100)*((m:ℝ)-1))*(volume S).toReal := hcaps.1
      have hu : (volume U).toReal ≤ Real.exp (3*concentrationTilt M*(K+1)-
        (concentrationTilt M/100)*((m:ℝ)-1))*(volume S).toReal := hcaps.2
      linarith only [hl,hu]
    _ = _ := by
      dsimp only [S]
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
      rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
      ring_nf

end TotientAsymptotic

end

end OAI
