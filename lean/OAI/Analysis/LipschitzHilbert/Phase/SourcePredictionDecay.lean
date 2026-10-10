import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictableDecay

namespace OAI

/-! The smaller fixed power gain used after mass normalization in the
prediction argument. The constants and polynomial exponents remain fixed. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem relative_exponential_error_le {E B : ℝ} (hE : E ≤ 1)
    (hbound : E ≤ B) (hE0 : 0 ≤ E) : Real.exp E*E ≤ Real.exp 1*B :=
  mul_le_mul (Real.exp_le_exp.mpr hE) hbound hE0 (Real.exp_pos 1).le

/-- Packet motion of order `G^(-1/4)` and any fixed polynomial times
`G^(-1/2)` from the mass factors leave a uniform `G^(-1/8)` gain. -/
theorem eventually_source_rescaled_motion (B b c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ η q C : ℝ,
      0 ≤ η → η ≤ SourceParameters.step L^(-(1/4:ℝ)) →
      0 ≤ q → q ≤ B*L^b/Real.sqrt (SourceParameters.step L) →
      0 ≤ C → C ≤ L^c →
      (1+q)*η+q*C ≤ SourceParameters.step L^(-(1/8:ℝ)) := by
  have hpoly := eventually_source_polynomial_motion (2*B) (b+c)
  have hpower := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp
    source_step_tendsto_atTop).eventually_ge_atTop 2
  filter_upwards [hpoly,hpower,eventually_ge_atTop (1:ℝ)] with L hpoly hpower hL
  intro η q C hη0 hη hq0 hq hC0 hC
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hG0 := SourceParameters.step_pos L
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hη1 : η ≤ 1 := hη.trans (Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num))
  have hc1 : 1 ≤ L^c := Real.one_le_rpow hL hc
  have hCsum : η+C ≤ 2*L^c := by linarith
  have hsmall : 2*SourceParameters.step L^(-(1/4:ℝ)) ≤
      SourceParameters.step L^(-(1/8:ℝ)) := by
    have hm := mul_le_mul_of_nonneg_right hpower
      (Real.rpow_nonneg hG0.le (-(1/4:ℝ)))
    have heq : SourceParameters.step L^(1/8:ℝ)*
        SourceParameters.step L^(-(1/4:ℝ)) =
        SourceParameters.step L^(-(1/8:ℝ)) := by
      rw [← Real.rpow_add hG0]
      norm_num
    exact hm.trans_eq heq
  calc
    _ = η+q*(η+C) := by ring
    _ ≤ SourceParameters.step L^(-(1/4:ℝ))+
        (B*L^b/Real.sqrt (SourceParameters.step L))*(2*L^c) :=
      add_le_add hη (mul_le_mul hq hCsum (by positivity) (by positivity))
    _ = SourceParameters.step L^(-(1/4:ℝ))+
        (2*B)*L^(b+c)/Real.sqrt (SourceParameters.step L) := by
      rw [Real.rpow_add hL0]
      ring
    _ ≤ SourceParameters.step L^(-(1/4:ℝ))+SourceParameters.step L^(-(1/4:ℝ)) :=
      add_le_add le_rfl hpoly
    _ = 2*SourceParameters.step L^(-(1/4:ℝ)) := by ring
    _ ≤ _ := hsmall

end LipschitzHilbert

end

end OAI
