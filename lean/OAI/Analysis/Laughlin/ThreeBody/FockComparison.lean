import OAI.Analysis.Laughlin.ThreeBody.FockNull
import OAI.Analysis.Laughlin.ThreeBody.FockTail
import OAI.Analysis.Laughlin.ThreeBody.TraceComparison

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory Filter
open scoped BigOperators Matrix

theorem physicalThreeBodyTraceFormula_high (Q z : ℕ) (hz : 15 < z) :
    physicalThreeBodyTraceFormula Q z=0 := by
  have he (t : ℕ) : (List.range 16).filter (fun T => max z t ≤ T) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro T hT
    simp only [List.mem_range] at hT
    simp only [decide_eq_true_eq,max_le_iff]
    omega
  simp only [physicalThreeBodyTraceFormula,threeBodyTraceFormula,he,List.map_nil,List.sum_nil,
    List.map_const',List.sum_replicate,nsmul_zero]

theorem physical_threeBody_Fock_haar_real (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) :
    (∫ g, contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal)
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re =
      ∑ z : Fin (Q+1), (physicalThreeBodyTraceFormula Q z.val/(coupledWeight Q z.val+1 : ℕ)) *
        (contractionForm Q (sourceThreeEnd Q) ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re := by
  rw [physical_threeBody_Fock_haar Q hQ,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Complex.ofReal_natCast,← Complex.ofReal_div]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem physical_threeBody_Fock_comparison_eventually :
    ∀ᶠ Q : ℕ in atTop, ∃ hQ : 15 ≤ Q, ∀ x : Space Q,
      (2*Q-2+1 : ℕ) * (∫ g, contractionForm Q (sourceThreeEnd Q)
        ((physicalThreeBodyMatrix Q).map Complex.ofReal) (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re ≤
      ∑ z : Fin (Q+1), if z.val ≤ 15 then gramEigenvalueFormula Q z.val *
        (contractionForm Q (sourceThreeEnd Q)
          ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re else 0 := by
  filter_upwards [source_threeBody_physical_traces_strict_eventually] with Q h
  obtain ⟨hQ,hs⟩ := h
  refine ⟨hQ,fun x => ?_⟩
  rw [physical_threeBody_Fock_haar_real Q hQ,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  by_cases h15 : z.val ≤ 15
  · rw [ite_eq_left h15]
    by_cases hn : z.val=0 ∨ z.val=1 ∨ z.val=3
    · rw [physical_threeBody_Fock_null Q (by omega) z hn]
      simp
    · have hm : z.val ∈ [2,4,5,6,7,8,9,10,11,12,13,14,15] := by
        simp only [List.mem_cons]
        omega
      have ht := hs z hm
      rw [source_physical_threeBody_trace_identity Q hQ] at ht
      have hr := threeBody_dimension_ratio Q z.val (by omega) (by omega)
      change _ = threeBodyDimensionRatio Q z.val at hr
      rw [← hr] at ht
      have ha : (0 : ℝ) < (2*Q-2+1 : ℕ) := by positivity
      have hd : (0 : ℝ) < (coupledWeight Q z.val+1 : ℕ) := by positivity
      have hc : (2*Q-2+1 : ℕ) *
          (physicalThreeBodyTraceFormula Q z.val/(coupledWeight Q z.val+1 : ℕ)) ≤
            gramEigenvalueFormula Q z.val := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hd).mpr
        have hh := mul_lt_mul_of_pos_left ht ha
        have he : ((2*Q-2+1 : ℕ) : ℝ) *
            (((coupledWeight Q z.val+1 : ℕ)/(2*Q-2+1 : ℕ) : ℝ) * gramEigenvalueFormula Q z.val) =
            gramEigenvalueFormula Q z.val*(coupledWeight Q z.val+1 : ℕ) := by
          field_simp
        rw [he] at hh
        exact hh.le
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
        (physical_threeBody_projector_nonneg Q (by omega) z x)
  · rw [ite_eq_right h15,physicalThreeBodyTraceFormula_high Q z.val (by omega)]
    simp

end Laughlin.Fock

end OAI
