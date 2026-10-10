import OAI.Analysis.Laughlin.FourBody.ErrorLimit
import OAI.Analysis.Laughlin.Spin.Specializations

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

noncomputable def threeBodyInner (s : ℕ → ℕ → ℕ → ℝ) (z T t : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) : ℝ :=
  (entries.map (fun e => if e.1+e.2.1=T then sourceAlpha t e * s z T e.1 else 0)).sum

noncomputable def threeBodyTraceFormula (s : ℕ → ℕ → ℕ → ℝ) (z : ℕ) : ℝ :=
  (Certificate.rows.map (fun row =>
    (((List.range 16).filter (fun T => max z row.1 ≤ T)).map (fun T =>
      let a := threeBodyInner s z T row.1 row.2.2
      2*((row.2.1 : ℝ)/10^7)*s z T row.1*a+a^2)).sum)).sum

noncomputable def physicalThreeBodyTraceFormula (Q z : ℕ) : ℝ :=
  threeBodyTraceFormula (physicalCouplingCoefficient (2*Q-2) Q) z
noncomputable def limitThreeBodyTraceFormula (z : ℕ) : ℝ :=
  threeBodyTraceFormula (fun z T p => couplingPolynomialCoefficient
    (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p) z

theorem threeBodyInner_tendsto (z T t : ℕ) (entries : List (ℕ × ℕ × ℤ)) (hz : z ≤ T) :
    Tendsto (fun Q => threeBodyInner (physicalCouplingCoefficient (2*Q-2) Q) z T t entries)
      atTop (𝓝 (threeBodyInner (fun z T p => couplingPolynomialCoefficient
        (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p) z T t entries)) := by
  apply physical_list_sum_tendsto
  intro e he
  by_cases h : e.1+e.2.1=T
  · simp only [ite_eq_left h]
    exact tendsto_const_nhds.mul (source_threeBody_coupling_tendsto z T e.1 hz (by omega))
  · simp only [ite_eq_right h]
    exact tendsto_const_nhds

theorem physicalThreeBodyTraceFormula_tendsto (z : ℕ) :
    Tendsto (fun Q => physicalThreeBodyTraceFormula Q z) atTop
      (𝓝 (limitThreeBodyTraceFormula z)) := by
  unfold physicalThreeBodyTraceFormula limitThreeBodyTraceFormula threeBodyTraceFormula
  apply physical_list_sum_tendsto
  intro row hrow
  apply physical_list_sum_tendsto
  intro T hT
  have h : z ≤ T ∧ row.1 ≤ T := by
    simp only [List.mem_filter,decide_eq_true_eq, max_le_iff] at hT
    exact hT.2
  exact ((tendsto_const_nhds.mul (source_threeBody_coupling_tendsto z T row.1 h.1 h.2)).mul
    (threeBodyInner_tendsto z T row.1 row.2.2 h.1)).add
    ((threeBodyInner_tendsto z T row.1 row.2.2 h.1).pow 2)

end Laughlin.Spin

end OAI
