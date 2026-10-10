import OAI.Analysis.Laughlin.FourBody.ErrorCertificate
import OAI.Analysis.Laughlin.ThreeBody.Radical
import OAI.Analysis.Laughlin.ThreeBody.TraceLimit

namespace OAI

namespace Laughlin.Spin

 theorem threeBodyInner_certificate (z T t : ℕ) (hz : z ≤ T)
    (entries : List (ℕ × ℕ × ℤ)) :
    threeBodyInner (fun z T p => couplingPolynomialCoefficient
      (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p) z T t entries =
      (threeBodyRadical z T t / 10^7) * (Certificate.X entries z T : ℝ) := by
  induction entries with
  | nil => simp [threeBodyInner,Certificate.X]
  | cons e es ih =>
    simp only [threeBodyInner,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    change _ = (threeBodyRadical z T t/10^7) *
      (((if e.1+e.2.1=T then e.2.2*Certificate.U 2 z T e.1 else 0)+Certificate.X es z T : ℤ) : ℝ)
    rw [Int.cast_add]
    by_cases he : e.1+e.2.1=T
    · rw [ite_eq_left he,ite_eq_left he,sourceAlpha_factor,
        source_threeBody_radical_coefficient z T e.1 hz (by omega)]
      simp only [Int.cast_mul]
      have hc := threeBody_alpha_radical_cancel z T t e.1 e.2.1 he
      calc
        _ = ((e.2.2 : ℝ)*(Certificate.U 2 z T e.1 : ℝ)/10^7) *
            (alphaRadical t e.1 e.2.1 * threeBodyRadical z T e.1) +
            threeBodyRadical z T t/10^7 * (Certificate.X es z T : ℝ) := by ring
        _ = _ := by rw [hc]; ring
    · simp [he]

noncomputable def rationalThreeBodyLevel (z T : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) : ℚ :=
  ((2 : ℚ)^z * (T.choose z : ℚ) / ((3 : ℚ)^T * (2 : ℚ)^row.1 * (T.choose row.1 : ℚ))) *
    (Certificate.X row.2.2 z T : ℚ) *
    ((Certificate.X row.2.2 z T : ℚ)+2*(row.2.1 : ℚ)*(Certificate.U 2 z T row.1 : ℚ))

theorem threeBodyLevel_certificate (z T : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (hz : z ≤ T) (ht : row.1 ≤ T) :
    (let a := threeBodyInner (fun z T p => couplingPolynomialCoefficient
      (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p) z T row.1 row.2.2;
      2*((row.2.1 : ℝ)/10^7)*couplingPolynomialCoefficient
        (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) row.1*a+a^2) =
      (1/(10^14) : ℝ)*(rationalThreeBodyLevel z T row : ℝ) := by
  dsimp only
  rw [threeBodyInner_certificate z T row.1 hz,
    source_threeBody_radical_coefficient z T row.1 hz ht]
  calc
    _ = (1/(10^14) : ℝ)*(threeBodyRadical z T row.1)^2 * (Certificate.X row.2.2 z T : ℝ) *
        ((Certificate.X row.2.2 z T : ℝ)+2*(row.2.1 : ℝ)*(Certificate.U 2 z T row.1 : ℝ)) := by ring
    _ = _ := by
      rw [threeBodyRadical_sq_choose z T row.1 hz ht]
      unfold rationalThreeBodyLevel
      push_cast
      ring

theorem source_threeBody_trace_certificate_identity (z : ℕ) :
    limitThreeBodyTraceFormula z = (Certificate.e z : ℝ) := by
  unfold limitThreeBodyTraceFormula threeBodyTraceFormula
  have he : Certificate.rows.map (fun row =>
      (((List.range 16).filter (fun T => max z row.1 ≤ T)).map (fun T =>
      let a := threeBodyInner (fun z T p => couplingPolynomialCoefficient
        (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p) z T row.1 row.2.2;
      2*((row.2.1 : ℝ)/10^7)*couplingPolynomialCoefficient
        (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) row.1*a+a^2)).sum) =
      Certificate.rows.map (fun row => (((List.range 16).filter (fun T => max z row.1 ≤ T)).map
        (fun T => (1/(10^14) : ℝ)*(rationalThreeBodyLevel z T row : ℝ))).sum) := by
    apply List.map_congr_left; intro row hrow
    apply congrArg List.sum
    apply List.map_congr_left; intro T hT
    simp only [List.mem_filter,decide_eq_true_eq,max_le_iff] at hT
    exact threeBodyLevel_certificate z T row hT.2.1 hT.2.2
  rw [he]
  simp_rw [real_list_sum_scale]
  unfold Certificate.e rationalThreeBodyLevel
  push_cast
  simp only [List.map_map,Function.comp_def]
  push_cast
  simp only [List.map_map,Function.comp_def]
  push_cast
  ring

 theorem source_physical_threeBody_trace_formula_tendsto (z : ℕ) :
    Filter.Tendsto (fun Q => physicalThreeBodyTraceFormula Q z) Filter.atTop
      (nhds (Certificate.e z : ℝ)) := by
  rw [← source_threeBody_trace_certificate_identity]
  exact physicalThreeBodyTraceFormula_tendsto z

end Laughlin.Spin

end OAI
