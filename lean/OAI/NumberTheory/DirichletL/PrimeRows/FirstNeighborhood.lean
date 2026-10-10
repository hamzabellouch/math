import OAI.NumberTheory.DirichletL.PrimeRows.FirstContinuation
import OAI.NumberTheory.DirichletL.Detector.HighRowsFirstNeighborhood

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

theorem unramifiedFactor_first_neighborhood_defect (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hP : 4≤P.val.absNorm) (x w z : ℂ) (eps : ℝ) (heps : 0<eps)
    (hx : (101/200:ℝ)≤x.re) (hz : (27/80:ℝ)≤z.re)
    (hw : -(3/200:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedFactor η u P x w z-1‖≤firstPrimeDefectBound eps P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using firstPrimeDefectBound_nonneg eps P
  · apply unramifiedClosed_first_neighborhood_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact heps
    · exact hx
    · exact hz
    · exact hw
    · exact hxw

theorem unramifiedProduct_first_neighborhood_analytic_x (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (w z : ℂ)
    (hw : -(3/200:ℝ)≤w.re) (hz : (27/80:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedProduct S η u x w z)
      {x : ℂ | max (101/200:ℝ) (1+eps-w.re)<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply (unramifiedClosed_first_analytic_x _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro x hx
      change max (101/200:ℝ) (1+eps-w.re)<x.re at hx
      have hx' := (lt_of_le_of_lt (le_max_left (101/200:ℝ) (1+eps-w.re)) hx)
      change (1/2:ℝ)<x.re
      linarith
  · intro P x hx
    have hx' := (lt_of_le_of_lt (le_max_left (101/200:ℝ) (1+eps-w.re)) hx)
    have hxw := (lt_of_le_of_lt (le_max_right (101/200:ℝ) (1+eps-w.re)) hx)
    exact unramifiedFactor_first_neighborhood_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx'.le hz hw (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_neighborhood_analytic_w (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x z : ℂ)
    (hx : (101/200:ℝ)≤x.re) (hz : (27/80:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w=>unramifiedProduct S η u x w z)
      {w : ℂ | max (-(3/200:ℝ)) (1+eps-x.re)<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      exact (unramifiedClosed_first_analytic_w _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith) (by linarith)).mono
          (Set.subset_univ _)
  · intro P w hw
    have hw' := (lt_of_le_of_lt (le_max_left (-(3/200:ℝ)) (1+eps-x.re)) hw)
    have hxw := (lt_of_le_of_lt (le_max_right (-(3/200:ℝ)) (1+eps-x.re)) hw)
    exact unramifiedFactor_first_neighborhood_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw'.le (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_neighborhood_analytic_z (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (101/200:ℝ)≤x.re) (hw : -(3/200:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    AnalyticOnNhd ℂ (fun z=>unramifiedProduct S η u x w z) {z : ℂ | (27/80:ℝ)<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ=>if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [ite_eq_right h]
      apply (unramifiedClosed_first_analytic_z _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro z hz
      change (27/80:ℝ)<z.re at hz
      change (1/3:ℝ)<z.re
      linarith
  · intro P z hz
    exact unramifiedFactor_first_neighborhood_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz.le hw hxw
  · exact hS.half

end SevenEighths.ProbeHighRowFamily

end

end OAI
